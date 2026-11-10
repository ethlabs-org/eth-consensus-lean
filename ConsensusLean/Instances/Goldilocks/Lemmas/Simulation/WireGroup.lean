module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Relay

public section

/-! # Goldilocks Simulation: the wire checks of a group

The wire checks of the simulating trace, independent of which nodes are honest:

* `wireOK_of_delivered`: a canonical event of an object an engine delivery delivers passes the
  wire checks;
* `wireOK_of_group_cut`: a group whose first cut lies in a group with a checked event is that
  group (the first cut of a handler names its event), so its event passes the wire checks.

The cut-to-group step is its users' (`Run` for constant faults, `Growing/Simulation/Wire` for a
signer honest at its cut). -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)

section Delivered

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- A canonical event of an object an engine delivery delivers passes the wire checks: a block
decodes with the engine's digests of the delivery, which map its header to the engine's hash of
it, the root `digestOf` names. -/
theorem wireOK_of_delivered (o : (Model.protoOf (compiled (goldilocks S)) E).Object)
    {o' : Wire (S.params (pubOf E) hn).n} (ho : o' ∈ delivered (S.params (pubOf E) hn) o)
    {e : Event (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    (he : canonEvent (S.params (pubOf E) hn) (S.ro _) (Model.digests rho.hash o) o' = some e) :
    WireOK (digestOf S rho) e := by
  rcases canonEvent_eq_some he with ⟨B, rfl, rfl⟩ | ⟨m, rfl, -⟩ | ⟨a, rfl, -⟩
  · obtain ⟨hroot, hpar, hwf, hval⟩ := decodeBlock_wire (decodeBlock_of_canonEvent he)
    have hh : rootOf (Model.digests rho.hash o) (headerOf _ B) =
        some (rho.hash (headerOf _ B)) := by
      apply rootOf_digests_of_mem
      exact List.mem_filterMap.2 ⟨blockObj _ B, mem_delivered ho, rfl⟩
    rw [hh, Option.map_some, Option.some.injEq] at hroot
    have hrt := hroot.symm
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hpar
    refine ⟨?_, hwf, hval⟩
    rw [digestOf_eq]
    change B.root = dgOf rho.hash S.genesisRoot B.parent B.slot B.input B.fgPayload B.acPayload
    erw [dgOf_eq, hrt]
    simp only [headerOf, hr]
  · trivial
  · exact wellFormed_of_canonEvent he

end Delivered

section Group

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}

/-- **A group whose first cut lies in a checked group passes the wire checks**: let `y`'s group at
`j` have event `e`, and let its first cut (labelled, of `y`) lie in `y`'s group at `j0` whose
event passes the wire checks. The first cut of a group is a cut of the earlier group only when
the two start together, and the first cut of a handler names its event (a block's or an
attestation's FG call; other events need no checks), so `e` passes them. -/
theorem wireOK_of_group_cut {y : Fin sp.n} {j : Nat} {t : Time} {e : Event (goldilocksNode sp ro)}
    (hg : tr.GroupAt proposer dg y j t e)
    (hcut : tr.node j = y → tr.label j ≠ none → ∃ j0 t0 e0,
      tr.GroupAt proposer dg y j0 t0 e0 ∧ j0 ≤ j ∧
        j < j0 + (Node.exec proposer dg y (tr.state y j0) t0 e0).2.length ∧ WireOK dg e0) :
    WireOK dg e := by
  obtain ⟨hne, hcuts, huniq⟩ := hg
  obtain ⟨hn0, -, -, -, hl0⟩ := hcuts 0 (List.length_pos_of_ne_nil hne)
  rw [Nat.add_zero] at hn0 hl0
  obtain ⟨j0, t0, e0, ⟨hne0, hc0, -⟩, h1, h2, hw0⟩ := hcut hn0 (by rw [hl0]; simp)
  have hj : j0 = j := by
    have hev := (hc0 (j - j0) (by omega)).2.2.1
    rw [Nat.add_sub_cancel' h1] at hev
    have := (huniq j0 hev.symm).1
    omega
  subst hj
  have hl1 := (hc0 0 (List.length_pos_of_ne_nil hne0)).2.2.2.2
  rw [Nat.add_zero, hl0, Option.some.injEq] at hl1
  obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨c0, cs0, hcs0⟩ := List.exists_cons_of_ne_nil hne0
  have hc : c = c0 := by
    rw [List.getElem_of_eq hcs, List.getElem_of_eq hcs0] at hl1
    exact hl1
  subst hc
  cases e with
  | tick _ => trivial
  | restart => trivial
  | message _ => trivial
  | block B =>
    obtain ⟨acc, rfl⟩ := exec_block_head _ _ _ _ _ B hcs
    rcases exec_head_fg _ _ _ _ _ e0 hcs0 with ⟨B', acc', rfl, h⟩ | ⟨a, -, h⟩
    · cases h; exact hw0
    · cases h
  | attestation a =>
    have : c = .fg (.attestation a) := by
      have := hcs.symm
      simp only [Node.exec, onAttestation, List.cons.injEq] at this
      exact this.1
    subst this
    rcases exec_head_fg _ _ _ _ _ e0 hcs0 with ⟨B', acc', -, h⟩ | ⟨a', rfl, h⟩
    · cases h
    · cases h; exact hw0

end Group

end Consensus.Goldilocks.Simulation

end
