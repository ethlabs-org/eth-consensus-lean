module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Groups

public section

/-! # Wire checks for the growing canonical trace

Wire decoding is independent of signer honesty; the latter is needed separately for
unforgeability. We recover the canonical event at each group and preserve that separation.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
private theorem wireOK_of_delivered (o : (Model.protoOf (compiled (goldilocks S)) E).Object)
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

private theorem group_of_cut (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} {k : Nat} (hnode : (simTrace S rho hn).node k = y)
    (hl : (simTrace S rho hn).label k ≠ none) :
    ∃ j0 t e,
      (simTrace S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho) y j0 t e ∧ j0 ≤ k ∧
      k < j0 + (Node.exec (runProposer S rho hn) (digestOf S rho)
        y ((simTrace S rho hn).state y j0) t e).2.length ∧ WireOK (digestOf S rho) e := by
  obtain ⟨r, i, ev, -, he, h1, h2, -, hn', -, -, -⟩ := simTrace_cut S rho hn hl
  have hy' := hn'.symm.trans hnode
  cases ev with
  | tick v t =>
    change rho.ownKey v = y at hy'
    subst hy'
    by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
    · obtain ⟨hg, hlen⟩ := simTraceAt_tick_public_group S rho hn hv he hp
      rw [simTraceAt_eq] at hg hlen
      exact ⟨_, t, _, hg, h1, by omega, trivial⟩
    · have hlen := cutMap_succ S rho hn i
      rw [eventCuts_tick_other S rho hn i v t he hp, List.length_nil] at hlen
      omega
  | deliver v o t =>
    change rho.ownKey v = y at hy'
    subst hy'
    have hseq := simTraceAt_deliver S rho hn hv he
    rw [simTraceAt_eq] at hseq
    obtain ⟨-, hcov⟩ := deliverSeq_cover hseq
    obtain ⟨j0, e, o', ho, hce, hg, h3, h4⟩ := hcov k h1 h2
    exact ⟨j0, t, e, hg, h3, h4, wireOK_of_delivered S rho hn o ho hce⟩
  | restart v t =>
    change rho.ownKey v = y at hy'
    subst hy'
    obtain ⟨hg, hlen⟩ := simTraceAt_restart S rho hn hv he
    rw [simTraceAt_eq] at hg hlen
    exact ⟨_, t, _, hg, h1, by omega, trivial⟩

/-- Every canonical handler group passes wire checks, independently of later compromise. -/
theorem simTraceAt_wire (hv : rho.ExecutionValid) :
    ∀ y j t e,
      (simTraceAt S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho) y j t e →
      WireOK (digestOf S rho) e := by
  rw [simTraceAt_eq]
  intro y j t e hg
  obtain ⟨hne, hcuts, huniq⟩ := hg
  obtain ⟨hn0, -, -, -, hl0⟩ := hcuts 0 (List.length_pos_of_ne_nil hne)
  rw [Nat.add_zero] at hn0 hl0
  obtain ⟨j0, t0, e0, ⟨hne0, hc0, -⟩, h1, h2, hw0⟩ :=
    group_of_cut S rho hn hv hn0 (by rw [hl0]; simp)
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

end Consensus.Goldilocks.Simulation
