module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NetworkTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ForwardingDecode

public section

/-! # Node output of steady-state finality (r14 s6 L6.5 steps 5–10)

`finalized_carrier_cached`: once an honest validator has accepted a carrier block `Z`, every honest
reader that is ready one protocol delay later has the block `X` that `Z`'s state finalizes below its
finalized tip. Premises are the run's own: execution validity, no hash collision, partial
synchrony from `g`, and the fault bound. No post-heal chain structure, proposer gap or timeout
bound is used. The readiness duration `c` is a `Time` (in a contract run, `cDur = catchUp·Δe`),
not the dimensionless catch-up coefficient. Corollaries: any target below `X`
(`finalized_carrier_cached_of_anc`), and every later cut (`finalized_carrier_cached_mono`).

The steps: the acceptance publishes an authenticated forwarding chain (`forwardAtAcceptance`); one
protocol-delay tail makes it held at the reader (`publication_held_ready_tail`); the reader's tip is
compatible with the replay-finalized block (`Store.replay_finalized_safety`), so either it already
covers it or the reader accepts the carrier (`held_forward_accepted_before`); acceptance moves the
reader's cache to the carrier's finality (`Healing.accepted_replay_finalized_cached`), and the
tip only moves to descendants. This is the body of `final_cache_acceptance_of_publication_tail`
with an arbitrary honest carrier in place of the window's last anchor. -/

namespace Consensus.Goldilocks.Refinement

open Shape Blocks
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- **Node output of a finalized carrier.** An honest acceptance of `Z`, whose state finalizes
`X` (`hX`, `hXr` identify the finalized block of `σ[Z]`), puts `X` below the finalized tip of
every honest reader that is ready at `t` for the duration `c`, at a cut after `t`, when `t` is one
protocol delay after both the acceptance and GST. -/
theorem finalized_carrier_cached (hv : rho.ExecutionValid) (hnc : ¬ rho.HashCollision)
    {g c : Time} (hnet : rho.log.PSync rho.point g)
    (hf : (honestKeys S rho)ᶜ.ncard <
      2 * (S.params (pubOf E) hn).toParams.fg.q - (S.params (pubOf E) hn).n)
    {x : Fin (Fintype.card V)} (hx : x ∈ honestKeys S rho) {k : Nat}
    {Z X : SA.Blk (S.params (pubOf E) hn).n (List (FG.Att (S.params (pubOf E) hn).n))}
    (hacc : (simTrace S rho hn).AcceptAt x k Z)
    (hX : X ∈ ((simTrace S rho hn).state x (k + 1)).fg.tree)
    (hXr : X.root = (((simTrace S rho hn).state x (k + 1)).fg.σ Z.root).F)
    {y : Fin (Fintype.card V)} {t : Time} {j : Nat}
    (hy : Regimes.ReadyAt (simTrace S rho hn) (honestKeys S rho) c y t)
    (ht : t ≤ rho.horizon)
    (hbudget : max (max ((simTrace S rho hn).time k) g) 0 + (S.params (pubOf E) hn).Δ ≤ t)
    (hc : (S.params (pubOf E) hn).Δ ≤ c + 1)
    (hj : Regimes.CutAfter (simTrace S rho hn) j t) :
    Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho)) X
      ((simTrace S rho hn).state y j).fg.F := by
  have run := simTrace_goldilocksRun S rho hn hv
  have hncR := noCollTransport V S E rho hn hv hnc
  have hreq : (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).Requirements := by
    have h := SA.interface_requirements (S.params (pubOf E) hn)
      (List (FG.Att (S.params (pubOf E) hn).n)) (S.ro _)
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, SA.proposal_payload_valid _ _ _⟩
  have fg : FGLocalRun (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload
      (honestKeys S rho) ((simTrace S rho hn).HonestBlocks (honestKeys S rho))
      (simTrace S rho hn).projFG :=
    Compose.fg_projection _ _ _ _ _ _ _ hreq run.genesis_root_ok run.toLocalRun hncR
  have hst : ∀ z, z ∈ honestKeys S rho → ∀ i,
      (simTrace S rho hn).projFG.store z i = ((simTrace S rho hn).state z i).fg := by
    intro z hz i
    simp only [FGTrace.store, Compose.projFG_state run.toLocalRun hz i]
  have hreach := Compose.fg_reachable run.toLocalRun hx (k + 1)
  have hZ : Z ∈ ((simTrace S rho hn).state x (k + 1)).fg.tree := by
    have hon := (run.cutLaw _ hx _ _ hacc).2.1
    rw [(simTrace S rho hn).state_succ_of_call hacc]
    rw [(Store.tree_grows _ _ _ _ (Compose.fg_reachable run.toLocalRun hx _)).1 _ _ hon]
    exact Set.mem_insert _ _
  have hXZ : Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho)) X Z := by
    obtain ⟨_, ⟨X', hX', hX'r, hanc⟩, _⟩ :=
      Store.entry_state_of_source _ _ _ _ hreach _ hZ
    have he : X' = X := (Store.accepted_tree _ _ _ _ hreach).2.1.1 hX' hX
      (hX'r.trans hXr.symm)
    subst X'
    exact hanc.mono (by rw [← hst _ hx]; exact fg.tree_subset _ hx _)
  obtain ⟨r, p, hr, horg, _, _, htime, _, hdecode⟩ :=
    (forwardAtAcceptance_iff S rho hn _ _ _).mp (forwardAtAcceptance S rho hn hv) _ hx _ _ hacc
  have hsafe := Store.replay_finalized_safety fg hf hx hy.1
    (by rw [hst _ hx]; exact hZ) (by rw [hst _ hx]; exact hX) (by rw [hst _ hx]; exact hXr)
    (j := j)
  rw [hst _ hy.1] at hsafe
  rcases hsafe with hXF | hFX
  · exact hXF
  obtain ⟨d, hheld, hdt'⟩ := publication_held_ready_tail S rho hn hnet r hr
    (horg ▸ hx) (not_isRow_of_decodeForward hdecode) hy ht (by rw [htime]; exact hbudget) hc
  obtain ⟨k', hkj, hacc', hkt⟩ := held_forward_accepted_before S rho hn hv hncR
    hy.1 hx hheld hdecode hdt' hj.2.le (hFX.trans hXZ)
  have hkj' : k' + 1 ≤ j := by
    have : k' ≠ j := by intro he; subst k'; exact (not_lt_of_ge hj.2.le) hkt
    omega
  have hac : (simTrace S rho hn).projFG.AcceptAt y k' Z := Compose.projFG_callAt.mpr hacc'
  have hpostZ : Z ∈ ((simTrace S rho hn).projFG.store y (k' + 1)).tree := by
    have h := Store.accept_onBlock fg hy.1 hac
    rw [(Store.tree_grows _ _ _ _ (Store.store_reachable fg hy.1 k')).1 _ _ h]
    exact Set.mem_insert _ _
  have hpostXZ := Store.anc_of_U fg hy.1 hXZ hpostZ
  have hpostX : X ∈ ((simTrace S rho hn).projFG.store y (k' + 1)).tree := by
    by_cases he : X = Z
    · exact he ▸ hpostZ
    · exact (Anc.mem hpostXZ he).1
  have hσ := Store.σ_eq_of_held fg hx hy.1 (by rw [hst _ hx]; exact hZ) hpostZ
  have hkFX : Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho))
      ((simTrace S rho hn).projFG.store y k').F X := by
    rw [hst _ hy.1]
    exact ((Compose.fg_grows run hy.1 hkj).2).trans hFX
  have hcache := Healing.accepted_replay_finalized_cached fg hf hy.1 hac hpostX
    (by rw [← hσ, hst _ hx]; exact hXr) hkFX
  rw [hst _ hy.1] at hcache
  exact hcache.trans (Compose.fg_grows run hy.1 hkj').2

/-- Any target below the carrier's finalized block is output, by transitivity. -/
theorem finalized_carrier_cached_of_anc (hv : rho.ExecutionValid) (hnc : ¬ rho.HashCollision)
    {g c : Time} (hnet : rho.log.PSync rho.point g)
    (hf : (honestKeys S rho)ᶜ.ncard <
      2 * (S.params (pubOf E) hn).toParams.fg.q - (S.params (pubOf E) hn).n)
    {x : Fin (Fintype.card V)} (hx : x ∈ honestKeys S rho) {k : Nat}
    {Z X X' : SA.Blk (S.params (pubOf E) hn).n (List (FG.Att (S.params (pubOf E) hn).n))}
    (hacc : (simTrace S rho hn).AcceptAt x k Z)
    (hX : X ∈ ((simTrace S rho hn).state x (k + 1)).fg.tree)
    (hXr : X.root = (((simTrace S rho hn).state x (k + 1)).fg.σ Z.root).F)
    (hX'X : Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho)) X' X)
    {y : Fin (Fintype.card V)} {t : Time} {j : Nat}
    (hy : Regimes.ReadyAt (simTrace S rho hn) (honestKeys S rho) c y t)
    (ht : t ≤ rho.horizon)
    (hbudget : max (max ((simTrace S rho hn).time k) g) 0 + (S.params (pubOf E) hn).Δ ≤ t)
    (hc : (S.params (pubOf E) hn).Δ ≤ c + 1)
    (hj : Regimes.CutAfter (simTrace S rho hn) j t) :
    Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho)) X'
      ((simTrace S rho hn).state y j).fg.F :=
  hX'X.trans (finalized_carrier_cached S rho hn hv hnc hnet hf hx hacc hX hXr hy ht hbudget hc hj)

/-- The output persists: an honest node's finalized tip only moves to descendants. -/
theorem finalized_carrier_cached_mono (hv : rho.ExecutionValid) (hnc : ¬ rho.HashCollision)
    {g c : Time} (hnet : rho.log.PSync rho.point g)
    (hf : (honestKeys S rho)ᶜ.ncard <
      2 * (S.params (pubOf E) hn).toParams.fg.q - (S.params (pubOf E) hn).n)
    {x : Fin (Fintype.card V)} (hx : x ∈ honestKeys S rho) {k : Nat}
    {Z X : SA.Blk (S.params (pubOf E) hn).n (List (FG.Att (S.params (pubOf E) hn).n))}
    (hacc : (simTrace S rho hn).AcceptAt x k Z)
    (hX : X ∈ ((simTrace S rho hn).state x (k + 1)).fg.tree)
    (hXr : X.root = (((simTrace S rho hn).state x (k + 1)).fg.σ Z.root).F)
    {y : Fin (Fintype.card V)} {t : Time} {j j' : Nat}
    (hy : Regimes.ReadyAt (simTrace S rho hn) (honestKeys S rho) c y t)
    (ht : t ≤ rho.horizon)
    (hbudget : max (max ((simTrace S rho hn).time k) g) 0 + (S.params (pubOf E) hn).Δ ≤ t)
    (hc : (S.params (pubOf E) hn).Δ ≤ c + 1)
    (hj : Regimes.CutAfter (simTrace S rho hn) j t) (hjj : j ≤ j') :
    Anc ((simTrace S rho hn).HonestBlocks (honestKeys S rho)) X
      ((simTrace S rho hn).state y j').fg.F :=
  (finalized_carrier_cached S rho hn hv hnc hnet hf hx hacc hX hXr hy ht hbudget hc hj).trans
    (Compose.fg_grows (simTrace_goldilocksRun S rho hn hv) hy.1 hjj).2

end Consensus.Goldilocks.Refinement

end
