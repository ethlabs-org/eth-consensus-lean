module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Bounded clean-source comparisons and vote retention -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload Vote)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n} {g ΔF a b : Time}

/-- An optimistic source has an actual honest supporting vote no later than its write. -/
theorem ResetPremisesUpTo.optimistic_supporter
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {x : Fin sp.n} (hx : x ∈ H) {r s : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hs1 : sp.slot (AC.gbar g) + 1 ≤ s) (hop : AC.OptimisticLockAt tr.projAC x r s B CV) :
    B ∈ (tr.state x r).fg.tree ∧ ∃ z ∈ H, ∃ q ≤ r, ∃ e,
      AC.VoteAt tr.projAC z q e ∧ e.msg.slot = s ∧
      AC.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hrun := Compose.goldilocks_ac_projection_from hp.run hp.noColl
  obtain ⟨ell, A, hpt, hsl, hsel, _⟩ := hop
  have hU := (AC.frameIn_of_callAt hrun.localRun hx hpt.1).2
  unfold AC.optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  refine ⟨hp.frame_tree_subset hx hpt.1 (AC.deepest_mem hsel).1.1, ?_⟩
  have h34 := (AC.deepest_mem hsel).1.2.1
  rw [hsl] at h34
  have hK : AC.optimisticVoters sp A ell.frame s B ⊆ K.committee s := by
    rintro _ ⟨v, hv, rfl, -⟩; exact hp.hP.2 x hx r ell A hpt s v (hsl ▸ hv)
  have hf := hp.cs2 hs1
  obtain ⟨z, ⟨v, hv, rfl, R, hR, hRr, hBR⟩, hz⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (s := K.committee s ∩ Hᶜ)
      (t := AC.optimisticVoters sp A ell.frame s B) (by omega)
  have hvH : v.val ∈ H := by
    by_contra hn
    exact hz ⟨hK ⟨v, hv, rfl, R, hR, hRr, hBR⟩, hn⟩
  obtain ⟨hvs, q, hqr, e, he, rfl⟩ :=
    AC.optimisticPoint_pool_voteU hrun.toU hx hpt (hsl ▸ hv) hvH
  exact ⟨_, hvH, q, hqr, e, he, hvs.trans hsl, R, hU hR, hRr, hBR.mono hU⟩

end Consensus.Goldilocks.Healing

end
