module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Family
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Family.Identity
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.ACProjection

/-! # The actual-node Goldilocks identity family run -/

public section

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload goldilocksFamily)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {R : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

theorem goldilocksFamilyRun (hr : GoldilocksRun proposer dg H R) (hnc : NoCollRun dg R) :
    FamilyRun (goldilocksFamily sp (List (FG.Att sp.n)) ro) proposer dg H R := by
  refine ⟨hr.toLocalRun, hr.genesis_root_ok, ?_,
    SA.goldilocksObservationAgreement H R.projAC,
    SA.goldilocksObservation (goldilocks_ac_projection sp ro dg H R proposer hr hnc).localRun⟩
  intro y hy i B hc v hv hh
  obtain ⟨j, hj, he⟩ := hr.carried_vote_unforgeable y hy i B hc v hv hh
  change ∃ j < i, ∃ e, SA.VoteAt
    ((goldilocksFamily sp (List (FG.Att sp.n)) ro).proj R.projAC) v.val j e ∧ e.msg = v
  rw [SA.proj_goldilocks]
  obtain ⟨ℓ, hc, e, he, rfl⟩ := he
  exact ⟨j, hj, e, ⟨ℓ, projAC_callAt.mpr hc, he⟩, rfl⟩

end Consensus.Goldilocks.Compose

end
