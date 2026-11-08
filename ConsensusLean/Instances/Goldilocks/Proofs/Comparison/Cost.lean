module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.Cost
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.CarriedVotes
import ConsensusLean.Instances.Goldilocks.Lemmas.Candidates.LockCountParent
import ConsensusLean.Instances.Goldilocks.Lemmas.Candidates.LockCountER
import ConsensusLean.Instances.Goldilocks.Lemmas.Candidates.Memory

public section

/-! # Goldilocks cost at Tier A (proofs)

* `carriedBoundAC0`: an honest proposal carries at most `|H| + 2·|Hᶜ|` distinct votes, at every
  write mode and unlock oracle (`carried_votes_le`);
* `lockMemoryAC0`, `lockMemoryERAC0`, `lockMemoryCertAC0`: the parent's stage, evidence-release and
  the late-certificate rule at every write mode without the optimistic write
  (`parent_lockMemory`, `er_lockMemory`, `cert_lockMemory`). -/

namespace Consensus.Goldilocks.Comparison

open SA

theorem carriedBoundAC0 : CarriedBoundAC0 :=
  fun _ _ _ _ _ _ _ _ _ h hobj _ hy _ _ _ _ _ _ hp => carried_votes_le h hobj hy hp

theorem lockMemoryAC0 : LockMemoryAC0 := by
  intro sp m FGP ro H U tr hopt h hone y hy i
  obtain ⟨h1, h2, h3⟩ := parent_lockMemory hopt h hone hy i
  refine ⟨?_, h2, ?_⟩
  · rw [lockMemory_eq, lockBound]
    exact h1
  · rw [savedMemory_eq]
    exact h3 m.width

theorem lockMemoryERAC0 : LockMemoryERAC0 := by
  intro sp m FGP ro H U tr hopt h hone y hy i
  obtain ⟨h1, h2, h3⟩ := EvidenceRelease.er_lockMemory hopt h hone hy i
  refine ⟨?_, h2, ?_⟩
  · rw [EvidenceRelease.lockMemoryW_eq, lockBound]
    exact h1
  · rw [EvidenceRelease.countMemory_eq]
    exact h3 m.width

theorem lockMemoryCertAC0 : LockMemoryCertAC0 := by
  intro sp m FGP ro H U tr hopt h hone y hy i
  obtain ⟨h1, h2, h3⟩ := LateCertificate.cert_lockMemory hopt h hone hy i
  refine ⟨?_, h2, ?_⟩
  · rw [EvidenceRelease.lockMemoryW_eq, lockBound]
    exact h1
  · rw [EvidenceRelease.countMemory_eq]
    exact h3 m.width

end Consensus.Goldilocks.Comparison

end
