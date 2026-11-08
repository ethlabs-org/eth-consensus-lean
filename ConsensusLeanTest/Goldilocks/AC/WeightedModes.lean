module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Candidates.EvidenceRelease

@[expose] public section

/-! # The evidence-release SA at a write mode: sanity checks

(a) `weightedModes_parent`: at the parent's mode the evidence-release SA at a mode is
evidence-release's SA, and its weighted writes are evidence-release's.

(b) `slowOnly_update_writes_no_fast_lock`, `slowOnly_off_no_optimistic_lock`: at a slow-only mode
the update writes only slow weighted locks, and with the optimistic write off the optimistic
confirmation writes no weighted lock, so a non-parent mode does change the writes;
`slowOnly_update_eq_parent_slow`: at width `k` the slow-only update writes exactly the parent's
new locks without its fast one.

(c) `slowWeightW_width_zero`: width `0` weighs as width `1`, as `newLocksM` forms its lock. -/

namespace Consensus.Goldilocks.EvidenceRelease.Test.WeightedModes

open SA

variable {sp : SAParams} {FGP : Type}

/-- **At the parent's mode, the SA and its weighted writes are evidence-release's.** -/
theorem weightedModes_parent (ro : ReplayOrder sp FGP) :
    evidenceReleaseSAM sp (WriteMode.parent sp) FGP ro = evidenceReleaseSA sp FGP ro ∧
      updateLocksWM (FGP := FGP) sp (WriteMode.parent sp) = updateLocksW sp ∧
      optimisticLocksWM (FGP := FGP) sp (WriteMode.parent sp) = optimisticLocksW sp :=
  ⟨evidenceReleaseSAM_parent ro, updateLocksWM_parent, optimisticLocksWM_parent⟩

/-- **A slow-only update writes only slow weighted locks**: every weighted lock it adds to the new
locks of its result is not fast. -/
theorem slowOnly_update_writes_no_fast_lock (w : Nat) (opt : Bool) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (s : Nat) {N : Set (Nat × Bool × Nat)}
    (hN : updateNewLocksM sp (WriteMode.slowOnly w opt) A Φ t s = some N) (C : Int → Nat → Nat) :
    ∀ x ∈ updateWritesM sp (WriteMode.slowOnly w opt) A Φ C s N, x.lock.fast = false := by
  obtain ⟨D, -, rfl⟩ := Option.map_eq_some_iff.1 hN
  rintro x ⟨p, hp, rfl⟩
  exact newLocksM_no_fast rfl p hp

/-- **With the optimistic write off, the optimistic confirmation writes no weighted lock.** -/
theorem slowOnly_off_no_optimistic_lock (w : Nat) (W : Set WLock) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    optimisticLocksWM sp (WriteMode.slowOnly w false) W A Φ t = W :=
  optimisticLocksWM_off rfl W A Φ t

/-- **At width `k`, a slow-only update writes exactly the parent's new locks without the fast
one**: it keeps the parent's slow lock and differs from the parent only in the fast arm. -/
theorem slowOnly_update_eq_parent_slow (opt : Bool) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (s : Nat) :
    updateNewLocksM sp (WriteMode.slowOnly sp.k opt) A Φ t s =
      (updateNewLocks sp A Φ t s).map fun N => {p | p ∈ N ∧ p.2.1 = false} := by
  rw [← updateNewLocksM_parent, updateNewLocksM, updateNewLocksM, Option.map_map]
  congr 1
  funext C
  ext p
  simp only [Function.comp_apply, Set.mem_ofPred_eq, mem_newLocksM]
  simp only [WriteMode.slowOnly, WriteMode.parent]
  constructor
  · rintro (⟨h, -⟩ | h)
    · exact absurd h Bool.false_ne_true
    · obtain ⟨B, hB, rfl⟩ := h
      exact ⟨Or.inr ⟨B, hB, rfl⟩, rfl⟩
  · rintro ⟨(⟨-, B, -, rfl⟩ | h), hp⟩
    · exact absurd hp Bool.noConfusion
    · exact Or.inr h

/-- **Width `0` weighs as width `1`.** -/
theorem slowWeightW_width_zero :
    slowWeightW (FGP := FGP) sp (WriteMode.slowOnly 0 false).width =
      slowWeightW sp (WriteMode.slowOnly 1 false).width :=
  slowWeightW_zero

end Consensus.Goldilocks.EvidenceRelease.Test.WeightedModes

end
