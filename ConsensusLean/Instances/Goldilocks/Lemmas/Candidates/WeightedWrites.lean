module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Candidates.WeightedWrites
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.Write
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WriteMode

public section

/-! # Weighted locks: the laws of the writes at a write mode

The laws of `Milestones/Spec/Candidates/WeightedWrites`:

* at the parent's mode they are the evidence-release writes: `slowWeightW_k`,
  `newLocksM_parent` (the SA's new locks, moved here from `Lemmas/AC/WriteMode`),
  `updateNewLocksM_parent`, `updateWritesM_parent`, `updateLocksWM_parent`,
  `optimisticLocksWM_parent`; these certify the parent's mode only; width `0` is width `1`
  (`slowWeightW_zero`);
* with the fast arm and width `k` the update's write is evidence-release's
  (`updateLocksWM_of_parent`); the optimistic write is evidence-release's when on
  (`optimisticLocksWM_on`) and the identity when off (`optimisticLocksWM_off`,
  `optimisticLocksWM_eq`);
* the update's weighted writes are its new locks with their weights (`mem_updateWritesM`); the
  update without a result keeps the stored weighted locks (`updateLocksWM_of_none`);
* **forgetting the weights gives the writes at the same mode**: when the stored weighted locks
  forget to the stored locks, so do they after the update (`lock_image_updateLocksWM`, against
  `updateConfirmationM`) and after the optimistic confirmation (`lock_image_optimisticLocksWM`,
  against `optimisticConfirmationM`). -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type}

/-- At the parent's mode, the update's new locks for its result are evidence-release's (moved here
from `Lemmas/AC/WriteMode`, so that the SA's write-mode laws import no weighted lock). -/
theorem newLocksM_parent (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    (getConfirmation sp A Φ s).map (fun C => newLocksM sp (WriteMode.parent sp) A Φ t s C
      (Function.update A.saved s (some C.root)) A.locks) =
      EvidenceRelease.updateNewLocks sp A Φ t s :=
  rfl

end Consensus.Goldilocks.SA

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable {sp : SAParams} {FGP : Type}

/-- At width `k ≥ 1`, the slow weight is evidence-release's. -/
theorem slowWeightW_k : slowWeightW (FGP := FGP) sp sp.k = slowWeight sp := by
  have hk : max sp.k 1 = sp.k := max_eq_left (by have := sp.two_le_k; omega)
  funext Φ C s o
  unfold slowWeightW slowWeight
  rw [hk]

/-- Width `0` is width `1`: the slow lock and its weight read the same window. -/
theorem slowWeightW_zero : slowWeightW (FGP := FGP) sp 0 = slowWeightW sp 1 := by
  rfl

/-- At the parent's mode, the update's new locks are evidence-release's. -/
theorem updateNewLocksM_parent (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    updateNewLocksM sp (WriteMode.parent sp) A Φ t s = updateNewLocks sp A Φ t s :=
  rfl

/-- At the parent's mode, the weighted new locks are evidence-release's. -/
theorem updateWritesM_parent :
    updateWritesM (FGP := FGP) sp (WriteMode.parent sp) = updateWrites sp := by
  funext A Φ C s N
  unfold updateWritesM updateWrites
  rw [show (WriteMode.parent sp).width = sp.k from rfl, slowWeightW_k]

/-- **At the parent's mode, the update's weighted write is evidence-release's.** -/
theorem updateLocksWM_parent :
    updateLocksWM (FGP := FGP) sp (WriteMode.parent sp) = updateLocksW sp := by
  funext W A C Φ t s
  simp only [updateLocksWM, updateLocksW, updateNewLocksM_parent, updateWritesM_parent]
  cases updateNewLocks sp A Φ t s <;> rfl

/-- With the fast arm and width `k`, the update's weighted write is evidence-release's, whatever
the optimistic write. -/
theorem updateLocksWM_of_parent {m : WriteMode} (hf : m.fastArm = true) (hw : m.width = sp.k) :
    updateLocksWM (FGP := FGP) sp m = updateLocksW sp := by
  obtain ⟨_, o, _⟩ := m
  dsimp only at hf hw
  subst hf hw
  exact updateLocksWM_parent

/-- With the optimistic write on, the weighted optimistic write is evidence-release's. -/
theorem optimisticLocksWM_on {m : WriteMode} (h : m.optimistic = true) :
    optimisticLocksWM (FGP := FGP) sp m = optimisticLocksW sp := by
  funext W A Φ t
  unfold optimisticLocksWM
  rw [h]

/-- **At the parent's mode, the weighted optimistic write is evidence-release's.** -/
theorem optimisticLocksWM_parent :
    optimisticLocksWM (FGP := FGP) sp (WriteMode.parent sp) = optimisticLocksW sp :=
  optimisticLocksWM_on rfl

/-- With the optimistic write off, the weighted optimistic write keeps the stored weighted
locks. -/
theorem optimisticLocksWM_off {m : WriteMode} (h : m.optimistic = false) (W : Set WLock)
    (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) : optimisticLocksWM sp m W A Φ t = W := by
  unfold optimisticLocksWM
  rw [h]

theorem optimisticLocksWM_eq (m : WriteMode) (W : Set WLock) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : optimisticLocksWM sp m W A Φ t =
      if m.optimistic then optimisticLocksW sp W A Φ t else W := by
  cases h : m.optimistic
  · rw [optimisticLocksWM_off h]; rfl
  · rw [optimisticLocksWM_on h]; rfl

theorem mem_updateWritesM {m : WriteMode} {A : SAState sp.n} {Φ : Frm sp.n FGP}
    {C : Int → Nat → Nat} {s : Nat} {N : Set (Nat × Bool × Nat)} {w : WLock} :
    w ∈ updateWritesM sp m A Φ C s N ↔ ∃ p ∈ N, w = ⟨⟨p.1, s, p.2.1, p.2.2⟩, p.1,
      if p.2.1 then fastWeight sp A Φ s p.1 else slowWeightW sp m.width Φ C s p.1⟩ :=
  Iff.rfl

theorem updateNewLocksM_eq_none_iff {m : WriteMode} {A : SAState sp.n} {Φ : Frm sp.n FGP}
    {t : Time} {s : Nat} :
    updateNewLocksM sp m A Φ t s = none ↔ getConfirmation sp A Φ s = none := by
  unfold updateNewLocksM
  exact Option.map_eq_none_iff

/-- The update without a result keeps the stored weighted locks. -/
theorem updateLocksWM_of_none {m : WriteMode} {W : Set WLock} {A : SAState sp.n}
    {C : Int → Nat → Nat} {Φ : Frm sp.n FGP} {t : Time} {s : Nat}
    (h : getConfirmation sp A Φ s = none) : updateLocksWM sp m W A C Φ t s = W := by
  unfold updateLocksWM
  rw [updateNewLocksM_eq_none_iff.2 h]

theorem lock_image_updateWritesM (m : WriteMode) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (C : Int → Nat → Nat) (s : Nat) (N : Set (Nat × Bool × Nat)) :
    WLock.lock '' updateWritesM sp m A Φ C s N = {l | ∃ p ∈ N, l = ⟨p.1, s, p.2.1, p.2.2⟩} := by
  ext l
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨_, ⟨p, hp, rfl⟩, rfl⟩

/-- **The update's weighted write forgets to the write at the same mode**: if the stored weighted
locks forget to the stored locks, so do they after the update of slot `s` at mode `m`. -/
theorem lock_image_updateLocksWM (m : WriteMode) {W : Set WLock} {A : SAState sp.n}
    (hW : WLock.lock '' W = A.locks) (C : Int → Nat → Nat) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) :
    WLock.lock '' updateLocksWM sp m W A C Φ t s = (updateConfirmationM sp m A Φ t s).locks := by
  cases hC : getConfirmation sp A Φ s with
  | none => rw [updateLocksWM_of_none hC, updateConfirmationM_locks_of_none hC, hW]
  | some D =>
    have hN : updateNewLocksM sp m A Φ t s =
        some (newLocksM sp m A Φ t s D (Function.update A.saved s (some D.root)) A.locks) := by
      unfold updateNewLocksM
      rw [hC, Option.map_some]
    unfold updateLocksWM
    rw [hN, updateConfirmationM_locks_of_some hC]
    have himg := LockStore.lock_image_addLocksWith (S := wlockStore) wlockStore_lawful W _ Φ t s
      (lock_image_updateWritesM m A Φ (saveCount sp C A Φ s) s
        (newLocksM sp m A Φ t s D (Function.update A.saved s (some D.root)) A.locks))
    rw [hW] at himg
    exact himg

/-- **The weighted optimistic write forgets to the write at the same mode.** -/
theorem lock_image_optimisticLocksWM (m : WriteMode) {W : Set WLock} {A : SAState sp.n}
    (hW : WLock.lock '' W = A.locks) (Φ : Frm sp.n FGP) (t : Time) :
    WLock.lock '' optimisticLocksWM sp m W A Φ t = (optimisticConfirmationM sp m A Φ t).locks := by
  cases h : m.optimistic
  · rw [optimisticLocksWM_off h, optimisticConfirmationM_off h, hW]
  · rw [optimisticLocksWM_on h, optimisticConfirmationM_on h]
    exact lock_image_optimisticLocksW hW Φ t

end Consensus.Goldilocks.EvidenceRelease

end
