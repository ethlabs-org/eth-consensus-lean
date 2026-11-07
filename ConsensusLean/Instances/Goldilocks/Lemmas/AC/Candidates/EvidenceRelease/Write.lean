module
public import ConsensusLean.Instances.Goldilocks.Spec.WeightedLocks.Writes
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.Rule
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.HandlerFields

public section

/-! # Candidate `evidence-release`: the weighted write

The writes are defined in `Spec/WeightedLocks/Writes`; this module proves what they do. The
candidate writes the parent's locks, each with a weight fixed at its write: for each block
`Y` at or below the block it was written on, the number of validators that the confirmation
writing it counted for `Y` (`0` elsewhere, `weightBelow`):

* a fast lock of the update of slot `s` weighs the update's own count, `confirmationScore`
  (`fastWeight`);
* a slow lock of the update of slot `s` weighs the **maximum over its `k` formation slots**
  `s − k + 1, …, s` of the counts saved with those slots' confirmations (`slowWeight`). The
  counts are saved per slot (`saveCount`: the update of slot `s` saves its count before it
  writes); a slot with no saved count counts `0`;
* a lock of the optimistic confirmation of slot `s` weighs the optimistic test's count,
  `optimisticVoters` (`optimisticWeight`).

The origin of every new lock is the root of the block it is written on.

`updateNewLocks` names the new locks of the parent's update (its `N`);
`updateConfirmation_locks_of_none`, `updateConfirmation_locks_of_some` state the parent's locks
after the update with it. The candidate's writes (`updateLocksW`, `optimisticLocksW`) are
`addLocksWith` of the weighted new locks, and **forget to the parent's**:
`lock_image_updateLocksW`, `lock_image_optimisticLocksW`. So the forgotten lock store follows
the parent at every write, and departs from it only at an unlock (`Rule`).

The weight facts the keep sites read: on the chain of the written block the weight is the
writer's count (`weightBelow_of_anc`), the counts are antitone along the chain
(`confirmationScore_antitone`, `optimisticVoters_antitone`), and a slow lock weighs at least
each count saved in its formation window (`le_slowWeight`), in particular its own slot's. -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable {sp : SAParams} {FGP : Type}

/-- On the chain of the written block, the weight is the writer's count. -/
theorem weightBelow_of_anc {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {o : Nat}
    (f : Blk sp.n FGP → Nat) {Y : Blk sp.n FGP} (hY : Y ∈ Φ.tree) (hYo : AncR Φ Y o) :
    weightBelow sp Φ o f Y.root = f Y := by
  have hl : lookup Φ Y.root = some Y := by
    cases h : lookup Φ Y.root with
    | none => exact absurd ⟨Y, hY, rfl⟩ (lookup_eq_none h)
    | some Y' =>
      obtain ⟨hY', hr⟩ := lookup_eq_some h
      exact congrArg some (hΦ.coherent.1 hY' hY hr)
  simp only [weightBelow, hl, hYo, ↓reduceIte]

/-- Off the chain of the written block, the weight is `0`. -/
theorem weightBelow_of_not_anc {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {o : Nat}
    (f : Blk sp.n FGP → Nat) {Y : Blk sp.n FGP} (hY : Y ∈ Φ.tree) (hYo : ¬ AncR Φ Y o) :
    weightBelow sp Φ o f Y.root = 0 := by
  have hl : lookup Φ Y.root = some Y := by
    cases h : lookup Φ Y.root with
    | none => exact absurd ⟨Y, hY, rfl⟩ (lookup_eq_none h)
    | some Y' =>
      obtain ⟨hY', hr⟩ := lookup_eq_some h
      exact congrArg some (hΦ.coherent.1 hY' hY hr)
  simp only [weightBelow, hl, hYo, ↓reduceIte]

/-- A slow lock weighs at least each count saved in its formation window: the slots `s − j` for
`j < k`. -/
theorem le_slowWeight {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (C : Int → Nat → Nat) {s o : Nat}
    {Y : Blk sp.n FGP} (hY : Y ∈ Φ.tree) (hYo : AncR Φ Y o) {j : Nat} (hj : j < sp.k) :
    C ((s : Int) - j) Y.root ≤ slowWeight sp Φ C s o Y.root := by
  rw [slowWeight, weightBelow_of_anc hΦ _ hY hYo]
  exact Finset.le_sup (f := fun j : Nat => C ((s : Int) - j) Y.root) (Finset.mem_range.2 hj)

/-- After the update of slot `s` saves its count, a slow lock of slot `s` weighs at least that
update's own count. -/
theorem confirmationScore_le_slowWeight {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (C : Int → Nat → Nat) (A : SAState sp.n) {s o : Nat} {Y : Blk sp.n FGP} (hY : Y ∈ Φ.tree)
    (hYo : AncR Φ Y o) (hk : 1 ≤ sp.k) :
    confirmationScore sp A Φ s Y ≤ slowWeight sp Φ (saveCount sp C A Φ s) s o Y.root := by
  have h := le_slowWeight hΦ (saveCount sp C A Φ s) hY hYo (s := s) (j := 0) (by omega)
  rw [Nat.cast_zero, sub_zero] at h
  have hl : lookup Φ Y.root = some Y := by
    cases h : lookup Φ Y.root with
    | none => exact absurd ⟨Y, hY, rfl⟩ (lookup_eq_none h)
    | some Y' =>
      obtain ⟨hY', hr⟩ := lookup_eq_some h
      exact congrArg some (hΦ.coherent.1 hY' hY hr)
  rwa [saveCount, Function.update_self, updateCount, hl, Option.map_some,
    Option.getD_some] at h

/-- The update's count is antitone along a chain: a supporter of `Y'` supports `Y ⪯ Y'`. -/
theorem confirmationScore_antitone (A : SAState sp.n) {Φ : Frm sp.n FGP} (s : Nat)
    {Y Y' : Blk sp.n FGP} (hYY' : Φ.Anc Y Y') :
    confirmationScore sp A Φ s Y' ≤ confirmationScore sp A Φ s Y := by
  unfold confirmationScore
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro i ⟨hi, x, hx, hxi, hxs, R, hR, hRr, hY'R⟩
  exact ⟨hi, x, hx, hxi, hxs, R, hR, hRr, hYY'.trans hY'R⟩

/-- The optimistic test's voters are antitone along a chain. -/
theorem optimisticVoters_antitone (A : SAState sp.n) {Φ : Frm sp.n FGP} (s : Nat)
    {Y Y' : Blk sp.n FGP} (hYY' : Φ.Anc Y Y') :
    optimisticVoters sp A Φ s Y' ⊆ optimisticVoters sp A Φ s Y := by
  rintro i ⟨x, hx, hxi, R, hR, hRr, hY'R⟩
  exact ⟨x, hx, hxi, R, hR, hRr, hYY'.trans hY'R⟩

/-! ### The writes of the update and of the optimistic confirmation -/

/-- The parent's update with no result keeps the locks. -/
theorem updateConfirmation_locks_of_none {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {s : Nat} (h : updateNewLocks sp A Φ t s = none) :
    (updateConfirmation sp A Φ t s).locks = A.locks := by
  unfold updateNewLocks at h
  unfold updateConfirmation
  rw [Option.map_eq_none_iff] at h
  simp only [h]

/-- The parent's update with a result writes its new locks with `add_locks`. -/
theorem updateConfirmation_locks_of_some {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {s : Nat} {N : Set (Nat × Bool × Nat)} (h : updateNewLocks sp A Φ t s = some N) :
    (updateConfirmation sp A Φ t s).locks = addLocks sp A.locks Φ t s N := by
  unfold updateNewLocks at h
  obtain ⟨C, hC, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold updateConfirmation
  simp only [hC, Option.map_some]
  split_ifs <;> simp only [updateLatestConfirmed_keeps_locks]

theorem mem_updateWrites {A : SAState sp.n} {Φ : Frm sp.n FGP} {C : Int → Nat → Nat} {s : Nat}
    {N : Set (Nat × Bool × Nat)} {w : WLock} :
    w ∈ updateWrites sp A Φ C s N ↔ ∃ p ∈ N, w = ⟨⟨p.1, s, p.2.1, p.2.2⟩, p.1,
      if p.2.1 then fastWeight sp A Φ s p.1 else slowWeight sp Φ C s p.1⟩ :=
  Iff.rfl

theorem lock_image_updateWrites (A : SAState sp.n) (Φ : Frm sp.n FGP) (C : Int → Nat → Nat)
    (s : Nat) (N : Set (Nat × Bool × Nat)) :
    WLock.lock '' updateWrites sp A Φ C s N = {l | ∃ p ∈ N, l = ⟨p.1, s, p.2.1, p.2.2⟩} := by
  ext l
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨_, ⟨p, hp, rfl⟩, rfl⟩

/-- **The update write forgets to the parent's**: if the stored weighted locks forget to the
parent's locks, so do they after the update. -/
theorem lock_image_updateLocksW {W : Set WLock} {A : SAState sp.n} (hW : WLock.lock '' W = A.locks)
    (C : Int → Nat → Nat) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    WLock.lock '' updateLocksW sp W A C Φ t s = (updateConfirmation sp A Φ t s).locks := by
  unfold updateLocksW
  cases h : updateNewLocks sp A Φ t s with
  | none => rw [updateConfirmation_locks_of_none h, hW]
  | some N =>
    have himg := LockStore.lock_image_addLocksWith (S := wlockStore) wlockStore_lawful W _ Φ t s
      (lock_image_updateWrites A Φ (saveCount sp C A Φ s) s N)
    rw [hW] at himg
    rw [updateConfirmation_locks_of_some h]
    exact himg

theorem optimisticWrite_lock (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) :
    (optimisticWrite sp A Φ t B).lock =
      ⟨B.root, sp.slot t, true, fastExpiry sp A.locks Φ t (sp.slot t)⟩ := by
  rfl

theorem optimisticWrite_weight (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) :
    (optimisticWrite sp A Φ t B).weight = optimisticWeight sp A Φ (sp.slot t) B.root := by
  rfl

/-- **The optimistic write forgets to the parent's.** -/
theorem lock_image_optimisticLocksW {W : Set WLock} {A : SAState sp.n}
    (hW : WLock.lock '' W = A.locks) (Φ : Frm sp.n FGP) (t : Time) :
    WLock.lock '' optimisticLocksW sp W A Φ t = (optimisticConfirmation sp A Φ t).locks := by
  unfold optimisticLocksW optimisticConfirmation
  cases h : optimisticSelect sp A Φ t with
  | none => exact hW
  | some B =>
    have hN : wlockStore.lock '' {optimisticWrite sp A Φ t B} =
        {l | ∃ p ∈ ({(B.root, true, fastExpiry sp A.locks Φ t (sp.slot t))} :
          Set (Nat × Bool × Nat)), l = ⟨p.1, sp.slot t, p.2.1, p.2.2⟩} := by
      ext l
      simp only [Set.image_singleton, Set.mem_singleton_iff, Set.mem_ofPred_eq, exists_eq_left]
      rw [optimisticWrite_lock]
    have himg := LockStore.lock_image_addLocksWith (S := wlockStore) wlockStore_lawful W _ Φ t
      (sp.slot t) hN
    rw [hW] at himg
    dsimp only
    rw [updateLatestConfirmed_keeps_locks]
    exact himg

/-- An optimistic lock weighs, at each block at or below its block, at least the optimistic
test's count at its block. -/
theorem optimisticWrite_weight_ge {A : SAState sp.n} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (t : Time) {B Y : Blk sp.n FGP} (hB : B ∈ Φ.tree) (hY : Y ∈ Φ.tree) (hYB : Φ.Anc Y B) :
    (optimisticVoters sp A Φ (sp.slot t) B).ncard ≤
      (optimisticWrite sp A Φ t B).weight Y.root := by
  rw [optimisticWrite_weight, optimisticWeight, weightBelow_of_anc hΦ _ hY ⟨B, hB, rfl, hYB⟩]
  exact Set.ncard_le_ncard (optimisticVoters_antitone A _ hYB) (Set.toFinite _)

end Consensus.Goldilocks.EvidenceRelease

end
