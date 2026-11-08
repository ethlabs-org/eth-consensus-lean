module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Candidates.Memory
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.Projection
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Candidates.WeightedWrites

public section

/-! # Lock memory and working rows: the measures' sanity theorems

The measures of `Milestones/Spec/Candidates/Memory` read the family's own state:

* `lockMemory_eq`, `lockMemoryW_eq`, `savedMemory_eq`, `countMemory_eq`: each is the `encard` of
  the stored objects it names;
* `liveLocks_encard_le_lockMemory`: the protocol's `live_locks(locks, Φ, t)` has at most
  `lockMemory` locks, at every well-formed frame (roots injective on the tree);
* `lockMemory_le_lockMemoryW`: evidence-release's parent locks (the forgotten image of its
  weighted locks) are at most its weighted lock memory;
* `liveLocks_heldLocks`, `liveLockBlocks_heldLocks`, `conflictsWithLock_heldLocks`,
  `fastExpiry_heldLocks`, `unlock_heldLocks`: the live locks, their blocks (which the anchor and
  `ac_to_fg` read), the conflict test, the fast expiry and the unlock read only the unexpired
  stored locks (an expired lock stays in `A.locks` until the next write), so the expired ones
  are not counted;
* the working rows (`workingRows`, `workingCountRows`, at formation width `w`):
  `newLocksM_congr_saved` (the update of slot `s` reads the saved results of `s − w < j < s`
  only) and `slowWeightW_congr` (the slow weight of slot `s` reads the saved counts of
  `s − max w 1 < j ≤ s` only). The update of slot `s` runs at `t_{s+1} + 2Δ`, so these rows are
  `j ≥ slot(t) − max w 1` at its time `t`, the working window. -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type}

theorem lockMemory_eq {n : Nat} (A : SAState n) (t : Time) :
    lockMemory sp A t = {l | l ∈ A.locks ∧ l.LiveAt sp t}.encard := by
  rfl

theorem savedMemory_eq {n : Nat} (w : Nat) (A : SAState n) (t : Time) :
    savedMemory sp w A t =
      {j : Int | (sp.slot t : Int) - (max w 1 : Nat) ≤ j ∧ A.saved j ≠ none}.encard := by
  rfl

/-- **Sanity: the protocol's live locks are among the lock memory.** At a frame whose roots are
injective on its tree, `live_locks(locks, Φ, t)` has at most `lockMemory` locks: each live lock is
an unexpired stored lock moved to the viable ancestor of its block, which its root determines. -/
theorem liveLocks_encard_le_lockMemory {Φ : Frm sp.n FGP} (hΦ : Set.InjOn Block.root Φ.tree)
    (A : SAState sp.n) (t : Time) : (liveLocks sp A.locks Φ t).encard ≤ lockMemory sp A t := by
  classical
  have hw : ∀ l' ∈ liveLocks sp A.locks Φ t, ∃ l ∈ A.locks, ∃ B ∈ Φ.tree, B.root = l.block ∧
      l.LiveAt sp t ∧ l' = { l with block := (Φ.viableAncestor B).root } := fun _ h => h
  let g : Lock → Lock := fun l' =>
    if h : l' ∈ liveLocks sp A.locks Φ t then Classical.choose (hw l' h) else l'
  have hg : ∀ l' (h : l' ∈ liveLocks sp A.locks Φ t), g l' = Classical.choose (hw l' h) :=
    fun l' h => dite_eq_left h
  rw [lockMemory_eq]
  refine Set.encard_le_encard_of_injOn (f := g) ?_ ?_
  · intro l' h
    obtain ⟨hl, B, hB, -, hlive, -⟩ := Classical.choose_spec (hw l' h)
    rw [hg l' h]
    exact ⟨hl, hlive⟩
  · intro l₁ h₁ l₂ h₂ he
    obtain ⟨-, B₁, hB₁, hr₁, -, e₁⟩ := Classical.choose_spec (hw l₁ h₁)
    obtain ⟨-, B₂, hB₂, hr₂, -, e₂⟩ := Classical.choose_spec (hw l₂ h₂)
    rw [hg l₁ h₁, hg l₂ h₂] at he
    rw [he] at hr₁ e₁
    obtain rfl : B₁ = B₂ := hΦ hB₁ hB₂ (hr₁.trans hr₂.symm)
    exact e₁.trans e₂.symm

/-- **Sanity: the live locks read only the unexpired stored locks.** -/
theorem liveLocks_heldLocks (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time) :
    liveLocks sp (heldLocks sp L t) Φ t = liveLocks sp L Φ t := by
  ext l'
  constructor
  · rintro ⟨l, ⟨hl, -⟩, h⟩
    exact ⟨l, hl, h⟩
  · rintro ⟨l, hl, B, hB, hr, hlive, rfl⟩
    exact ⟨l, ⟨hl, hlive⟩, B, hB, hr, hlive, rfl⟩

theorem liveLockBlocks_heldLocks (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time) :
    liveLockBlocks sp (heldLocks sp L t) Φ t = liveLockBlocks sp L Φ t := by
  unfold liveLockBlocks
  rw [liveLocks_heldLocks]

/-- The conflict test reads the unexpired stored locks only. -/
theorem conflictsWithLock_heldLocks (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time)
    (C : Blk sp.n FGP) :
    conflictsWithLock sp (heldLocks sp L t) Φ t C ↔ conflictsWithLock sp L Φ t C := by
  unfold conflictsWithLock
  rw [liveLockBlocks_heldLocks]

/-- The fast expiry reads the unexpired stored locks only. -/
theorem fastExpiry_heldLocks (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    fastExpiry sp (heldLocks sp L t) Φ t s = fastExpiry sp L Φ t s := by
  unfold fastExpiry
  rw [liveLocks_heldLocks]

/-- The unlock reads the unexpired stored locks only. -/
theorem unlock_heldLocks (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time) (s : Int) (V : View sp.n) :
    unlock sp (heldLocks sp L t) Φ t s V = unlock sp L Φ t s V := by
  unfold unlock
  rw [liveLocks_heldLocks]

/-- **Sanity: the update of slot `s` at width `m.width` reads the saved results of
`s − m.width < j < s` only.** -/
theorem newLocksM_congr_saved {m : WriteMode} {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {s : Nat} {C : Blk sp.n FGP} {sv sv' : Int → Option Nat} (L : Set Lock)
    (h : ∀ j : Int, (s : Int) - m.width < j → j < s → sv j = sv' j) :
    newLocksM sp m A Φ t s C sv L = newLocksM sp m A Φ t s C sv' L := by
  have hset : {B : Blk sp.n FGP | (B ∈ confirmationPath sp Φ C ∧
      ¬ conflictsWithLock sp A.locks Φ t B) ∧ ∀ j : Int, (s : Int) - m.width < j → j < s →
      ∃ S ∈ Φ.tree, sv j = some S.root ∧ Φ.Anc B S} =
      {B | (B ∈ confirmationPath sp Φ C ∧ ¬ conflictsWithLock sp A.locks Φ t B) ∧
      ∀ j : Int, (s : Int) - m.width < j → j < s →
      ∃ S ∈ Φ.tree, sv' j = some S.root ∧ Φ.Anc B S} := by
    ext B
    refine and_congr_right fun _ => forall_congr' fun j => imp_congr_right fun h₁ =>
      imp_congr_right fun h₂ => ?_
    rw [h j h₁ h₂]
  ext p
  rw [mem_newLocksM, mem_newLocksM, hset]

end Consensus.Goldilocks.SA

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable {sp : SAParams}

theorem lockMemoryW_eq {n : Nat} (X : WState n) (t : Time) :
    lockMemoryW sp X t = {w | w ∈ X.wlocks ∧ w.lock.LiveAt sp t}.encard := by
  rfl

theorem countMemory_eq {n : Nat} (w : Nat) (X : WState n) (t : Time) :
    countMemory sp w X t =
      {j : Int | (sp.slot t : Int) - (max w 1 : Nat) ≤ j ∧ ∃ r, X.counts j r ≠ 0}.encard := by
  rfl

/-- **Sanity: evidence-release's parent locks are among its weighted lock memory.** When its
parent's locks are the forgotten image of its weighted locks (`LocksForget`, every reachable
state), the parent's lock memory is at most the weighted lock memory. -/
theorem lockMemory_le_lockMemoryW {n : Nat} {X : WState n} (hX : LocksForget X) (t : Time) :
    lockMemory sp X.ac t ≤ lockMemoryW sp X t := by
  rw [lockMemory_eq, lockMemoryW_eq, (locksForget_iff X).1 hX]
  calc {l | l ∈ WLock.lock '' X.wlocks ∧ l.LiveAt sp t}.encard
      = (WLock.lock '' {w | w ∈ X.wlocks ∧ w.lock.LiveAt sp t}).encard := by
        congr 1
        ext l
        constructor
        · rintro ⟨⟨w, hw, rfl⟩, hl⟩
          exact ⟨w, ⟨hw, hl⟩, rfl⟩
        · rintro ⟨w, ⟨hw, hl⟩, rfl⟩
          exact ⟨⟨w, hw, rfl⟩, hl⟩
    _ ≤ _ := Set.encard_image_le _ _

/-- **Sanity: the slow weight of slot `s` at width `w` reads the saved counts of
`s − max w 1 < j ≤ s` only.** -/
theorem slowWeightW_congr {FGP : Type} {w : Nat} {Φ : Frm sp.n FGP} {C C' : Int → Nat → Nat}
    {s : Nat} (o : Nat) (h : ∀ j : Int, (s : Int) - (max w 1 : Nat) < j → j ≤ s → C j = C' j) :
    slowWeightW sp w Φ C s o = slowWeightW sp w Φ C' s o := by
  unfold slowWeightW
  congr 1
  funext Y
  refine Finset.sup_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  rw [h ((s : Int) - j) (by omega) (by omega)]

end Consensus.Goldilocks.EvidenceRelease

end
