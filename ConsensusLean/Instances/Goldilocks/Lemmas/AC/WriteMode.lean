module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.HandlerFields
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.WriteModes.Writes
public import ConsensusLean.Instances.Goldilocks.Spec.WeightedLocks.Writes

public section

/-! # SA handlers at a write mode

The SA's handlers with the locks after the unlock given (`Lemmas/AC/RelTrace`) and the writes of
a write mode `m` (`Milestones/Spec/WriteModes/Writes`): `tryVoteWithM`, `acOnTickWithM`,
`acOnMessageWithM`, `acOnBlockWithM`, the call `stepWithM`, and the unlock input `callInputM` and
view `callViewM` of a call. The proposal writes nothing and is `acProposalWith`; `ac_to_fg` and
the restart are the parent's (the restart's replay runs while the node is not joined, so its
optimistic confirmations select nothing at any mode).

The laws:

* **the parent's mode**: at `WriteMode.parent sp` each handler is the parent's
  (`updateConfirmationM_parent`, `optimisticConfirmationM_parent`, `stepWithM_parent`,
  `callInputM_parent`, `callViewM_parent`), and the new locks are the parent's
  (`newLocksM_parent`); more generally `updateConfirmationM_of_parent` at every mode with the
  fast arm and width `k`, and `optimisticConfirmationM_on` at every mode with the optimistic
  write;
* **the update at any mode** changes only the parent's fields and its locks
  (`updateConfirmationM_eq`), with `updateConfirmationM_locks_of_none`/`_of_some`, and its new
  locks are exactly its two arms (`mem_newLocksM`), with no fast lock without the fast arm
  (`newLocksM_no_fast`) and among the parent's at width `k` (`newLocksM_subset_parent`);
* **the optimistic confirmation off** is the identity (`optimisticConfirmationM_off`), so a
  property of the parent's optimistic result and of its input holds at every mode
  (`optimisticConfirmationM_of`), and a field the parent's keeps is kept
  (`optimisticConfirmationM_keep`). -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type}

/-! ### The parent's mode -/

theorem newLocksM_parent (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    (getConfirmation sp A Φ s).map (fun C => newLocksM sp (WriteMode.parent sp) A Φ t s C
      (Function.update A.saved s (some C.root)) A.locks) =
      EvidenceRelease.updateNewLocks sp A Φ t s :=
  rfl

theorem optimisticConfirmationM_on {m : WriteMode} (h : m.optimistic = true) :
    optimisticConfirmationM (FGP := FGP) sp m = optimisticConfirmation sp := by
  funext A Φ t
  unfold optimisticConfirmationM optimisticConfirmation
  rw [h]
  rfl

theorem optimisticConfirmationM_parent :
    optimisticConfirmationM (FGP := FGP) sp (WriteMode.parent sp) = optimisticConfirmation sp :=
  optimisticConfirmationM_on rfl

/-- **The optimistic write off** writes nothing. -/
theorem optimisticConfirmationM_off {m : WriteMode} (h : m.optimistic = false) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : optimisticConfirmationM sp m A Φ t = A := by
  unfold optimisticConfirmationM
  rw [h]

theorem optimisticConfirmationM_eq (m : WriteMode) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : optimisticConfirmationM sp m A Φ t =
      if m.optimistic then optimisticConfirmation sp A Φ t else A := by
  cases h : m.optimistic
  · exact optimisticConfirmationM_off h A Φ t
  · rw [optimisticConfirmationM_on h]; rfl

/-- A property of the parent's optimistic confirmation and of its input holds at every mode. -/
theorem optimisticConfirmationM_of {P : SAState sp.n → Prop} {m : WriteMode} {A : SAState sp.n}
    {Φ : Frm sp.n FGP} {t : Time} (h₁ : P (optimisticConfirmation sp A Φ t)) (h₂ : P A) :
    P (optimisticConfirmationM sp m A Φ t) := by
  rw [optimisticConfirmationM_eq]
  split_ifs
  exacts [h₁, h₂]

/-- A field that the parent's optimistic confirmation keeps is kept at every mode. -/
theorem optimisticConfirmationM_keep {α : Sort _} (f : SAState sp.n → α)
    (hf : ∀ (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time),
      f (optimisticConfirmation sp A Φ t) = f A)
    (m : WriteMode) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    f (optimisticConfirmationM sp m A Φ t) = f A :=
  optimisticConfirmationM_of (P := fun X => f X = f A) (hf A Φ t) rfl

theorem optimisticM_keeps (m : WriteMode) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmationM sp m A Φ t).votedSlot = A.votedSlot ∧
      (optimisticConfirmationM sp m A Φ t).restartTime = A.restartTime :=
  optimisticConfirmationM_of (P := fun X => X.votedSlot = A.votedSlot ∧
    X.restartTime = A.restartTime) (optimistic_keeps A Φ t) ⟨rfl, rfl⟩

theorem updateConfirmationM_of_parent {m : WriteMode} (hf : m.fastArm = true)
    (hw : m.width = sp.k) :
    updateConfirmationM (FGP := FGP) sp m = updateConfirmation sp := by
  obtain ⟨_, o, _⟩ := m
  dsimp only at hf hw
  subst hf hw
  rfl

theorem updateConfirmationM_parent :
    updateConfirmationM (FGP := FGP) sp (WriteMode.parent sp) = updateConfirmation sp :=
  rfl

/-! ### The update at a mode -/

/-- **The update at mode `m` is the parent's but for its locks.** -/
theorem updateConfirmationM_eq (m : WriteMode) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) : updateConfirmationM sp m A Φ t s =
      { updateConfirmation sp A Φ t s with locks := (updateConfirmationM sp m A Φ t s).locks } := by
  unfold updateConfirmationM updateConfirmation
  cases getConfirmation sp A Φ s with
  | none => rfl
  | some C => dsimp only

/-- Every field of the update but its locks is the parent's. -/
theorem updateConfirmationM_field {α : Sort _} (f : SAState sp.n → α)
    (hf : ∀ (X : SAState sp.n) (L : Set Lock), f { X with locks := L } = f X) (m : WriteMode)
    (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    f (updateConfirmationM sp m A Φ t s) = f (updateConfirmation sp A Φ t s) := by
  rw [updateConfirmationM_eq, hf]

theorem updateConfirmationM_keeps (m : WriteMode) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (s : Nat) : (updateConfirmationM sp m A Φ t s).votedSlot = A.votedSlot ∧
      (updateConfirmationM sp m A Φ t s).restartTime = A.restartTime := by
  rw [updateConfirmationM_field SAState.votedSlot (fun _ _ => rfl),
    updateConfirmationM_field SAState.restartTime (fun _ _ => rfl)]
  exact updateConfirmation_keeps A Φ t s

theorem updateConfirmationM_locks_of_none {m : WriteMode} {A : SAState sp.n} {Φ : Frm sp.n FGP}
    {t : Time} {s : Nat} (h : getConfirmation sp A Φ s = none) :
    (updateConfirmationM sp m A Φ t s).locks = A.locks := by
  unfold updateConfirmationM
  simp only [h]

theorem updateConfirmationM_locks_of_some {m : WriteMode} {A : SAState sp.n} {Φ : Frm sp.n FGP}
    {t : Time} {s : Nat} {C : Blk sp.n FGP} (h : getConfirmation sp A Φ s = some C) :
    (updateConfirmationM sp m A Φ t s).locks = addLocks sp A.locks Φ t s
      (newLocksM sp m A Φ t s C (Function.update A.saved s (some C.root)) A.locks) := by
  unfold updateConfirmationM
  simp only [h, Option.map_some]
  split_ifs <;> simp only [updateLatestConfirmed_keeps_locks]

/-- **The new locks at mode `m`** are exactly its two arms: the fast lock of the path when
`m.fastArm`, and the slow lock of width `m.width`. -/
theorem mem_newLocksM {m : WriteMode} {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time} {s : Nat}
    {C : Blk sp.n FGP} {sv : Int → Option Nat} {L : Set Lock} {p : Nat × Bool × Nat} :
    p ∈ newLocksM sp m A Φ t s C sv L ↔
      (m.fastArm = true ∧ ∃ B, deepest Φ {B | (B ∈ confirmationPath sp Φ C ∧
          ¬ conflictsWithLock sp A.locks Φ t B) ∧ FastTest sp A Φ s B} = some B ∧
        p = (B.root, true, fastExpiry sp L Φ t s)) ∨
      (∃ B, deepest Φ {B | (B ∈ confirmationPath sp Φ C ∧ ¬ conflictsWithLock sp A.locks Φ t B) ∧
          ∀ j : Int, (s : Int) - m.width < j → j < s →
            ∃ S ∈ Φ.tree, sv j = some S.root ∧ Φ.Anc B S} =
          some B ∧ p = (B.root, false, s + sp.k)) := by
  unfold newLocksM
  cases m.fastArm <;> simp

/-- **No fast lock without the fast arm.** -/
theorem newLocksM_no_fast {m : WriteMode} (h : m.fastArm = false) {A : SAState sp.n}
    {Φ : Frm sp.n FGP} {t : Time} {s : Nat} {C : Blk sp.n FGP} {sv : Int → Option Nat}
    {L : Set Lock} : ∀ p ∈ newLocksM sp m A Φ t s C sv L, p.2.1 = false := by
  intro p hp
  rcases mem_newLocksM.1 hp with ⟨hf, -⟩ | ⟨B, -, rfl⟩
  · rw [h] at hf; exact absurd hf Bool.false_ne_true
  · rfl

/-- At width `k` the new locks of mode `m` are among the parent's. -/
theorem newLocksM_subset_parent {m : WriteMode} (hw : m.width = sp.k) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (s : Nat) (C : Blk sp.n FGP) (sv : Int → Option Nat)
    (L : Set Lock) :
    newLocksM sp m A Φ t s C sv L ⊆ newLocksM sp (WriteMode.parent sp) A Φ t s C sv L := by
  intro p hp
  rcases mem_newLocksM.1 hp with ⟨-, h⟩ | h
  · exact mem_newLocksM.2 (Or.inl ⟨rfl, h⟩)
  · rw [hw] at h
    exact mem_newLocksM.2 (Or.inr h)

end Consensus.Goldilocks.SA

end
