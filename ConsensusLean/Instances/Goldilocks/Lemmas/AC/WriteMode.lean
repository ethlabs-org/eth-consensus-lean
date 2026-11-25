module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.HandlerFields
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.WriteModes.Writes

public section

/-! # AC handlers at a write mode

The AC's handlers with the locks after the unlock given (`Lemmas/AC/RelTrace`) and the writes of
a write mode `m` (`Milestones/Spec/WriteModes/Writes`): `tryVoteWithM`, `acOnTickWithM`,
`acOnMessageWithM`, `acOnBlockWithM`, the call `stepWithM`, and the unlock input `callInputM` and
view `callViewM` of a call. The proposal writes nothing and is `acProposalWith`; `ac_to_fg` and
the restart are the parent's (the restart's replay runs while the node is not joined, so its
optimistic confirmations select nothing).
The optimistic confirmation is the parent's at every mode.

The laws:

* **the parent's mode**: at `WriteMode.parent sp` each handler is the parent's
  (`stepWithM_parent`, `callInputM_parent`, `callViewM_parent`);
* **the update at any mode** changes only the parent's fields and its locks
  (`updateConfirmationM_eq`), with `updateConfirmationM_locks_of_none`/`_of_some`, and its new
  locks are exactly its two arms (`mem_newLocksM`). -/

namespace Consensus.Goldilocks.AC

variable {sp : ACParams} {FGP : Type}

/-! ### The update at a mode -/

/-- **The update at mode `m` is the parent's but for its locks.** -/
theorem updateConfirmationM_eq (m : WriteMode) (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) : updateConfirmationM sp m A Φ t s =
      { updateConfirmation sp A Φ t s with locks := (updateConfirmationM sp m A Φ t s).locks } := by
  unfold updateConfirmationM updateConfirmation
  cases getConfirmation sp A Φ s with
  | none => rfl
  | some C => dsimp only

/-- Every field of the update but its locks is the parent's. -/
theorem updateConfirmationM_field {α : Sort _} (f : ACState sp.n → α)
    (hf : ∀ (X : ACState sp.n) (L : Set Lock), f { X with locks := L } = f X) (m : WriteMode)
    (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    f (updateConfirmationM sp m A Φ t s) = f (updateConfirmation sp A Φ t s) := by
  rw [updateConfirmationM_eq, hf]

theorem updateConfirmationM_keeps (m : WriteMode) (A : ACState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (s : Nat) : (updateConfirmationM sp m A Φ t s).votedSlot = A.votedSlot ∧
      (updateConfirmationM sp m A Φ t s).restartTime = A.restartTime := by
  rw [updateConfirmationM_field ACState.votedSlot (fun _ _ => rfl),
    updateConfirmationM_field ACState.restartTime (fun _ _ => rfl)]
  exact updateConfirmation_keeps A Φ t s

theorem updateConfirmationM_locks_of_none {m : WriteMode} {A : ACState sp.n} {Φ : Frm sp.n FGP}
    {t : Time} {s : Nat} (h : getConfirmation sp A Φ s = none) :
    (updateConfirmationM sp m A Φ t s).locks = A.locks := by
  unfold updateConfirmationM
  simp only [h]

theorem updateConfirmationM_locks_of_some {m : WriteMode} {A : ACState sp.n} {Φ : Frm sp.n FGP}
    {t : Time} {s : Nat} {C : Blk sp.n FGP} (h : getConfirmation sp A Φ s = some C) :
    (updateConfirmationM sp m A Φ t s).locks = addLocks sp A.locks Φ t s
      (newLocksM sp m A Φ t s C (Function.update A.saved s (some C.root)) A.locks) := by
  unfold updateConfirmationM
  simp only [h, Option.map_some]
  split_ifs <;> simp only [updateLatestConfirmed_keeps_locks]

/-- **The new locks at mode `m`** are exactly its two arms: the fast lock of the path when
`m.fastArm`, and the slow lock of width `m.width`. -/
theorem mem_newLocksM {m : WriteMode} {A : ACState sp.n} {Φ : Frm sp.n FGP} {t : Time} {s : Nat}
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

end Consensus.Goldilocks.AC

end
