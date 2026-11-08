module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.WriteModes.Writes
public import ConsensusLean.Instances.Goldilocks.Spec.WeightedLocks.Writes

@[expose] public section

/-! # Weighted locks: the writes at a write mode

The evidence-release writes (`Spec/WeightedLocks/Writes`) at a write mode `m`
(`Milestones/Spec/WriteModes/Writes`), written once and uniformly in the mode:

* the new locks of the update of slot `s` are the mode's (`newLocksM`, with the update's result
  saved at `s` and the stored locks), `none` when it has no result (`updateNewLocksM`);
* a fast lock weighs the update's count (`fastWeight`), a slow lock the maximum over its
  formation slots `s, …, s − max m.width 1 + 1` of the saved counts (`slowWeightW`), as at width
  `k` (`slowWeight`) (`updateWritesM`);
* the stored weighted locks after the update (`updateLocksWM`) and after the optimistic
  confirmation, which writes only when `m.optimistic` (`optimisticLocksWM`).

The slow weight reads the window the slow lock is formed on, `max m.width 1` slots ending at `s`:
`newLocksM` reads the update's own result and the saved results of the previous `m.width − 1`
slots, so width `0` writes the width-`1` lock, and the weight is the width-`1` weight too.

Each definition reads the mode only through its fields; none tests whether the mode is the
parent's. That they are the evidence-release writes at the parent's mode is a theorem
(`Lemmas/Candidates/WeightedWrites`). Definitions only. -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable (sp : SAParams) {FGP : Type}

/-- The weight of a slow lock of width `w` of slot `s` on the block of root `o`, from the saved
counts `C`: for each block at or below `o`, the maximum over the formation slots `s − j`,
`j < max w 1`, of the count saved for its root. The window is the lock's own: `newLocksM` reads
the update's result at `s` and the saved results of the previous `w − 1` slots, so width `0` is
width `1` in both. -/
noncomputable def slowWeightW (w : Nat) (Φ : Frm sp.n FGP) (C : Int → Nat → Nat) (s o : Nat) :
    Nat → Nat :=
  weightBelow sp Φ o fun Y => (Finset.range (max w 1)).sup fun j => C ((s : Int) - j) Y.root

/-- The new locks of the update of slot `s` at mode `m` (`none` when it has no result): the
mode's new locks for the update's result, read with the result saved at `s` and the stored
locks. -/
noncomputable def updateNewLocksM (m : WriteMode) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (s : Nat) : Option (Set (Nat × Bool × Nat)) :=
  (getConfirmation sp A Φ s).map fun C =>
    newLocksM sp m A Φ t s C (Function.update A.saved s (some C.root)) A.locks

/-- The weighted new locks of the update of slot `s` at mode `m`, from the new locks `N` and the
saved counts `C` (after `saveCount`): fast locks weigh the update's count, slow locks the maximum
over their `m.width` formation slots. -/
noncomputable def updateWritesM (m : WriteMode) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (C : Int → Nat → Nat) (s : Nat) (N : Set (Nat × Bool × Nat)) : Set WLock :=
  {w | ∃ p ∈ N, w = ⟨⟨p.1, s, p.2.1, p.2.2⟩, p.1,
    if p.2.1 then fastWeight sp A Φ s p.1 else slowWeightW sp m.width Φ C s p.1⟩}

/-- The stored weighted locks after the update of slot `s` at mode `m`, from the saved counts `C`
before it (the update saves its own count first). -/
noncomputable def updateLocksWM (m : WriteMode) (W : Set WLock) (A : SAState sp.n)
    (C : Int → Nat → Nat) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) : Set WLock :=
  match updateNewLocksM sp m A Φ t s with
  | none => W
  | some N => wlockStore.addLocksWith sp W (updateWritesM sp m A Φ (saveCount sp C A Φ s) s N) Φ t

/-- The stored weighted locks after the optimistic confirmation at mode `m`: its weighted lock
when `m.optimistic`, nothing otherwise. -/
noncomputable def optimisticLocksWM (m : WriteMode) (W : Set WLock) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : Set WLock :=
  match m.optimistic with
  | false => W
  | true => optimisticLocksW sp W A Φ t

end Consensus.Goldilocks.EvidenceRelease

end
