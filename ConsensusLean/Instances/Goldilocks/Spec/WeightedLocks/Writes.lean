module
public import ConsensusLean.Instances.Goldilocks.Spec.WeightedLocks.Evidence
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Confirmation
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

/-! # Weighted locks: the writes

The evidence-release rule writes the parent's locks (goldilocks-spec.tex §"Confirmation"), each
with a weight fixed at its write: for each block `Y` at or below the block the lock is written
on (in the frame of the write), the number of validators that the confirmation writing it counted
for `Y`, and `0` for every other root (`weightBelow`). The origin of a new lock is the root of the
block it is written on.

* A fast lock of the update of slot `s` weighs the update's own count, its
  `confirmation_score` (`fastWeight`).
* A slow lock of the update of slot `s` weighs, for each `Y`, the **maximum over its `k`
  formation slots** `s, s − 1, …, s − k + 1` of the counts saved with those slots' confirmations
  (`slowWeight`). Each update of slot `s` saves its count before it writes, with or without a
  result (`saveCount`); a slot with no saved count counts `0`, and a restart drops the saved
  counts with the saved results.
* A lock of the optimistic confirmation of slot `s` weighs the optimistic test's count, its
  `optimisticVoters` (`optimisticWeight`).

The new locks of an update are the parent's (`updateNewLocks`, the update's `N`), and the writes
are `add_locks` on weighted locks (`updateLocksW`, `optimisticLocksW`). -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable (sp : SAParams) {FGP : Type}

open Classical in
/-- A weight fixed at a write on the block of root `o`: `f Y` for the block `Y` of root `r` when
`Y` is at or below `o` in the frame of the write, `0` otherwise. -/
noncomputable def weightBelow (Φ : Frm sp.n FGP) (o : Nat) (f : Blk sp.n FGP → Nat) :
    Nat → Nat :=
  fun r => match lookup Φ r with
    | some Y => if AncR Φ Y o then f Y else 0
    | none => 0

/-- The count of the update of slot `s` by root, saved at every update of slot `s` (with or
without a result): the update's `confirmation_score` for the block of root `r` (`0` off the
tree). A slow lock reads only counts of slots whose result is saved. -/
noncomputable def updateCount (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat) : Nat → Nat :=
  fun r => ((lookup Φ r).map (confirmationScore sp A Φ s)).getD 0

/-- The saved counts after the update of slot `s` saves its own count. -/
noncomputable def saveCount (C : Int → Nat → Nat) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (s : Nat) : Int → Nat → Nat :=
  Function.update C s (updateCount sp A Φ s)

/-- The weight of a fast lock of the update of slot `s` on the block of root `o`. -/
noncomputable def fastWeight (A : SAState sp.n) (Φ : Frm sp.n FGP) (s o : Nat) : Nat → Nat :=
  weightBelow sp Φ o (confirmationScore sp A Φ s)

/-- The weight of a slow lock of slot `s` on the block of root `o`, from the saved counts `C`:
for each block at or below `o`, the maximum over the formation slots `s − j`, `j < k`, of the
count saved for its root. -/
noncomputable def slowWeight (Φ : Frm sp.n FGP) (C : Int → Nat → Nat) (s o : Nat) : Nat → Nat :=
  weightBelow sp Φ o fun Y => (Finset.range sp.k).sup fun j => C ((s : Int) - j) Y.root

/-- The weight of an optimistic lock of slot `s` on the block of root `o`. -/
noncomputable def optimisticWeight (A : SAState sp.n) (Φ : Frm sp.n FGP) (s o : Nat) :
    Nat → Nat :=
  weightBelow sp Φ o fun Y => (optimisticVoters sp A Φ s Y).ncard

open Classical in
/-- The new locks `N` of the parent's update of slot `s` (`none` when it has no result): a fast
lock on the deepest unvetoed block of the result's path that passes the fast test, and a slow
lock on the deepest one that the saved results of the previous `k − 1` slots extend
(`updateConfirmation`'s `N`). -/
noncomputable def updateNewLocks (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    Option (Set (Nat × Bool × Nat)) :=
  (getConfirmation sp A Φ s).map fun C =>
    let A₁ := { A with saved := Function.update A.saved s (some C.root) }
    let path := {B | B ∈ confirmationPath sp Φ C ∧ ¬ conflictsWithLock sp A₁.locks Φ t B}
    let fast := FastTest sp A Φ s
    let slow := fun B : Blk sp.n FGP => ∀ j : Int, (s : Int) - sp.k < j → j < s →
      ∃ S ∈ Φ.tree, A₁.saved j = some S.root ∧ Φ.Anc B S
    let D := deepest Φ {B | B ∈ path ∧ fast B}
    let X := deepest Φ {B | B ∈ path ∧ slow B}
    {p | (∃ B, D = some B ∧ p = (B.root, true, fastExpiry sp A.locks Φ t s)) ∨
      (∃ B, X = some B ∧ p = (B.root, false, s + sp.k))}

/-- The weighted new locks of the update of slot `s`, from the parent's `N` and the saved counts
`C` (after `saveCount`): fast locks weigh the update's count, slow locks the maximum over their
formation slots. -/
noncomputable def updateWrites (A : SAState sp.n) (Φ : Frm sp.n FGP) (C : Int → Nat → Nat)
    (s : Nat) (N : Set (Nat × Bool × Nat)) : Set WLock :=
  {w | ∃ p ∈ N, w = ⟨⟨p.1, s, p.2.1, p.2.2⟩, p.1,
    if p.2.1 then fastWeight sp A Φ s p.1 else slowWeight sp Φ C s p.1⟩}

/-- The stored weighted locks after the update of slot `s`, from the saved counts `C` before it
(the update saves its own count first). -/
noncomputable def updateLocksW (W : Set WLock) (A : SAState sp.n) (C : Int → Nat → Nat)
    (Φ : Frm sp.n FGP) (t : Time) (s : Nat) : Set WLock :=
  match updateNewLocks sp A Φ t s with
  | none => W
  | some N => wlockStore.addLocksWith sp W (updateWrites sp A Φ (saveCount sp C A Φ s) s N) Φ t

/-- The weighted lock of the optimistic confirmation on `B`, of slot `slot(t)`. -/
noncomputable def optimisticWrite (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) : WLock :=
  ⟨⟨B.root, sp.slot t, true, fastExpiry sp A.locks Φ t (sp.slot t)⟩, B.root,
    optimisticWeight sp A Φ (sp.slot t) B.root⟩

/-- The stored weighted locks after the optimistic confirmation. -/
noncomputable def optimisticLocksW (W : Set WLock) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : Set WLock :=
  match optimisticSelect sp A Φ t with
  | none => W
  | some B => wlockStore.addLocksWith sp W {optimisticWrite sp A Φ t B} Φ t

end Consensus.Goldilocks.EvidenceRelease

end
