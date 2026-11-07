module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Locks

@[expose] public section

/-! # Lock rules: stored locks and an unlock stage after the parent's unlock

The operational part of a variant of the SA's lock rules that keeps Goldilocks' `live_locks`,
`add_locks` and `unlock` (goldilocks-spec.tex §"Locks") and changes two things:

* **the stored lock** (`LockStore`): a type `Lk`, the forgetful map `lock : Lk → Lock` to the
  parent's lock, and `withBlock`, the move of a stored lock to the block of another root. A move
  changes the block and nothing else, so data a lock carries from its write (such as a weight)
  travels with it, and two writes with the same lock tuple stay two stored locks;
* **an unlock stage** (`UnlockStage`) after the parent's unlock: a lock of a slot below `s` whose
  parent target is `T` moves on to `target c Φ V s w T`, which may read a context `c` (node state
  the stage reads; `Unit` when none) and the stored lock.

`LockStore.liveLocks` and `LockStore.addLocksWith` are `live_locks` and `add_locks` on stored
locks, and `LockStore.unlockWith` is the variant's unlock: the parent's `unlock`, then the stage.
The parent's own rules are the instance `lockStore` (`Lk = Lock`, `lock = id`) with the stage
`UnlockStage.id`, which keeps the parent's target. The laws a store and a stage satisfy, and the
step properties they give, are stated and proved outside the Spec. -/

namespace Consensus.Goldilocks.SA

/-- A lock store: the stored lock type, the forgetful map to the parent's `Lock`, and the move of
a stored lock to the block of root `r`. -/
structure LockStore where
  /-- The stored lock. -/
  Lk : Type
  /-- The lock as the parent stores it. -/
  lock : Lk → Lock
  /-- The stored lock moved to the block of root `r`. -/
  withBlock : Lk → Nat → Lk

/-- An unlock stage after the parent's unlock, for stored locks of `S`, reading a context of type
`σ`: the block a stored lock `w` of a slot below `s` with parent target `T` moves to, against the
slot-`s` votes of `V`. -/
structure UnlockStage (sp : SAParams) (S : LockStore) (σ : Type) where
  /-- The block `w` moves to from its parent target `T`. -/
  target : ∀ {FGP : Type}, σ → Frm sp.n FGP → View sp.n → Int → S.Lk → Blk sp.n FGP →
    Blk sp.n FGP

namespace LockStore

variable (S : LockStore) (sp : SAParams) {FGP : Type}

/-- `live_locks` on stored locks: each live stored lock moved back to its viable ancestor. -/
def liveLocks (L : Set S.Lk) (Φ : Frm sp.n FGP) (t : Time) : Set S.Lk :=
  {w' | ∃ w ∈ L, ∃ B ∈ Φ.tree, B.root = (S.lock w).block ∧ (S.lock w).LiveAt sp t ∧
    w' = S.withBlock w (Φ.viableAncestor B).root}

/-- `add_locks` on stored locks: the live locks of the stored set with the new stored locks `N`
(each written with its block, slot, fast bit and expiry and its own data). -/
def addLocksWith (L N : Set S.Lk) (Φ : Frm sp.n FGP) (t : Time) : Set S.Lk :=
  S.liveLocks sp (L ∪ N) Φ t

/-- The variant's unlock (`E ∘ unlock`): every live stored lock of a slot below `s` moves to the
stage's target of its parent unlock target (`unlockTarget`); the others keep their place. -/
noncomputable def unlockWith {σ : Type} (E : UnlockStage sp S σ) (c : σ) (L : Set S.Lk)
    (Φ : Frm sp.n FGP) (t : Time) (s : Int) (V : View sp.n) : Set S.Lk :=
  {w' | ∃ w ∈ S.liveLocks sp L Φ t, ∃ B ∈ Φ.tree, B.root = (S.lock w).block ∧
    w' = if ((S.lock w).slot : Int) < s then
      S.withBlock w (E.target c Φ V s w (unlockTarget sp Φ V s B)).root else w}

end LockStore

/-- The parent's lock store: `Lock` itself, moved by changing its block. -/
abbrev lockStore : LockStore where
  Lk := Lock
  lock l := l
  withBlock l r := { l with block := r }

/-- The stage that adds nothing: the parent's target. -/
def UnlockStage.id (sp : SAParams) (S : LockStore) (σ : Type) : UnlockStage sp S σ where
  target _ _ _ _ _ T := T

end Consensus.Goldilocks.SA

end
