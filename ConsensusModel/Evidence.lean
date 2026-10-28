module
public import ConsensusModel.Conditions

@[expose] public section

/-! # Evidence and hashes (layer ½)

Evidence is generic: a validator is slashable on a set of objects if two of
them (possibly the same one) are signed by seats it holds and the protocol's
rule `conflicts` convicts them.

The hash is arbitrary run data. `HashCollision`: two distinct observed items
with one digest, or an observed item with digest `0` (reserved for a root, such
as a genesis block). An item is observed if it occurs in an object that an
honest node released or received, at any depth, under any signature; this is
exactly the set of items whose digests the engine passes to honest code.
Honest code still chooses what it signs, so collision resistance (including
"no item hashes to 0") is an assumption about the deployed hash, not a
theorem. -/

namespace Consensus.Model


variable {V : Type} [Fintype V] [DecidableEq V] {F : Family} {E : Env V}

namespace Run

variable (rho : Run F E)

/-- `x` is slashable on the objects `A`. -/
def Slashable (A : Set (protoOf F E).Object) (x : V) : Prop :=
  ∃ o ∈ A, ∃ o' ∈ A, rho.holderOf o.auth = some x ∧ rho.holderOf o'.auth = some x ∧
    (protoOf F E).conflicts o o' = true

/-- No honest validator is slashable on what the honest nodes saw. -/
def HonestNeverSlashed : Prop :=
  ∀ v ∈ rho.honest, ¬ rho.Slashable rho.Observed v

/-- An item is observed: it is said by an object the honest nodes saw. -/
def ObservedItem (x : (protoOf F E).Item) : Prop :=
  ∃ o ∈ rho.Observed, o.item? = some x

/-- A hash collision was observed: two distinct observed items with one
digest, or an observed item with digest `0`. -/
def HashCollision : Prop :=
  (∃ x y, x ≠ y ∧ rho.ObservedItem x ∧ rho.ObservedItem y ∧ rho.hash x = rho.hash y) ∨
    ∃ x, rho.ObservedItem x ∧ rho.hash x = 0

/-- The hash is injective and never `0`: no collision can occur. -/
def InjectiveHash : Prop := Function.Injective rho.hash ∧ ∀ x, rho.hash x ≠ 0

end Run

end Consensus.Model

end
