module
public import ConsensusModel.Conditions

@[expose] public section

/-! # Evidence and hashes (layer ½)

Evidence is generic: a validator is slashable on a set of objects if two of
them (possibly the same one) are signed by its key (through the run's PKI) and
the protocol's rule `conflicts` convicts them.

The hash is arbitrary run data. `HashCollision`: two distinct observed items
with one digest. No digest is reserved: a root (such as a genesis block) is an
explicit constructor of the protocol's parent references, not a digest. An
item is observed if it occurs in an object that an honest node released or
received, at any depth, under any signature; this is exactly the set of items
whose digests the engine passes to honest code. Honest code still chooses what
it signs, so collision resistance is an assumption about the deployed hash, not
a theorem. -/

namespace Consensus.Model


variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}

namespace Run

variable (rho : Run F E)

/-- `x` is slashable on the objects `A`. -/
def Slashable (A : Set (protoOf F E).Object) (x : V) : Prop :=
  ∃ o ∈ A, ∃ o' ∈ A, rho.signerOf o.auth = some x ∧ rho.signerOf o'.auth = some x ∧
    (protoOf F E).conflicts o o' = true

/-- No honest validator is slashable on what the honest nodes saw. -/
def HonestNeverSlashed : Prop :=
  ∀ v ∈ rho.honest, ¬ rho.Slashable rho.Observed v

/-- An item is observed: it is said by an object the honest nodes saw. -/
def ObservedItem (x : (protoOf F E).Item) : Prop :=
  ∃ o ∈ rho.Observed, o.item? = some x

/-- A hash collision was observed: two distinct observed items with one
digest. -/
def HashCollision : Prop :=
  ∃ x y, x ≠ y ∧ rho.ObservedItem x ∧ rho.ObservedItem y ∧ rho.hash x = rho.hash y

/-- The hash is injective: no collision can occur. -/
def InjectiveHash : Prop := Function.Injective rho.hash

end Run

end Consensus.Model

end
