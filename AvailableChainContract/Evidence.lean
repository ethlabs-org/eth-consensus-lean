module
public import AvailableChainContract.Properties

@[expose] public section

/-! # Evidence and accountability

Evidence is generic: a validator is slashable on a set of objects if two of
them (possibly the same one) are held by it and the protocol's rule
`conflicts` convicts them. The evidence sets are what honest nodes saw
(`Run.View`), with everything carried inside. The threshold is fixed: a third
of the validators. -/

namespace AvailableChain.Contract

open AvailableChain.Generic

variable {V : Type} [Fintype V] [DecidableEq V] {F : Family} {E : Env V}

namespace Run

variable (rho : Run F E)

/-- `x` is slashable on the objects `A`. -/
def Slashable (A : Set (protoOf F E).Object) (x : V) : Prop :=
  ∃ o ∈ A, ∃ o' ∈ A, rho.holder o.auth = some x ∧ rho.holder o'.auth = some x ∧
    (protoOf F E).conflicts o o' = true

/-- The validators slashable on `A`. -/
noncomputable def slashedBy (A : Set (protoOf F E).Object) : Finset V := by
  classical
  exact Finset.univ.filter (rho.Slashable A)

/-- Accountable safety of `g` from `t₀`: two honest reads, at any nodes and
times, are compatible, or what the two readers saw slashes a third of the
validators. -/
def AccountablySafeFrom (g : Output F E) (t₀ : Time) : Prop :=
  ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t' : Time,
    t₀ ≤ t → t ≤ rho.horizon → t₀ ≤ t' → t' ≤ rho.horizon →
    CBlock.Compatible (rho.readOut g u t) (rho.readOut g v t') ∨
      Fintype.card V ≤ 3 * (rho.slashedBy (rho.View u t ∪ rho.View v t')).card

/-- No honest validator is slashable on what the honest nodes saw. -/
def HonestNeverSlashed : Prop :=
  ∀ v ∈ rho.honest, ¬ rho.Slashable rho.Observed v

end Run

end AvailableChain.Contract

end
