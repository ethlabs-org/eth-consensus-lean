module
public import ConsensusLean.Spec.Problem.Good
public import ConsensusLean.Lemmas.Problem.Derived
public import ConsensusLean.Lemmas.Problem.Facts.Atoms
public import ConsensusLean.Lemmas.Problem.Facts.Transfer
public import ConsensusLean.Lemmas.Problem.Facts.Network
public import ConsensusLean.Lemmas.Problem.Facts.Properties
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
public import ConsensusLean.Lemmas.Problem.Facts.Good
public import Mathlib.Tactic
@[expose] public section

/-! # Shared test fixtures

The identity PKI on `Fin n` and the one-output schema serving every
capability, shared by the test files. -/

namespace Consensus.Shape.Tests

/-- The identity PKI on `Fin n`: key `k` is validator `k`. -/
def pkiFin (n : Nat) : Fin (Fintype.card (Fin n)) ≃ Fin n := finCongr (Fintype.card_fin n)

/-- One output, serving every capability. -/
abbrev schema : OutputSchema := ⟨Unit, fun _ => some ()⟩

end Consensus.Shape.Tests

end
