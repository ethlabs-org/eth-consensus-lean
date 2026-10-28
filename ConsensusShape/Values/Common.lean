module
public import ConsensusShape.Realizable

@[expose] public section

/-! # Shared vocabulary of the shape values

Definitions used by more than one value (`Goldilocks`, `Streamlet`,
`Tendermint`): affine latency bounds (in the recurrence gap or the fault
count) and the final-only schema. Values are skeletons and contracts
only; they carry no protocol proofs. -/

namespace Consensus.Shape

/-- An affine bound `a + b·k` (a `Δ`-coefficient) in the index `k` (the
recurrence gap in slots, or a fault count). -/
structure Affine where
  a : Nat
  b : Nat

/-- The value of an affine bound at `k`. -/
def Affine.eval (f : Affine) (k : Nat) : Nat := f.a + f.b * k

/-- The final-only schema (`OutputSchema.BFTCore` with no other output): one
output, serving the final capability. -/
def bftCore : OutputSchema := ⟨Unit, fun | .final => some () | _ => none⟩

theorem bftCore_serves : bftCore.Serves := Or.inl rfl

end Consensus.Shape

end
