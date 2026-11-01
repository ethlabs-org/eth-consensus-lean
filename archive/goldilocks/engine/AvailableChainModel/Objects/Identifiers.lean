module
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Basic

@[expose] public section

namespace AvailableChain

abbrev Slot := Nat

/-- A nominal block root. -/
@[ext]
structure BlockId where
  value : Nat
deriving DecidableEq, Repr

private theorem BlockId.value_injective : Function.Injective BlockId.value := by
  intro left right equal
  exact BlockId.ext equal

instance : LinearOrder BlockId :=
  LinearOrder.lift' BlockId.value (by exact BlockId.value_injective)

def genesisRoot : BlockId := ⟨0⟩

end AvailableChain
end
