module
public import AvailableChainEngineV2.Conditions.Committees

@[expose] public section

/-! Step-4b item S4b-14; the last Lead ruling in step4b-plan.md
(sha256 ebf5dc07). Linked is AvailableChain.V2.Linked, defined in
AvailableChainEngineV2/Conditions/Committees.lean:44. -/

-- Register the required Engine namespace without a KitV2 import.
namespace AvailableChain.V2.Engine
end AvailableChain.V2.Engine

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

namespace AvailableChain.Gen.V2

-- Keep the plan's binder names in the closed Statement.
set_option linter.unusedVariables false in
def LinkedHolderEqStatement : Prop :=
  ∀ {V In : Type} {P : ProtocolSpec In} {F : P.Label → Prop} {rho : Run V P}
    (hL : Linked F rho) {ℓ ℓ' : P.Label} (hℓ : F ℓ) (hℓ' : F ℓ')
    (i : Fin (P.seats ℓ)) (j : Fin (P.seats ℓ')) (h : i.val = j.val),
    rho.seatOf ℓ i = rho.seatOf ℓ' j

set_option linter.unusedVariables false in
theorem LinkedHolderEqStatement_def :
    LinkedHolderEqStatement =
      (∀ {V In : Type} {P : ProtocolSpec In} {F : P.Label → Prop} {rho : Run V P}
        (hL : Linked F rho) {ℓ ℓ' : P.Label} (hℓ : F ℓ) (hℓ' : F ℓ')
        (i : Fin (P.seats ℓ)) (j : Fin (P.seats ℓ')) (h : i.val = j.val),
        rho.seatOf ℓ i = rho.seatOf ℓ' j) := by
  rw [LinkedHolderEqStatement]

-- Keep the plan's binder names in the closed Statement.
set_option linter.unusedVariables false in
def LinkedCardLeOfHoldersStatement : Prop :=
  ∀ {V In : Type} {P : ProtocolSpec In} {F : P.Label → Prop} {rho : Run V P}
    (hL : Linked F rho) (I : Finset Nat) (X : Finset V)
    (hI : ∀ k ∈ I, ∃ ℓ, F ℓ ∧ ∃ i : Fin (P.seats ℓ),
      i.val = k ∧ rho.seatOf ℓ i ∈ X),
    I.card ≤ X.card

set_option linter.unusedVariables false in
theorem LinkedCardLeOfHoldersStatement_def :
    LinkedCardLeOfHoldersStatement =
      (∀ {V In : Type} {P : ProtocolSpec In} {F : P.Label → Prop} {rho : Run V P}
        (hL : Linked F rho) (I : Finset Nat) (X : Finset V)
        (hI : ∀ k ∈ I, ∃ ℓ, F ℓ ∧ ∃ i : Fin (P.seats ℓ),
          i.val = k ∧ rho.seatOf ℓ i ∈ X),
        I.card ≤ X.card) := by
  rw [LinkedCardLeOfHoldersStatement]

end AvailableChain.Gen.V2
