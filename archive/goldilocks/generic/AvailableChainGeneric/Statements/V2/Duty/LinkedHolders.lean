module
public import AvailableChainEngineV2.Conditions.Duty.Committees

@[expose] public section

namespace AvailableChain.V2.D.Engine
end AvailableChain.V2.D.Engine

open AvailableChain AvailableChain.V2 AvailableChain.V2.D AvailableChain.V2.D.Engine

namespace AvailableChain.Gen.V2.Duty

set_option linter.unusedVariables false in
-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Linked.lean:20.
def LinkedHolderEqStatement : Prop :=
  ∀ {V In : Type} {P : ProtocolSpecD In} {F : P.Label → Prop} {rho : D.Run V P}
    (hL : D.Linked F rho) {ℓ ℓ' : P.Label} (hℓ : F ℓ) (hℓ' : F ℓ')
    (i : Fin (P.seats ℓ)) (j : Fin (P.seats ℓ')) (h : i.val = j.val),
    rho.seatOf ℓ i = rho.seatOf ℓ' j

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Statements/V2/Linked.lean:27.
theorem LinkedHolderEqStatement_def :
    LinkedHolderEqStatement =
      (∀ {V In : Type} {P : ProtocolSpecD In} {F : P.Label → Prop} {rho : D.Run V P}
        (hL : D.Linked F rho) {ℓ ℓ' : P.Label} (hℓ : F ℓ) (hℓ' : F ℓ')
        (i : Fin (P.seats ℓ)) (j : Fin (P.seats ℓ')) (h : i.val = j.val),
        rho.seatOf ℓ i = rho.seatOf ℓ' j) := rfl

set_option linter.unusedVariables false in
-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Linked.lean:37.
def LinkedCardLeOfHoldersStatement : Prop :=
  ∀ {V In : Type} {P : ProtocolSpecD In} {F : P.Label → Prop} {rho : D.Run V P}
    (hL : D.Linked F rho) (I : Finset Nat) (X : Finset V)
    (hI : ∀ k ∈ I, ∃ ℓ, F ℓ ∧ ∃ i : Fin (P.seats ℓ),
      i.val = k ∧ rho.seatOf ℓ i ∈ X),
    I.card ≤ X.card

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Statements/V2/Linked.lean:45.
theorem LinkedCardLeOfHoldersStatement_def :
    LinkedCardLeOfHoldersStatement =
      (∀ {V In : Type} {P : ProtocolSpecD In} {F : P.Label → Prop} {rho : D.Run V P}
        (hL : D.Linked F rho) (I : Finset Nat) (X : Finset V)
        (hI : ∀ k ∈ I, ∃ ℓ, F ℓ ∧ ∃ i : Fin (P.seats ℓ),
          i.val = k ∧ rho.seatOf ℓ i ∈ X),
        I.card ≤ X.card) := rfl

end AvailableChain.Gen.V2.Duty
