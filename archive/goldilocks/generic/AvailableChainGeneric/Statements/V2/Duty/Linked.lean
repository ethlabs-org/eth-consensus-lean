module
public import AvailableChainEngineV2.Conditions.Duty.Committees

@[expose] public section

open AvailableChain AvailableChain.V2

namespace AvailableChain.Gen.V2.Duty

/-- The committee of one signing label has one bijection for all its duties. -/
def LinkedSingletonStatement : Prop :=
  ∀ {V In : Type} {P : ProtocolSpecD In} (rho : D.Run V P) (ℓ : P.Label),
    D.Linked (fun a => a = ℓ) rho ↔
      ∃ e : Fin (P.seats ℓ) ≃ V, ∀ i, rho.seatOf ℓ i = e i

theorem LinkedSingletonStatement_def :
    LinkedSingletonStatement =
      (∀ {V In : Type} {P : ProtocolSpecD In} (rho : D.Run V P) (ℓ : P.Label),
        D.Linked (fun a => a = ℓ) rho ↔
          ∃ e : Fin (P.seats ℓ) ≃ V, ∀ i, rho.seatOf ℓ i = e i) := rfl

end AvailableChain.Gen.V2.Duty
