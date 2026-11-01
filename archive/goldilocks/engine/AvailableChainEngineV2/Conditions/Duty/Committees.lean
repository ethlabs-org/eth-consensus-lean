module
public import Mathlib.Data.Fintype.Card
public import AvailableChainEngineV2.Engine.Duty.Run

@[expose] public section

namespace AvailableChain.V2.D

open AvailableChain

variable {V : Type} {In : Type} {P : ProtocolSpecD In}

structure LabelFamilies (P : ProtocolSpecD In) where
  ap : P.Label → Prop
  fresh : P.Label → Prop
  linked : P.Label → Prop

def CStar (F : P.Label → Prop) (rho : Run V P) : Prop :=
  ∀ ℓ, F ℓ → Function.Bijective (rho.seatOf ℓ)

def Linked (F : P.Label → Prop) (rho : Run V P) : Prop :=
  ∃ (N : Nat) (e : Fin N ≃ V), ∀ ℓ, F ℓ →
    ∃ h : P.seats ℓ = N, ∀ i, rho.seatOf ℓ i = e (Fin.cast h i)

def SingleSeat (P : ProtocolSpecD In) (F : P.Label → Prop) : Prop :=
  ∀ ℓ, F ℓ → P.seats ℓ = 1

theorem Linked.toCStar {F : P.Label → Prop} {rho : Run V P} (h : Linked F rho) :
    CStar F rho := by
  obtain ⟨N, e, hF⟩ := h
  intro ℓ hℓ
  obtain ⟨hN, hs⟩ := hF ℓ hℓ
  have hfun : rho.seatOf ℓ = e ∘ Fin.cast hN := funext hs
  rw [hfun]
  exact e.bijective.comp (finCongr hN).bijective

theorem CStar.seats_eq [Fintype V] {F : P.Label → Prop} {rho : Run V P}
    (h : CStar F rho) {ℓ : P.Label} (hℓ : F ℓ) : P.seats ℓ = Fintype.card V := by
  rw [← Fintype.card_of_bijective (h ℓ hℓ), Fintype.card_fin]

end AvailableChain.V2.D

end
