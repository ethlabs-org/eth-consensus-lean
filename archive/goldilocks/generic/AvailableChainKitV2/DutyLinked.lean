module
public import AvailableChainEngineV2.Conditions.Duty.Committees
public import AvailableChainEngineV2.Conditions.Committees
public import AvailableChainEngineV2.Engine.Duty.Lift
public import AvailableChainKitV2.Emission

public section

namespace AvailableChain.V2.D.Engine

/-- A constant signing label has one seat bijection, independent of duties. -/
theorem linked_singleton_iff {V In : Type} {P : ProtocolSpecD In} (rho : Run V P)
    (ℓ : P.Label) :
    Linked (fun a => a = ℓ) rho ↔
      ∃ e : Fin (P.seats ℓ) ≃ V, ∀ i, rho.seatOf ℓ i = e i := by
  constructor
  · rintro ⟨N, e, h⟩
    obtain ⟨hn, hi⟩ := h ℓ rfl
    exact ⟨(finCongr hn).trans e, hi⟩
  · rintro ⟨e, he⟩
    refine ⟨P.seats ℓ, e, ?_⟩
    rintro a rfl
    exact ⟨rfl, he⟩

/-- Under the old Linked law, every round equation is equivalent to one
representative equation after the identity lift. The labels remain distinct. -/
theorem seat_family_iff_representative_toD {V In R : Type} {P : ProtocolSpec In}
    (rho : V2.Run V P) (fg : R → P.Label) (r₀ : R) (N : Nat)
    (hs : ∀ r, P.seats (fg r) = N) (e : Fin N ≃ V)
    (hL : V2.Linked (fun ℓ => ∃ r, fg r = ℓ) rho) :
    (∀ r i, rho.toD.seatOf (fg r) (Fin.cast (hs r).symm i) = e i) ↔
      (∀ i, rho.toD.seatOf (fg r₀) (Fin.cast (hs r₀).symm i) = e i) := by
  constructor
  · exact fun h => h r₀
  · intro h r i
    have hi := V2.Engine.linked_index_stable hL ⟨r, rfl⟩ ⟨r₀, rfl⟩
      (Fin.cast (hs r).symm i) (Fin.cast (hs r₀).symm i) rfl
    exact hi.trans (h i)

/-- An old round family supplies the single representative holder equation.
This direction needs only the supplied family, with no extra Linked premise. -/
theorem seat_equation_toD_of_family {V In R : Type} {P : ProtocolSpec In}
    (rho : V2.Run V P) (fg : R → P.Label) (r₀ : R) (N : Nat)
    (hs : ∀ r, P.seats (fg r) = N) (e : Fin N ≃ V)
    (he : ∀ r i, rho.seatOf (fg r) (Fin.cast (hs r).symm i) = e i) :
    ∀ i, rho.toD.seatOf (fg r₀) i = ((finCongr (hs r₀)).trans e) i := by
  intro i
  simpa using he r₀ (Fin.cast (hs r₀) i)

end AvailableChain.V2.D.Engine
