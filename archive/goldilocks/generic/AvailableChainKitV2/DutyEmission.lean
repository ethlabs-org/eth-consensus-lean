module
public import AvailableChainEngineV2.Laws.Duty.SelfDelivery -- shake: keep (re-export)
public import AvailableChainEngineV2.Conditions.Duty.Committees -- shake: keep (re-export)
public import AvailableChainEngineV2.Conditions.Duty.Duties -- shake: keep (re-export)
public import AvailableChainEngineV2.Engine.Duty.Lift
public import AvailableChainKitV2.Emission

public section

namespace AvailableChain.V2.D.Engine

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}

/-- Signed emission keeps a duty witness; the label alone need not fix time. -/
theorem mem_tick_seat_iff (E : Generic.Env V) (rho : Run V P) (st : P.State) (v : V)
    (t : Time) (ℓ : P.Label) (i : Fin (P.seats ℓ)) (p : P.Payload) :
    (⟨.seat ℓ i, p⟩ : P.Object) ∈ (tick E rho st v t).2 ↔
      E.awake v t = true ∧ rho.seatOf ℓ i = v ∧
        ∃ d, P.signLabel d = ℓ ∧ P.actTime d = t ∧
          P.act (P.clock st t) d (rho.input v t) = some p := by
  simp only [tick]
  by_cases hw : E.awake v t = true
  · simp only [hw, ite_true, List.mem_append, List.mem_flatMap, List.mem_filterMap,
      Option.map_eq_some_iff, List.mem_map, true_and]
    constructor
    · rintro (⟨d, hd, i', hi', p', hp', heq⟩ | ⟨p', -, heq⟩)
      · have ha := congrArg Signed.auth heq
        have hl := (Auth.seat.inj ha).1
        have hp := congrArg Signed.payload heq
        have hh : Run.holder rho (.seat (P.signLabel d) i') =
            Run.holder rho (.seat ℓ i) := congrArg (Run.holder rho) ha
        simp only [Run.holder, Option.some.injEq] at hh
        simp only [Run.ownSeats, List.mem_filter, decide_eq_true_eq] at hi'
        exact ⟨hh ▸ hi'.2, d, hl, (P.duties_spec _ t).mp hd,
          hp'.trans (congrArg some hp)⟩
      · simp at heq
    · rintro ⟨hi, d, hl, ht, hp⟩
      subst ℓ
      left
      refine ⟨d, (P.duties_spec d t).mpr ht, i, ?_, p, hp, rfl⟩
      simp [Run.ownSeats, hi]
  · simp [hw]

/-- A due duty gives the exact form when due duties have distinct labels. -/
theorem mem_tick_duty_iff (E : Generic.Env V) (rho : Run V P) (st : P.State) (v : V)
    (t : Time) (d : P.Duty) (hd : P.actTime d = t) (hD : DutiesInjectiveAt P t)
    (i : Fin (P.seats (P.signLabel d))) (p : P.Payload) :
    (⟨.seat (P.signLabel d) i, p⟩ : P.Object) ∈ (tick E rho st v t).2 ↔
      E.awake v t = true ∧ rho.seatOf (P.signLabel d) i = v ∧
        P.act (P.clock st t) d (rho.input v t) = some p := by
  rw [mem_tick_seat_iff]
  constructor
  · rintro ⟨hw, hi, d', hl, ht, hp⟩
    exact ⟨hw, hi, hD d' d ht hd hl ▸ hp⟩
  · rintro ⟨hw, hi, hp⟩
    exact ⟨hw, hi, d, rfl, hd, hp⟩

/-- One due duty can emit without any injectivity premise. -/
theorem mem_tick_of_duty (E : Generic.Env V) (rho : Run V P) (st : P.State) (v : V)
    (t : Time) (d : P.Duty) (i : Fin (P.seats (P.signLabel d))) (p : P.Payload)
    (hw : E.awake v t = true) (hi : rho.seatOf (P.signLabel d) i = v)
    (ht : P.actTime d = t) (hp : P.act (P.clock st t) d (rho.input v t) = some p) :
    (⟨.seat (P.signLabel d) i, p⟩ : P.Object) ∈ (tick E rho st v t).2 :=
  (mem_tick_seat_iff E rho st v t _ i p).mpr ⟨hw, hi, d, rfl, ht, hp⟩

/-- A signing label with a bijective map has one owned seat. -/
theorem ownSeats_bijSeat (rho : Run V P) {ℓ : P.Label} (e : Fin (P.seats ℓ) ≃ V)
    (he : ∀ i, rho.seatOf ℓ i = e i) (v : V) : rho.ownSeats ℓ v = [e.symm v] := by
  have hp : (fun i => decide (rho.seatOf ℓ i = v)) = (fun i => decide (i = e.symm v)) := by
    funext i
    simp only [he, ← e.eq_symm_apply]
  rw [Run.ownSeats, hp, List.filter_eq,
    List.count_eq_one_of_mem (List.nodup_finRange _) (List.mem_finRange _)]
  rfl


/-- A bijective signing seat map fixes the seat, but does not fix the duty. -/
theorem emits_bijSeat (E : Generic.Env V) (rho : Run V P) {ℓ : P.Label}
    (e : Fin (P.seats ℓ) ≃ V) (he : ∀ i, rho.seatOf ℓ i = e i) (st : P.State) (v : V)
    (t : Time) (i : Fin (P.seats ℓ)) (p : P.Payload) :
    (⟨.seat ℓ i, p⟩ : P.Object) ∈ (tick E rho st v t).2 ↔
      i = e.symm v ∧ E.awake v t = true ∧
        ∃ d, P.signLabel d = ℓ ∧ P.actTime d = t ∧
          P.act (P.clock st t) d (rho.input v t) = some p := by
  rw [mem_tick_seat_iff, he, ← e.eq_symm_apply]
  tauto

/-- Identity-lift emission has exactly the old label-time form. -/
theorem mem_tick_seat_toD_iff {P : ProtocolSpec In} (E : Generic.Env V)
    (rho : V2.Run V P) (st : P.State) (v : V) (t : Time) (ℓ : P.Label)
    (i : Fin (P.seats ℓ)) (p : P.Payload) :
    (⟨.seat ℓ i, p⟩ : P.Object) ∈ (tick E rho.toD st v t).2 ↔
      E.awake v t = true ∧ P.actTime ℓ = t ∧ rho.seatOf ℓ i = v ∧
        P.act (P.clock st t) ℓ (rho.input v t) = some p := by
  rw [tick_toD]
  exact V2.Engine.mem_tick_seat_iff E rho st v t ℓ i p

end AvailableChain.V2.D.Engine
