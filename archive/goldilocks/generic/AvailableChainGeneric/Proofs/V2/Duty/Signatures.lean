module
public import AvailableChainGeneric.Statements.V2.Duty.Signatures
public import AvailableChainEngineV2.Engine.Duty.Lift
public import AvailableChainKitV2.DutyEmission

public section

open AvailableChain AvailableChain.V2

namespace AvailableChain.Gen.V2.Duty

variable {V In : Type} [DecidableEq V] {P : ProtocolSpecD In}

/-- A SingleDuty label recovers the old exact time and action form. -/
theorem mem_tick_singleDuty_iff (E : Generic.Env V) (rho : D.Run V P)
    (st : P.State) (v : V) (t : Time) (ℓ : P.Label) (h : SingleDuty P ℓ)
    (d : P.Duty) (hd : P.signLabel d = ℓ) (i : Fin (P.seats ℓ)) (p : P.Payload) :
    (⟨.seat ℓ i, p⟩ : P.Object) ∈ (D.tick E rho st v t).2 ↔
      E.awake v t = true ∧ P.actTime d = t ∧ rho.seatOf ℓ i = v ∧
        P.act (P.clock st t) d (rho.input v t) = some p := by
  obtain ⟨d₀, _, huniq⟩ := h
  rw [D.Engine.mem_tick_seat_iff]
  constructor
  · rintro ⟨hw, hi, d', hl, ht, hp⟩
    have heq : d' = d := (huniq d' hl).trans (huniq d hd).symm
    subst d'
    exact ⟨hw, ht, hi, hp⟩
  · rintro ⟨hw, ht, hi, hp⟩
    exact ⟨hw, hi, d, hd, ht, hp⟩

theorem emitted_unique_singleDuty_statement : EmittedUniqueSingleDutyStatement := by
  intro V In _ P E rho hn ℓ hD i v j k t u p q hj hk hp hq
  obtain ⟨d, hd, hu⟩ := hD
  have hD : SingleDuty P ℓ := ⟨d, hd, hu⟩
  rw [(D.Run.step_tick_eq E rho hj).2] at hp
  rw [(D.Run.step_tick_eq E rho hk).2] at hq
  obtain ⟨_, ht, _, hp⟩ := (mem_tick_singleDuty_iff E rho _ v t ℓ hD d hd i p).mp hp
  obtain ⟨_, ht', _, hq⟩ := (mem_tick_singleDuty_iff E rho _ v u ℓ hD d hd i q).mp hq
  subst t
  subst u
  have hjk : j = k := (List.Nodup.getElem?_inj
    (List.getElem?_eq_some_iff.mp hj).1 hn).mp (hj.trans hk.symm)
  subst k
  exact ⟨rfl, Option.some.inj (hp.symm.trans hq)⟩

/-- The object form has the same conclusion as the old G12. -/
theorem emitted_unique_of_singleDuty (E : Generic.Env V) (rho : D.Run V P)
    (hn : rho.events.Nodup) (ℓ : P.Label) (hD : SingleDuty P ℓ)
    (i : Fin (P.seats ℓ)) (v : V) (j k : Nat) (t u : Time) (o o' : P.Object)
    (hj : rho.events[j]? = some (.tick v t)) (hk : rho.events[k]? = some (.tick v u))
    (ho : o ∈ D.Run.emitsAt E rho j) (ho' : o' ∈ D.Run.emitsAt E rho k)
    (ha : o.auth = .seat ℓ i) (ha' : o'.auth = .seat ℓ i) :
    j = k ∧ o = o' := by
  cases o with
  | mk a p =>
    cases o' with
    | mk a' q =>
      cases ha
      cases ha'
      obtain ⟨hjk, hpq⟩ := emitted_unique_singleDuty_statement E rho hn ℓ hD i v j k t u
        p q hj hk ho ho'
      exact ⟨hjk, congrArg (Signed.mk (.seat ℓ i)) hpq⟩

theorem emit_unique_of_emitOnce : EmitUniqueOfEmitOnceStatement := by
  intro V In _ P E rho ℓ h i hh p j k t u hj hk hp hq
  have hjk := h i hh p j k t u hj hk hp hq
  subst k
  exact ⟨rfl, (Event.tick.inj (Option.some.inj (hj.symm.trans hk))).2⟩

/-- Due-duty injectivity also identifies explicit event-duty witnesses. -/
theorem emit_duty_unique_of_emitOnce (E : Generic.Env V) (rho : D.Run V P)
    (ℓ : P.Label) (h : EmitOnceUnder E rho ℓ) (i : Fin (P.seats ℓ))
    (hh : rho.seatOf ℓ i ∈ rho.honest) (p : P.Payload) (j k : Nat) (d d' : P.Duty)
    (hd : P.signLabel d = ℓ) (hd' : P.signLabel d' = ℓ)
    (hD : D.DutiesInjectiveAt P (P.actTime d))
    (hj : rho.events[j]? = some (.tick (rho.seatOf ℓ i) (P.actTime d)))
    (hk : rho.events[k]? = some (.tick (rho.seatOf ℓ i) (P.actTime d')))
    (hp : (⟨.seat ℓ i, p⟩ : P.Object) ∈ D.Run.emitsAt E rho j)
    (hq : (⟨.seat ℓ i, p⟩ : P.Object) ∈ D.Run.emitsAt E rho k) : j = k ∧ d = d' := by
  obtain ⟨hjk, ht⟩ := emit_unique_of_emitOnce E rho ℓ h i hh p j k _ _ hj hk hp hq
  exact ⟨hjk, hD d d' rfl ht.symm (hd.trans hd'.symm)⟩

/-- The identity lift has one duty for every old label. -/
theorem singleDuty_toD {P : ProtocolSpec In} (ℓ : P.Label) : SingleDuty P.toD ℓ :=
  ⟨ℓ, rfl, fun _ h => h⟩

theorem honest_unique_singleDuty_statement : HonestUniqueSingleDutyStatement := by
  rw [HonestUniqueSingleDutyStatement_def]
  intro V _ In P E rho hnodup hU hhandles ℓ hD i hh o₁ o₂ ha₁ ha₂ h₁ h₂
  have origin : ∀ o : P.Object, o.auth = .seat ℓ i →
      ((∃ t, D.Run.emits E rho (rho.seatOf ℓ i) o t) ∨
        ∃ j v t, D.Run.handlesAt E rho j v o t) →
      ∃ t, D.Run.emits E rho (rho.seatOf ℓ i) o t := by
    intro o ha ho
    rcases ho with ho | ⟨j, v, t, envelope, he, hc⟩
    · exact ho
    · have hholder : D.Run.holder rho o.auth = some (rho.seatOf ℓ i) := by
        rw [ha]
        rfl
      rcases hhandles _ _ _ hc with rfl | hc
      · obtain ⟨t', _, hem⟩ := hU.unforgeable v envelope t ⟨j, he⟩ _ hh hholder
        exact ⟨t', hem⟩
      · obtain ⟨t', _, hem⟩ := hU.carried v envelope t ⟨j, he⟩ o hc _ hh hholder
        exact ⟨t', hem⟩
  obtain ⟨t₁, j₁, he₁, ho₁⟩ := origin o₁ ha₁ h₁
  obtain ⟨t₂, j₂, he₂, ho₂⟩ := origin o₂ ha₂ h₂
  exact (emitted_unique_of_singleDuty E rho hnodup ℓ hD i (rho.seatOf ℓ i)
    j₁ j₂ t₁ t₂ o₁ o₂ he₁ he₂ ho₁ ho₂ ha₁ ha₂).2

end AvailableChain.Gen.V2.Duty
