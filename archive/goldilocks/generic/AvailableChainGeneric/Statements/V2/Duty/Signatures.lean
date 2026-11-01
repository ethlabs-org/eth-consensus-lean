module
public import AvailableChainEngineV2.Conditions.Duty.Schedule
public import AvailableChainEngineV2.Conditions.Duty.Duties -- shake: keep (re-export)

@[expose] public section

open AvailableChain AvailableChain.V2

namespace AvailableChain.Gen.V2.Duty

/-- Exactly one duty uses this signing label. -/
def SingleDuty {In : Type} (P : ProtocolSpecD In) (ℓ : P.Label) : Prop :=
  ∃! d, P.signLabel d = ℓ

theorem SingleDuty_def {In : Type} (P : ProtocolSpecD In) (ℓ : P.Label) :
    SingleDuty P ℓ = (∃! d, P.signLabel d = ℓ) := rfl

/-- Each honest holder emits each full content at most once under this label.
Different payloads may be emitted at different events. -/
def EmitOnceUnder {V In : Type} [DecidableEq V] {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P) (ℓ : P.Label) : Prop :=
  ∀ (i : Fin (P.seats ℓ)), rho.seatOf ℓ i ∈ rho.honest →
    ∀ (p : P.Payload) (j k : Nat) (t u : Time),
      rho.events[j]? = some (.tick (rho.seatOf ℓ i) t) →
      rho.events[k]? = some (.tick (rho.seatOf ℓ i) u) →
      (⟨.seat ℓ i, p⟩ : P.Object) ∈ D.Run.emitsAt E rho j →
      (⟨.seat ℓ i, p⟩ : P.Object) ∈ D.Run.emitsAt E rho k → j = k

theorem EmitOnceUnder_def {V In : Type} [DecidableEq V] {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P) (ℓ : P.Label) :
    EmitOnceUnder E rho ℓ =
      (∀ (i : Fin (P.seats ℓ)), rho.seatOf ℓ i ∈ rho.honest →
        ∀ (p : P.Payload) (j k : Nat) (t u : Time),
          rho.events[j]? = some (.tick (rho.seatOf ℓ i) t) →
          rho.events[k]? = some (.tick (rho.seatOf ℓ i) u) →
          (⟨.seat ℓ i, p⟩ : P.Object) ∈ D.Run.emitsAt E rho j →
          (⟨.seat ℓ i, p⟩ : P.Object) ∈ D.Run.emitsAt E rho k → j = k) := rfl

/-- G12 for a label with one duty. -/
def EmittedUniqueSingleDutyStatement : Prop :=
  ∀ {V In : Type} [DecidableEq V] {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P), rho.events.Nodup →
    ∀ (ℓ : P.Label), SingleDuty P ℓ →
    ∀ (i : Fin (P.seats ℓ)) (v : V) (j k : Nat) (t u : Time) (p q : P.Payload),
      rho.events[j]? = some (.tick v t) → rho.events[k]? = some (.tick v u) →
      (⟨.seat ℓ i, p⟩ : P.Object) ∈ D.Run.emitsAt E rho j →
      (⟨.seat ℓ i, q⟩ : P.Object) ∈ D.Run.emitsAt E rho k →
      j = k ∧ p = q

/-- Full-content uniqueness gives one event and one event time. -/
def EmitUniqueOfEmitOnceStatement : Prop :=
  ∀ {V In : Type} [DecidableEq V] {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P) (ℓ : P.Label), EmitOnceUnder E rho ℓ →
    ∀ (i : Fin (P.seats ℓ)), rho.seatOf ℓ i ∈ rho.honest →
    ∀ (p : P.Payload) (j k : Nat) (t u : Time),
      rho.events[j]? = some (.tick (rho.seatOf ℓ i) t) →
      rho.events[k]? = some (.tick (rho.seatOf ℓ i) u) →
      (⟨.seat ℓ i, p⟩ : P.Object) ∈ D.Run.emitsAt E rho j →
      (⟨.seat ℓ i, p⟩ : P.Object) ∈ D.Run.emitsAt E rho k → j = k ∧ t = u

theorem EmittedUniqueSingleDutyStatement_def :
    EmittedUniqueSingleDutyStatement =
      (∀ {V In : Type} [DecidableEq V] {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P), rho.events.Nodup →
    ∀ (ℓ : P.Label), SingleDuty P ℓ →
    ∀ (i : Fin (P.seats ℓ)) (v : V) (j k : Nat) (t u : Time) (p q : P.Payload),
      rho.events[j]? = some (.tick v t) → rho.events[k]? = some (.tick v u) →
      (⟨.seat ℓ i, p⟩ : P.Object) ∈ D.Run.emitsAt E rho j →
      (⟨.seat ℓ i, q⟩ : P.Object) ∈ D.Run.emitsAt E rho k →
      j = k ∧ p = q) := rfl

theorem EmitUniqueOfEmitOnceStatement_def :
    EmitUniqueOfEmitOnceStatement =
      (∀ {V In : Type} [DecidableEq V] {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P) (ℓ : P.Label), EmitOnceUnder E rho ℓ →
    ∀ (i : Fin (P.seats ℓ)), rho.seatOf ℓ i ∈ rho.honest →
    ∀ (p : P.Payload) (j k : Nat) (t u : Time),
      rho.events[j]? = some (.tick (rho.seatOf ℓ i) t) →
      rho.events[k]? = some (.tick (rho.seatOf ℓ i) u) →
      (⟨.seat ℓ i, p⟩ : P.Object) ∈ D.Run.emitsAt E rho j →
      (⟨.seat ℓ i, p⟩ : P.Object) ∈ D.Run.emitsAt E rho k → j = k ∧ t = u) := rfl

set_option linter.unusedVariables false in
/-- Honest signatures on emitted or handled objects identify one object.
The handler premise is exactly `HooksSound.handles_carries`. -/
def HonestUniqueSingleDutyStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P) (hnodup : rho.events.Nodup)
    (hU : D.UnforgeableSignatures E rho)
    (hhandles : ∀ st o o', P.handles st o o' → o = o' ∨ P.carries o o')
    (ℓ : P.Label) (hD : SingleDuty P ℓ) (i : Fin (P.seats ℓ))
    (hh : rho.seatOf ℓ i ∈ rho.honest) (o₁ o₂ : P.Object)
    (ha₁ : o₁.auth = .seat ℓ i) (ha₂ : o₂.auth = .seat ℓ i)
    (h₁ : (∃ t, D.Run.emits E rho (rho.seatOf ℓ i) o₁ t) ∨
      ∃ j v t, D.Run.handlesAt E rho j v o₁ t)
    (h₂ : (∃ t, D.Run.emits E rho (rho.seatOf ℓ i) o₂ t) ∨
      ∃ j v t, D.Run.handlesAt E rho j v o₂ t),
    o₁ = o₂

set_option linter.unusedVariables false in
theorem HonestUniqueSingleDutyStatement_def :
    HonestUniqueSingleDutyStatement =
    (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
        (E : Generic.Env V) (rho : D.Run V P) (hnodup : rho.events.Nodup)
        (hU : D.UnforgeableSignatures E rho)
        (hhandles : ∀ st o o', P.handles st o o' → o = o' ∨ P.carries o o')
        (ℓ : P.Label) (hD : SingleDuty P ℓ) (i : Fin (P.seats ℓ))
        (hh : rho.seatOf ℓ i ∈ rho.honest) (o₁ o₂ : P.Object)
        (ha₁ : o₁.auth = .seat ℓ i) (ha₂ : o₂.auth = .seat ℓ i)
        (h₁ : (∃ t, D.Run.emits E rho (rho.seatOf ℓ i) o₁ t) ∨
          ∃ j v t, D.Run.handlesAt E rho j v o₁ t)
        (h₂ : (∃ t, D.Run.emits E rho (rho.seatOf ℓ i) o₂ t) ∨
          ∃ j v t, D.Run.handlesAt E rho j v o₂ t),
        o₁ = o₂) := by
  rw [HonestUniqueSingleDutyStatement]

end AvailableChain.Gen.V2.Duty
