module
public import AvailableChainEngineV2.Conditions.Schedule

@[expose] public section

/-! G12 (GLY r3.16:199–201, 728–732): one signed object per seat and label.
F1.2 uses the emission form, including equality of event indices.
T7.8 uses the emitted-or-handled form after row-pool provenance.
The receipt window is a premise of the users, not of these statements. -/

-- Register the required Engine namespace without a KitV2 import.
namespace AvailableChain.V2.Engine
end AvailableChain.V2.Engine

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

namespace AvailableChain.Gen.V2

set_option linter.unusedVariables false in
/-- A fixed seat and label have one payload at one tick index.
Only the schedule's no-duplicate-events field is needed. -/
def EmittedUniquePerLabelStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P) (hnodup : rho.events.Nodup)
    (v : V) (ℓ : P.Label) (i : Fin (P.seats ℓ))
    (j₁ j₂ : Nat) (t₁ t₂ : Time) (o₁ o₂ : P.Object)
    (he₁ : rho.events[j₁]? = some (.tick v t₁))
    (he₂ : rho.events[j₂]? = some (.tick v t₂))
    (ho₁ : o₁ ∈ Run.emitsAt E rho j₁)
    (ho₂ : o₂ ∈ Run.emitsAt E rho j₂)
    (ha₁ : o₁.auth = .seat ℓ i) (ha₂ : o₂.auth = .seat ℓ i),
    j₁ = j₂ ∧ o₁ = o₂

set_option linter.unusedVariables false in
theorem EmittedUniquePerLabelStatement_def :
    EmittedUniquePerLabelStatement =
    (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
        (E : Generic.Env V) (rho : Run V P) (hnodup : rho.events.Nodup)
        (v : V) (ℓ : P.Label) (i : Fin (P.seats ℓ))
        (j₁ j₂ : Nat) (t₁ t₂ : Time) (o₁ o₂ : P.Object)
        (he₁ : rho.events[j₁]? = some (.tick v t₁))
        (he₂ : rho.events[j₂]? = some (.tick v t₂))
        (ho₁ : o₁ ∈ Run.emitsAt E rho j₁)
        (ho₂ : o₂ ∈ Run.emitsAt E rho j₂)
        (ha₁ : o₁.auth = .seat ℓ i) (ha₂ : o₂.auth = .seat ℓ i),
        j₁ = j₂ ∧ o₁ = o₂) := by
  rw [EmittedUniquePerLabelStatement]

set_option linter.unusedVariables false in
/-- Honest signatures on emitted or handled objects identify one object.
The handler premise is exactly `HooksSound.handles_carries`. -/
def HonestUniquePerLabelStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P) (hnodup : rho.events.Nodup)
    (hU : UnforgeableSignatures E rho)
    (hhandles : ∀ st o o', P.handles st o o' → o = o' ∨ P.carries o o')
    (ℓ : P.Label) (i : Fin (P.seats ℓ))
    (hh : rho.seatOf ℓ i ∈ rho.honest) (o₁ o₂ : P.Object)
    (ha₁ : o₁.auth = .seat ℓ i) (ha₂ : o₂.auth = .seat ℓ i)
    (h₁ : (∃ t, Run.emits E rho (rho.seatOf ℓ i) o₁ t) ∨
      ∃ j v t, Run.handlesAt E rho j v o₁ t)
    (h₂ : (∃ t, Run.emits E rho (rho.seatOf ℓ i) o₂ t) ∨
      ∃ j v t, Run.handlesAt E rho j v o₂ t),
    o₁ = o₂

set_option linter.unusedVariables false in
theorem HonestUniquePerLabelStatement_def :
    HonestUniquePerLabelStatement =
    (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
        (E : Generic.Env V) (rho : Run V P) (hnodup : rho.events.Nodup)
        (hU : UnforgeableSignatures E rho)
        (hhandles : ∀ st o o', P.handles st o o' → o = o' ∨ P.carries o o')
        (ℓ : P.Label) (i : Fin (P.seats ℓ))
        (hh : rho.seatOf ℓ i ∈ rho.honest) (o₁ o₂ : P.Object)
        (ha₁ : o₁.auth = .seat ℓ i) (ha₂ : o₂.auth = .seat ℓ i)
        (h₁ : (∃ t, Run.emits E rho (rho.seatOf ℓ i) o₁ t) ∨
          ∃ j v t, Run.handlesAt E rho j v o₁ t)
        (h₂ : (∃ t, Run.emits E rho (rho.seatOf ℓ i) o₂ t) ∨
          ∃ j v t, Run.handlesAt E rho j v o₂ t),
        o₁ = o₂) := by
  rw [HonestUniquePerLabelStatement]

end AvailableChain.Gen.V2
