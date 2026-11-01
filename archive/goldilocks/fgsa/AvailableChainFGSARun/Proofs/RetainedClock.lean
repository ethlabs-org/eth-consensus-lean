module
public import AvailableChainFGSARun.Statements.Acceptance
public import AvailableChainKitV2.DutyEngineClock -- shake: keep (re-export)
public import AvailableChainGeneric.Proofs.V2.Duty.Receipt

public section

/-! Relay timeliness uses the exact wake clock and public admission times. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.V2 (Event)
open AvailableChain.V2.D AvailableChain.V2.D.Engine
open AvailableChain.Gen.V2.Duty

variable {V : Type} [DecidableEq V] {In : Type}

/-- Relay admission is timely with exact wake clocks and public action times. -/
theorem timely_of_relay_retained {p : Params} {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {Timely : (fgsa p c).State → (fgsa p c).Object → Prop}
    (C : Gen.V2.Duty.TimelyClock (fgsa p c) Timely)
    (hAS : Gen.V2.Duty.AdmitSound (fgsa p c) C) (hS : ScheduleWellFormed E rho)
    (R : RestoreTimeLaw C.clock)
    (hpubAct : ∀ o, V2.PublicTime E (C.actTime o))
    (v : V) (i : Nat) (o : (fgsa p c).Object) (t : Time)
    (hacc : V2.D.Run.acceptsAt E rho i v o t) :
    C.actTime o ≤ Gen.V2.Duty.pubFloor E t :=
  Gen.V2.Duty.timely_of_relay_public_actTime E rho C hAS hS R hpubAct v i o t hacc

omit [DecidableEq V] in
/-- FG-SA admission thresholds are public multiples of 4Δ, including zero. -/
theorem fgsa_admissionTime_public (p : Params) (E : Generic.Env V) (hΔ : E.Δ = p.Δ)
    (o : Obj p) : V2.PublicTime E (fgsaAdmissionTime p o) := by
  have hslot (s : Slot) : V2.PublicTime E (4 * p.Δ * (s : Int)) := by
    refine ⟨4 * s, ?_⟩
    rw [hΔ]
    push_cast
    ring
  have hz : V2.PublicTime E 0 := ⟨0, by simp⟩
  unfold fgsaAdmissionTime
  cases o.auth with
  | none => exact hz
  | seat label seat =>
    cases label with
    | prop s => exact hslot s
    | base label =>
      cases label with
      | head s => exact hslot s
      | fg => exact hz

end AvailableChain.FGSA.Run

end
