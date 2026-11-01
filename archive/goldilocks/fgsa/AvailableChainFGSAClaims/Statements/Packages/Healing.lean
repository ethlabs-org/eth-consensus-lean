module
public import AvailableChainFGSAClaims.Statements.ComposeStmt

@[expose] public section

namespace AvailableChain.FGSA.Run
open Gen.Pure

/-- Healing time point (21 H.3–H.10), P3 §4.4.2 D41. -/
structure PtU where
  u : Time
/-- Full reset witness point (21 H.22:3044–3055), P3 §4.4.2 D41. -/
structure PtW where
  w : HealingWitness
/-- Frontier point (21 HG.1:1333–1350), P3 §4.4.2 D41. -/
structure PtM where
  m : Nat
/-- Round point (22 §1), P3 §4.4.2 D41. -/
structure PtR where
  r : Nat
/-- Attempt point (21 H.10:1263–1279), P3 §4.4.2 D41. -/
structure PtK where
  k : AttemptKey

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V] [Fintype V]

/-- Family (2) without a reset witness (21 §2), P3 §4.4.2.
Consumers: pre-reset channels.
DC: INTENTIONAL family delivery uses ΔF; SA clocks stay unchanged. -/
structure HealingPrem {Pt : Type} (G ΔF : Time)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (_pt : Pt) : Prop where
  set : HealingSet p c E rho G ΔF
  bound : LivenessBoundW p ΔF
/-- Family (2), full H0 point (21:3044–3055), P3 §4.4.2.
Consumers: post-reset channels. Full H0 uses ResetArrivalFullStatement.
DC: INTENTIONAL family delivery uses ΔF; SA clocks stay unchanged. -/
structure HealingWitnessPrem (G ΔF : Time)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtW) : Prop
    extends HealingPrem p c G ΔF E rho pt where
  h0 : H0 p c E rho pt.w
/-- H-time horizon (21:3152–3170), P3 §4.4.2. Consumer: HTimeStatement.
DC: INTENTIONAL family delivery uses ΔF; SA clocks stay unchanged. -/
structure HealingTimePrem (G ΔF : Time)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit) : Prop
    extends HealingPrem p c G ΔF E rho pt where
  hhor : recoveryStart p E + B_HF p ΔF G ≤ rho.horizon
/-- Reset-only horizon (21 H.11:1572–1595), P3 A.10 with lead ruling.
Consumer: ResetArrivalStatement. Does not promise Q*.
DC: INTENTIONAL family delivery uses ΔF; SA clocks stay unchanged. -/
structure ResetArrivalPrem (G ΔF : Time)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit) : Prop
    extends HealingPrem p c G ΔF E rho pt where
  hhor : recoveryStart p E + B'_resetF p ΔF G ≤ rho.horizon
/-- Full-H0 horizon (21 H.18:2868–2876), lead ruling 2026-09-30.
Consumer: ResetArrivalFullStatement.
DC: INTENTIONAL family delivery uses ΔF; SA clocks stay unchanged. -/
structure ResetArrivalFullPrem (G ΔF : Time)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit) : Prop
    extends HealingPrem p c G ΔF E rho pt where
  hhor : recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon
/-- Joined kernel (00:1119–1134), P3 A.10 D44.
Consumer: F0.6b kernel claim. Located after PtR to preserve module order.
The input and start use the same witness; the horizon includes carrier receipt.
DC: INTENTIONAL family delivery uses ΔF; SA clocks stay unchanged. -/
structure KernelJoinedPrem (G ΔF : Time)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtR) : Prop where
  set : Recovery₂ p c E rho G ΔF
  bound : LivenessBoundW p ΔF
  window : FGoodE_W (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c))
    p.R (kappaF p ΔF) pt.r
  start : ∃ w, HealingInput p c E rho w ΔF ∧ tstar p w ≤ ↑pt.r * P p
  hhor : kernelDeadlineW p ΔF (pt.r + 2) ≤ rho.horizon


/-- Attempt point premises (21 H.10:1263–1279), P3 §4.4.2/A.10.
Consumer: progress-attempt claim. Blueprint 21:161–164 requires the full
finite-run budget after the actual start event (H.10:1426–1498).
DC: INTENTIONAL family delivery uses ΔF; SA clocks stay unchanged. -/
structure HealingAttemptPrem (G ΔF : Time)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtK) : Prop
    extends HealingPrem p c G ΔF E rho pt where
  valid : AttemptValid p c E rho pt.k
  hhor : ∃ ev, rho.events[pt.k.start]? = some ev ∧
    ev.time + attemptBudget p G pt.k ≤ rho.horizon

/-- DC: INTENTIONAL FG healing package with its finite horizon. -/
structure HealingInputPrem (G ΔF : Time)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtW) : Prop
    extends HealingWitnessPrem p c G ΔF E rho pt where
  hhor : tstar p pt.w ≤ rho.horizon

/-- DC: INTENTIONAL FG healing package with its finite horizon. -/
structure RenewedPromotionPrem (G ΔF : Time)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtR) : Prop
    extends HealingPrem p c G ΔF E rho pt where
  hhor : p.actionTime pt.r + 2 * P p + Γ p G - 4 * p.Δ ≤ rho.horizon

end AvailableChain.FGSA.Run
end
