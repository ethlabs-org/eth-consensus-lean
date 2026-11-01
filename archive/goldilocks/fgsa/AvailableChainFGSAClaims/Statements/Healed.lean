module
-- shake: keep-all (F0.5 imports kept; S4.4a adds BoundsW for LivenessBoundW and B_HF)
public import AvailableChainFGSAClaims.Statements.Regimes
public import AvailableChainFGSAClaims.Statements.BoundsW
public import AvailableChainFGSAClaims.Statements.ChannelProps
public import AvailableChainFGSAClaims.Statements.Reads
public import AvailableChainFGSAClaims.Statements.Witness -- shake: keep (F0.8b append point)
public import AvailableChainFGSAClaims.Statements.Counts
public import AvailableChainFGSARun.Statements.Interface
public import AvailableChainGeneric.Statements.Pure.Props

@[expose] public section

/-! F0.5: HEALED through the GLY property kernel (P3 §4.6, D43, D61).
F0.8b adds the AC-output Props and healing input below these declarations. -/

namespace AvailableChain.FGSA.Run

variable (p : Params) {In : Type} (c : AppCodec In)
    {V : Type} [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Post-gate cut at gate times; inclusive cut otherwise
(21 H.22:2985–2994; 22 §1:167–176). -/
def healStart (t : Time) : Nat :=
  if isGateTime p t then afterTicksIdx rho t else timeIdx rho t

/-- All event-prefix states from the cut through the run's last state
(21 H.22:2988–2991; 22 §1:170–173). -/
def HealSuffix (t : Time) (i : Nat) : Prop :=
  healStart p c rho t ≤ i ∧ i ≤ rho.events.length

/-- HEALED (21 H.22:2996–2999; 22 §1:178–181), with the Gen statements
`Gen.Pure.CompatOn`, `MonoOn`, `BelowOn`, and `ServedOn` from
`AvailableChainGeneric.Statements.Pure.Props` (GLY property kernel).

Compatibility: 21:2996–2997; 22:178–179. P3 D43/D61 uses the cross-time form.
Monotonicity: 21:2997; 22:179. The index is an event prefix.
F below S: 21:2998; 22:180. Both reads use the same event prefix.
Proposal service: 21:2998–2999; 22:180–181. The gate read is after all ticks;
the gate must be within the finite run horizon (P3 §4.6). -/
def Healed (t : Time) : Prop :=
  ScopedCompat (confirmedReaderIdx p c E rho) (S_at p c E rho) (HealSuffix p c rho t) ∧
  ScopedMono (confirmedReaderIdx p c E rho) (S_at p c E rho) (HealSuffix p c rho t) ∧
  (∀ i x y, HealSuffix p c rho t i → x ∈ rho.honest →
    confirmedReaderIdx p c E rho y i →
    Block.Preceq (F_at p c E rho i x) (S_at p c E rho i y)) ∧
  (∀ s B, t ≤ V2.D.proposalTime (fgsaInterface p c) s →
    SA.gateTime p.toParams s ≤ rho.horizon →
    HonestProposal E rho (fgsaInterface p c) s B →
    ScopedServed (confirmedReader p c E rho)
      (fun u x => (fgsaInterface p c).stable (afterTicks E rho u x)) B
      (· = SA.gateTime p.toParams s))


open AvailableChain.SimplexFG
open Gen.Pure

/-- H2.A [joint] (21:3096–3102), P3 A.9.
HEAD consumers: F8, Q0, QF4 S2. Output consumers: healing and finality composition.
The output clause needs its cut within the horizon (ruling B31; 21:3289–3291). -/
def H2A (w : HealingWitness) : Prop := ∀ y r K, y ∈ rho.honest →
  actionSourceFG p c E rho y r = some (some K) → high p w K →
  (∀ x i H, headReader p E rho x i (SA.voteTime p.toParams i) →
    r * p.R + 1 ≤ i →
    headAtLabel p c E rho x i = some H → Block.Preceq (eraseFG K) H) ∧
  (∀ i x, confirmedReaderIdx p c E rho x i →
    p.actionTime r + 4 * p.Δ ≤ rho.horizon →
    HealSuffix p c rho (p.actionTime r + 4 * p.Δ) i →
    Block.Preceq (eraseFG K) (S_at p c E rho i x))
/-- H2′ [joint] (21:3104–3107), P3 A.9.
Consumers: F6, F8, QF2 Q1, QF4 S1/S2 and Q0, FL-T7. -/
def H2Prime (w : HealingWitness) : Prop := ∀ v Q,
  HonestProposal E rho (fgsaInterface p c) v Q → w.sStar + 2 ≤ v →
  ∀ x i H, headReader p E rho x i (SA.voteTime p.toParams i) →
    v + 1 ≤ i → headAtLabel p c E rho x i = some H →
    Block.Preceq Q H
/-- H3 [joint] (21:3109–3114), P3 A.9.
HEAD consumers: FF1, F6, F8, Q0, QF4 S2. Source consumer: QF4 S1.
Also supplies TExact (01:143–149) to FF1, F1 and F3. -/
def H3 (w : HealingWitness) : Prop := ∀ v Q,
  HonestProposal E rho (fgsaInterface p c) v Q → w.sStar + 2 ≤ v → ExactService p c E rho v Q
/-- H4 (21:3116–3123), P3 A.9. Consumers: F6, F8, FF5, FF6 and HEALED.
Uses the Gen property kernel, including cross-time compatibility. -/
def H4 (w : HealingWitness) : Prop :=
  (∀ x ∈ rho.honest, (fgsaInterface p c).stable (afterTicks E rho (tstar p w) x) = w.QStar) ∧
  ScopedCompat (confirmedReaderIdx p c E rho) (S_at p c E rho) (HealSuffix p c rho (tstar p w)) ∧
  ScopedMono (confirmedReaderIdx p c E rho) (S_at p c E rho) (HealSuffix p c rho (tstar p w)) ∧
  (∀ i x y, HealSuffix p c rho (tstar p w) i → x ∈ rho.honest →
    confirmedReaderIdx p c E rho y i →
    Block.Preceq (F_at p c E rho i x) (S_at p c E rho i y))
/-- H5 (21:3125–3132), P3 A.9. Consumer: Q0 in QF2 and QF4.
No fast threshold or passed-guard premise is imposed on the raw result.
The output clause needs its cut within the horizon (ruling B31; 21:3321). -/
def H5RawTransfer (w : HealingWitness) : Prop := ∀ y j C,
  y ∈ rho.honest → w.sStar ≤ j → gateResult p c E rho y j = some (some C) →
  (∀ x nd, x ∈ rho.honest → postClock E rho x (SA.releaseTime p.toParams j) = some nd →
    ∀ lease ∈ nd.st.base.obligations, nd.st.base.now < lease.2.2 → Block.Compatible lease.1 C) ∧
  (∀ x i H, headReader p E rho x i (SA.voteTime p.toParams i) →
    j + 1 ≤ i → headAtLabel p c E rho x i = some H →
    Block.Preceq C H) ∧
  (∀ v Q, j + 2 ≤ v → HonestProposal E rho (fgsaInterface p c) v Q → Block.Preceq C Q.parent) ∧
  (∀ i x, confirmedReaderIdx p c E rho x i →
    SA.gateTime p.toParams j + 4 * p.Δ ≤ rho.horizon →
    HealSuffix p c rho (SA.gateTime p.toParams j + 4 * p.Δ) i → Block.Preceq C (S_at p c E rho i x))
/-- H6 (21:3134–3141), P3 A.9. Consumer: Q0 in QF2 and QF4.
A unanimous synchronous batch gives a raw result, guard, fast write and lease. -/
def H6GateService (w : HealingWitness) : Prop := ∀ j D,
  w.sStar ≤ j → recoveryStart p E ≤ SA.voteTime p.toParams j →
  SA.gateTime p.toParams j ≤ rho.horizon → D ≠ .genesis →
  (∀ x ∈ rho.honest, ∃ H, headAtLabel p c E rho x j = some H ∧ Block.Preceq D H) →
  (∀ x st, x ∈ rho.honest → gateIn p c E rho x j = some st → Block.Preceq (eraseFG st.fg.F) D) →
  ∀ x ∈ rho.honest,
    (∃ C, gateResult p c E rho x j = some (some C) ∧ Block.Preceq D C) ∧
    (∃ i, IsGateTick p c rho i x j ∧ gatePassedAt p c E rho i) ∧
    (∃ nd d, postClock E rho x (SA.gateTime p.toParams j) = some nd ∧
      D ∈ (fastWriteAt nd.st j).getD [] ∧ leaseOf nd.st D = some d ∧
      SA.gateTime p.toParams j + L p ≤ d ∧ SA.gateTime p.toParams j < d)

/-- T-stream part (21:3057–3084), P3 A.6. Consumers: 22 FF1–FF4 and kernel.
DC: INTENTIONAL bound row delay; SAME block and HEAD services. -/
structure HealT (w : HealingWitness) (ΔF : Time) : Prop where
  h1 : THigh p c E rho w
  h2 : TCarrier p c E rho w
  rows : TRows p c E rho ΔF
/-- AC-output part (21:3086–3141), P3 A.9. Consumers: composition and Q0. -/
structure HealAC (w : HealingWitness) : Prop where
  /-- H2.A [joint]: F8, Q0, QF4 S2 (21:3096–3102). -/
  h2A : H2A p c E rho w
  /-- H2′ [joint]: F6, F8, QF2 Q1, QF4 S1/S2, FL-T7 (21:3104–3107). -/
  h2' : H2Prime p c E rho w
  /-- H3 [joint]: FF1, F6, F8, Q0, QF4 S1/S2 (21:3109–3114). -/
  h3 : H3 p c E rho w
  h4 : H4 p c E rho w
  h5 : H5RawTransfer p c E rho w
  h6 : H6GateService p c E rho w

/-- HEALING_INPUT (21 H.22:2984–3172; 22 §1:166–354), P3 §4.6.
Consumers: finality kernel, QF2, QF4, FF5–FF7. Four parts share the witness and reads:
(1) wit is full H0, (2) t is the T-stream, (3) ac is AC-output service,
(4) FG foundations IF.1–IF.4 are proved separately by F1, not extra fields.
HEALED remains an explicit field; composition services remain separate.
Spec map (8ef4ed3b): 2044 → healed; 2055 → wit; 2065 → t.h1;
2072 → t.h2; 2076 → t.rows; 2090 → ac.h2A; 2095 → ac.h2';
2099 → ac.h3; 2104 → ac.h4; 2109 → ac.h5; 2118 → ac.h6;
2128–2132 → F1 foundations; 2134–2138 → the H-time statements below.
Full wit uses ResetArrivalFullStatement (H.18 horizon), not reset-only arrival.
DC: INTENTIONAL family delivery uses ΔF; SA clocks stay unchanged.
Every caller supplies the row delay explicitly. -/
structure HealingInput (w : HealingWitness) (ΔF : Time) : Prop where
  healed : Healed p c E rho (tstar p w)
  wit : H0 p c E rho w
  t : HealT p c E rho w ΔF
  ac : HealAC p c E rho w

/-- H-time (21:3152–3170; 22:334–352), P3 §4.6/A.9.
Consumers: healing and finality claims. Both links of the chained bound remain.
DC: INTENTIONAL family delivery uses ΔF; SA clocks stay unchanged. -/
def HTimeStatement (G ΔF : Time) : Prop := p.δt = 2 * p.R →
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
    recoveryStart p E + B_HF p ΔF G ≤ rho.horizon →
    ∃ w, HealingInput p c E rho w ΔF ∧
      tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ ∧
      p.actionTime w.rStar + Γ p G + 4 * p.Δ < recoveryStart p E + B_HF p ΔF G

theorem HTimeStatement_def (G ΔF : Time) :
    HTimeStatement p G ΔF =
  (p.δt = 2 * p.R →
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
    recoveryStart p E + B_HF p ΔF G ≤ rho.horizon →
    ∃ w, HealingInput p c E rho w ΔF ∧
      tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ ∧
      p.actionTime w.rStar + Γ p G + 4 * p.Δ < recoveryStart p E + B_HF p ΔF G) := by
  rfl

-- equation export required by BUILD §7.2 B3a (post-freeze additive _def batch)
omit [DecidableEq V] in
theorem HealSuffix_def (t : Time) (i : Nat) :
    HealSuffix p c rho t i = (healStart p c rho t ≤ i ∧ i ≤ rho.events.length) := rfl

-- equation export required by BUILD §7.2 B3a (post-freeze additive _def batch)
omit [DecidableEq V] in
theorem healStart_def (t : Time) :
    healStart p c rho t =
      (if isGateTime p t then afterTicksIdx rho t else timeIdx rho t) := rfl

end AvailableChain.FGSA.Run
end
