module
public import AvailableChainFGSAClaims.Statements.Regimes

@[expose] public section

namespace AvailableChain.FGSA.Run

/-- OUTPUT-DIRECT §1 (V). DC: INTENTIONAL; the pending lease must cover
restored HEADs. Time subtraction and remainder are integer operations. -/
def OutageLengthV (p : Params) (b₀ b₁ : Time) : Prop :=
  b₁ - b₀ + (b₀ - 6 * p.Δ) % (4 * p.Δ) ≤ L p

theorem OutageLengthV_def (p : Params) (b₀ b₁ : Time) :
    OutageLengthV p b₀ b₁ = (b₁ - b₀ + (b₀ - 6 * p.Δ) % (4 * p.Δ) ≤ L p) := rfl

/-- OUTPUT-DIRECT §1. DC: INTENTIONAL; Outage₂ with its budget replaced
by (V), plus full-run acceptance relay and restored participation.
There is no participation premise on [b₀,b₁). No slashing bound is assumed. -/
structure OutageContinuationPrem (p : Params) {In V : Type} (c : AppCodec In)
    [DecidableEq V] [Fintype V] (fast : Bool) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (T b₀ b₁ ΔF : Time) : Prop where
  pre : HealthyPrefix₂ p c E rho b₀ ΔF
  sleepy : ∀ t, 0 ≤ t → t < b₀ →
    (awakeHonestIn E rho (t - p.η) t ∪ Gen.V2.Duty.faulty rho).card <
      2 * (Gen.V2.Duty.awakeHonest E rho t).card
  order : 0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ rho.horizon
  lag : T + (if fast then 4 * p.Δ else L p - 3 * p.Δ) ≤ b₀
  lengthV : OutageLengthV p b₀ b₁
  fastPart : fast = true → ∀ t, 0 ≤ t → t < b₀ →
    (p.n + 1) / 2 ≤ (Gen.V2.Duty.awakeHonest E rho t).card
  sync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF)
  gst : E.t_GST ≤ b₁
  partAfter : ∀ t, b₁ ≤ t → t ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card < (Gen.V2.Duty.awakeHonest E rho t).card

/-- INTENTIONAL FG-SA sleep adaptation: conditional safety after a repairing gate.
This is not SAME as DC stableAsynchronyResilient. -/
def OutageRepairReady (p : Params) {In V : Type} (c : AppCodec In)
    [DecidableEq V] [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (fast : Bool)
    (b₀ b₁ : Time) (B : Block) (y : V) (t : Time) : Prop :=
  y ∈ coveredNodes p E rho fast b₀ ∨
  Block.Preceq B (F_at p c E rho (timeIdx rho t) y) ∨
  ∃ s j, restoredLabel p b₁ + p.k ≤ s ∧
    j < timeIdx rho t ∧
    enabledGateAt p c E rho j y s ∧
    (let st := FGSA.clockPre p (storeAt p c E rho j y)
       (SA.gateTime p.toParams s)
     Block.Compatible B st.base.stableRecord ∨
       ∃ C, SA.Root.confirmationFrom p.toParams
           (eraseFG st.fg.F) (FGSA.actView st) s = some C ∧
         ¬ Block.Preceq C st.base.stableRecord)

/-- INTENTIONAL FG-SA sleep adaptation: continuation outputs require repair readiness.
HEAD and F safety are unchanged. This is not SAME as DC stableAsynchronyResilient. -/
def OutageContinuationConcl (p : Params) {In V : Type} (c : AppCodec In)
    [DecidableEq V] [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (fast : Bool)
    (T b₀ b₁ : Time) : Prop :=
  ∀ x B, confirmedReader p c E rho x T →
    Block.Preceq B (S_at p c E rho (timeIdx rho T) x) →
    (∀ y t, b₀ ≤ t → t ≤ rho.horizon →
      outageConfirmedReader p c E rho fast b₀ b₁ y t →
      OutageRepairReady p c E rho fast b₀ b₁ B y t →
      Block.Compatible B (S_at p c E rho (timeIdx rho t) y) ∧
      Block.Compatible B
        (V2.D.outputAt E rho (fgsaInterface p c).stable y t) ∧
      Block.Compatible B
        (V2.D.outputAt E rho (fgsaInterface p c).confirmed y t) ∧
      (y ∈ coveredNodes p E rho fast b₀ →
        Block.Preceq B (S_at p c E rho (timeIdx rho t) y) ∧
        Block.Preceq B
          (V2.D.outputAt E rho (fgsaInterface p c).stable y t) ∧
        Block.Preceq B
          (V2.D.outputAt E rho (fgsaInterface p c).confirmed y t))) ∧
    (∀ y t o H, b₀ ≤ t → t ≤ rho.horizon →
      outageHeadReader p E rho fast b₀ b₁ y t →
      V2.D.Run.emits E rho y o t →
      HeadTargetAtEmission p c E rho y o t H →
      Block.Compatible B H) ∧
    (∀ y t, y ∈ rho.honest → b₀ ≤ t → t ≤ rho.horizon →
      Block.Compatible B (F_at p c E rho (timeIdx rho t) y))

structure OutageContinuationSleepPrem (p : Params) {In V : Type} (c : AppCodec In)
    [DecidableEq V] [Fintype V] (fast : Bool) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (T b₀ b₁ ΔF : Time) : Prop
    extends OutageContinuationPrem p c fast E rho T b₀ b₁ ΔF where
  sleepPre : HealthyPrefixSleep₂ p c E rho b₀ ΔF
  joinedSleepy : ∀ t, 0 ≤ t → t < b₀ →
    (sleepyBad p E rho t).card < 2 * (joinedHonest p E rho t).card
  joinedFastPart : fast = true → ∀ t, 0 ≤ t → t < b₀ →
    (p.n + 1) / 2 ≤ (joinedHonest p E rho t).card
  protection : OutageE p E rho fast b₀ b₁
  joinedPartAfter : ∀ t, OutageEnd p (restoredLabel p b₁) ≤ t →
    t ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho t).card
  sleepyAfter : ∀ t, OutageEnd p (restoredLabel p b₁) ≤ t →
    t ≤ rho.horizon →
    (sleepyBad p E rho t).card < 2 * (joinedHonest p E rho t).card

end AvailableChain.FGSA.Run
end
