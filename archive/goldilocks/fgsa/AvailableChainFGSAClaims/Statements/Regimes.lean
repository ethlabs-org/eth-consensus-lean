module
public import AvailableChainFGSAClaims.Statements.Join
public import AvailableChainFGSARun.Statements.Roots
public import AvailableChainGeneric.Statements.V2.Duty.DeliveryBy

@[expose] public section

namespace AvailableChain.FGSA.Run

open Gen.Pure
open Gen.V2.Duty (faulty awakeHonest HonestSlot)

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V] [Fintype V]

structure Base₂ (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : Prop where
  valid : V2.D.ExecutionValid E rho
  linked : V2.D.Linked (fgsaFamilies p c).linked rho
  cstar : V2.D.CStar (fgsaFamilies p c).fresh rho
  restartsAtWakes : V2.D.RestartsAtWakes E rho
  delta : E.Δ = p.Δ
  /-- DECISION P23-A: delivered, held, and honest emitted bodies and their ancestors.
  A global form over all values is false: root is a free field. -/
  receiptIdealization : NamedReceiptRootCollisionFree p c E rho

omit [Fintype V] in
/-- DECISION P23-A: preserve the old safety projection from the single receipt field. -/
theorem Base₂.idealization {p : Params} {c : AppCodec In} {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} (h : Base₂ p c E rho) :
    NamedRootCollisionFree p c E rho := by
  have trans {A B C : NamedProposal p.n}
      (hAB : NamedProposal.Preceq A B) (hBC : NamedProposal.Preceq B C) :
      NamedProposal.Preceq A C := by
    induction C with
    | genesis =>
      have he : B = .genesis := by
        simpa [NamedProposal.Preceq, NamedProposal.preceq] using hBC
      simpa [he] using hAB
    | node P s r x raw sup rows ih =>
      simp only [NamedProposal.Preceq, NamedProposal.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hBC ⊢
      rcases hBC with rfl | hp
      · simpa only [NamedProposal.Preceq, NamedProposal.preceq, Bool.or_eq_true,
          decide_eq_true_eq] using hAB
      · exact Or.inr (ih hp)
  have ancestor {A B : NamedProposal p.n} (hB : NamedProposalInRun p c E rho B)
      (hAB : NamedProposal.Preceq A B) : NamedProposalInRun p c E rho A := by
    obtain ⟨C, hC, hBC⟩ := hB
    exact ⟨C, hC, trans hAB hBC⟩
  constructor
  intro B C hB hC A D hA hD he
  exact h.receiptIdealization A D
    (Or.inl (hA.elim (ancestor hB) (ancestor hC)))
    (Or.inl (hD.elim (ancestor hB) (ancestor hC))) he

/-- Per-object delivery regime.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
structure HealthyPrefix₂ (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (ΔF : Time := E.Δ) : Prop where
  base : Base₂ p c E rho
  cut : 0 ≤ b₀ ∧ b₀ ≤ rho.horizon
  healthy : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (fgsaDelay E.Δ ΔF) b₀
  deltaF : E.Δ ≤ ΔF
  partBefore : ∀ t : Time, 0 ≤ t → t < b₀ → (faulty rho).card < (awakeHonest E rho t).card

/-- Per-object delivery regime.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
structure CleanPrefix₂ (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (ΔF : Time := E.Δ) : Prop extends HealthyPrefix₂ p c E rho b₀ ΔF where
  partAt : (faulty rho).card < (awakeHonest E rho b₀).card

/-- The blueprint cut has no participation premise at the cut and no quorum field.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
abbrev CleanCut₂ (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (ΔF : Time := E.Δ) : Prop :=
  HealthyPrefix₂ p c E rho b₀ ΔF

/-- Per-object delivery regime.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
structure Clean₂ (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time := E.Δ) : Prop where
  pre : CleanPrefix₂ p c E rho rho.horizon ΔF
  gst : E.t_GST = 0

/-- Recovery has no delta-ratio premise. `gap` has the shape of DC SingleProposerRecurrence
from GST, over windows that end within the horizon; it has the role of DC RecoveryRegime.recurrence.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
structure Recovery₂ (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G : Time)
    (ΔF : Time := E.Δ) : Prop where
  sync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF)
  deltaF : E.Δ ≤ ΔF
  gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
    ∃ s, t < V2.D.proposalTime (fgsaInterface p c) s ∧
      V2.D.proposalTime (fgsaInterface p c) s ≤ t + G ∧
      HonestSlot rho (fgsaInterface p c) s
  base : Base₂ p c E rho
  fault : (faulty rho).card ≤ (p.n - 1) / 3
  awake : ∀ v ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon → E.awake v t = true
  gapPos : 4 * p.Δ ≤ G

structure HealthyPrefixSleep₂ (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (ΔF : Time := E.Δ) : Prop extends HealthyPrefix₂ p c E rho b₀ ΔF where
  joinedPartBefore : ∀ t : Time, 0 ≤ t → t < b₀ →
    (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho t).card

structure CleanPrefixSleep₂ (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (ΔF : Time := E.Δ) : Prop extends CleanPrefix₂ p c E rho b₀ ΔF where
  sleepPre : HealthyPrefixSleep₂ p c E rho b₀ ΔF
  joinedPartAt : (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho b₀).card

structure CleanSleep₂ (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time := E.Δ) : Prop extends Clean₂ p c E rho ΔF where
  sleepPre : CleanPrefixSleep₂ p c E rho rho.horizon ΔF

abbrev BaseSet (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : Prop := Base₂ p c E rho
abbrev CleanSet (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time := E.Δ) : Prop := CleanSleep₂ p c E rho ΔF
abbrev CleanCutSet (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (ΔF : Time := E.Δ) : Prop :=
  HealthyPrefixSleep₂ p c E rho b₀ ΔF
abbrev CleanPrefixSet (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (ΔF : Time := E.Δ) : Prop :=
  CleanPrefixSleep₂ p c E rho b₀ ΔF


/-- Awake proposer recurrence from t₀: every window (t, t + G] with t₀ ≤ t that ends within
the horizon holds an honest slot whose proposer is awake at its proposal time.
DC b241081 Generic/Conditions.lean:207–211 SingleProposerRecurrence: SAME role; INTENTIONAL: the
awake condition (FG-SA suppresses the duties of sleeping nodes). Consumers: CleanGrowthClaim and
the weak-continuation liveness companion. -/
def AwakeProposerRecurrenceFrom (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (t₀ G : Time) : Prop :=
  ∀ t, t₀ ≤ t → t + G ≤ rho.horizon →
    ∃ s, t < V2.D.proposalTime (fgsaInterface p c) s ∧
      V2.D.proposalTime (fgsaInterface p c) s ≤ t + G ∧
      HonestSlot rho (fgsaInterface p c) s ∧
      joinedAt p E rho (V2.D.proposerOf rho (fgsaInterface p c) s) s
        (V2.D.proposalTime (fgsaInterface p c) s)

structure RecoverySleep₂ (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G : Time) (ΔF : Time := E.Δ) : Prop extends Recovery₂ p c E rho G ΔF where
  suffixNoRestart : ∀ v ∈ rho.honest,
    V2.D.NoRestartOn rho v E.t_GST (rho.horizon + 1)
  joinedGap : AwakeProposerRecurrenceFrom p c E rho (recoveryStart p E) G

def RecoveryReadinessClaim (p : Params) : Prop :=
  ∀ {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G ΔF t : Time),
    RecoverySleep₂ p c E rho G ΔF →
    recoveryStart p E ≤ t → t ≤ rho.horizon →
    ∀ v ∈ rho.honest,
      joinedAt p E rho v (slotAt p t) t ∧ caughtUpAt p c E rho v t

/-- DC: INTENTIONAL family delivery with an explicit row bound.
Every caller supplies the row delay explicitly.
HealingPrem carries LivenessBoundW for the active healing claims. -/
abbrev HealingSet (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G : Time)
    (ΔF : Time) : Prop :=
  RecoverySleep₂ p c E rho G ΔF

/-- Final outage fields for G-F0a. Participation is strict before the cut;
the sleep witness is in `outWin`. -/
structure Outage₂ (fast : Bool) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (T b₀ b₁ : Time) (ΔF : Time := E.Δ) : Prop where
  pre : HealthyPrefix₂ p c E rho b₀ ΔF
  sleepy : ∀ t, 0 ≤ t → t < b₀ →
    (awakeHonestIn E rho (t - p.η) t ∪ faulty rho).card < 2 * (awakeHonest E rho t).card
  order : 0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ rho.horizon
  lag : T + (if fast then 4 * p.Δ else L p - 3 * p.Δ) ≤ b₀
  budget : b₁ - b₀ ≤ min p.η (L p)
  fastPart : fast = true → ∀ t, 0 ≤ t → t < b₀ →
    (p.n + 1) / 2 ≤ (awakeHonest E rho t).card

structure OutageSleep₂ (fast : Bool) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (T b₀ b₁ : Time) (ΔF : Time := E.Δ) : Prop
    extends Outage₂ p c fast E rho T b₀ b₁ ΔF where
  sleepPre : HealthyPrefixSleep₂ p c E rho b₀ ΔF
  joinedSleepy : ∀ t, 0 ≤ t → t < b₀ →
    (sleepyBad p E rho t).card < 2 * (joinedHonest p E rho t).card
  joinedFastPart : fast = true → ∀ t, 0 ≤ t → t < b₀ →
    (p.n + 1) / 2 ≤ (joinedHonest p E rho t).card
  protection : OutageE1 p E rho fast b₀ b₁

abbrev OutageSet (fast : Bool) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (T b₀ b₁ : Time) (ΔF : Time := E.Δ) : Prop := OutageSleep₂ p c fast E rho T b₀ b₁ ΔF

end AvailableChain.FGSA.Run
end
