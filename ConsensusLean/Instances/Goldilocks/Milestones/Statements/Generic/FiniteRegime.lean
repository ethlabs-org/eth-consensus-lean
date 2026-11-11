module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.CorrectLocal
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Truncation

@[expose] public section

/-! # Finite regimes for actual-cut consumers

All implication contracts below are UNPROVED suppliers, not facts obtained from
`ACCorrectLocal`. In particular neither trace retention nor honesty truncation supplies
the all-time fault counts in `SleepyRunAt` or `HealthyRunAt`. Explicit-time engine reads
need separate suppliers; these contracts only read at actual trace cuts.
-/

namespace Consensus.Goldilocks.Generic

variable {P : Params} {A : NodeAC P}

/-- The healthy transport's service, with awake and fault bounds only through `b`.
Service retains its event-delivery meaning; no future awake schedule is required. -/
def HealthyPrefix (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (ΔF g b : Time) : Prop :=
  0 ≤ b ∧ tr.GSTRunAt H ΔF g ∧
    (∀ y t, max g 0 ≤ t → t ≤ b → y ∈ H t → tr.awake y t) ∧
    (∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1)

/-- Service on the retained event trace, not service for arbitrary future calls. -/
def PrefixService (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (g ΔF b : Time) : Prop :=
  Service (tr.upTo b) H g ΔF b

variable (A) (sg : A.Msg → Fin P.n)

/-- UNPROVED restriction to an earlier consumer horizon, including the clamped fault charge. -/
def sleepyPrefix_restrict : Prop :=
  ∀ (tr : RunTrace A) H ΔF look b d,
    Antitone H → 0 ≤ d → d ≤ b →
    tr.SleepyPrefixAt H ΔF look b → tr.SleepyPrefixAt H ΔF look d

/-- UNPROVED trace-prefix transport, retaining the finite, clamped count predicate. -/
def sleepyPrefix_upTo : Prop :=
  ∀ proposer dg H tr ΔF look b,
    Growing.LocalRun proposer dg H sg tr →
    tr.SleepyPrefixAt H ΔF look b → (tr.upTo b).SleepyPrefixAt H ΔF look b

/-- UNPROVED prefix service supplier. Strict signed-row processing remains an obligation. -/
def prefixService_of_gst : Prop :=
  ∀ proposer dg H tr g ΔF b,
    Growing.LocalRun proposer dg H sg tr → Compose.NoCollRun dg tr →
    0 ≤ b → tr.GSTRunAt H ΔF g → PrefixService tr H g ΔF b

/-- UNPROVED honesty truncation on the retained trace, matching `resetService_truncH`.
Returning to the original trace's relay ancestry needs a separate supplier. -/
def prefixService_truncH : Prop :=
  ∀ (tr : RunTrace A) H g ΔF b,
    PrefixService tr H g ΔF b → Service (tr.upTo b) (truncH H b) g ΔF b

/-- UNPROVED readiness retention at a surviving actual cut. -/
def readyCut_upTo : Prop :=
  ∀ (tr : RunTrace A) H c b y i,
    0 ≤ tr.time i → tr.time i ≤ b →
    (ReadyCut (tr.upTo b) H c y i ↔ ReadyCut tr H c y i)

/-- Finite local consumers, independent of the whole-run fields of `ACCorrectLocal`.
Constructing this type provides no supplier. The proposal hold must survive the horizon. -/
structure FiniteLocal (C : ACCorrectLocal A sg) : Prop where
  /-- Bounded L3, with each reader honest at its own cut. -/
  sleepyReadySafe : ∀ proposer dg H tr ΔF b,
    Growing.LocalRun proposer dg H sg tr → Compose.NoCollRun dg tr →
    tr.SleepyPrefixAt H ΔF C.look b →
    ∀ y z i j, 0 ≤ tr.time i → tr.time i ≤ b →
      0 ≤ tr.time j → tr.time j ≤ b →
      ReadyCut tr H C.catchUp y i → ReadyCut tr H C.catchUp z j →
      Compatible (tr.HonestBlocksAt H) (tr.confirmedAt y i) (tr.confirmedAt z j)
  /-- Bounded L4; coverage does not produce a proposal. -/
  sleepyProposalSupply : ∀ proposer dg H tr ΔF b,
    Growing.LocalRun proposer dg H sg tr → Compose.NoCollRun dg tr →
    tr.SleepyPrefixAt H ΔF C.look b →
    ∀ B k y j, 0 ≤ tr.time k → tr.time k + C.hold ≤ b →
      ReadyProposal tr H C.catchUp C.hold B k →
      tr.time k + C.margin ≤ tr.time j → tr.time j ≤ b →
      ReadyCut tr H C.catchUp y j →
      Anc (tr.HonestBlocksAt H) B (tr.confirmedAt y j)
  /-- Bounded L5, retaining the actual payload projection. -/
  sleepyInclusionCoverage : ∀ proposer dg H tr ΔF b,
    Growing.LocalRun proposer dg H sg tr → Compose.NoCollRun dg tr →
    tr.SleepyPrefixAt H ΔF C.look b →
    ∀ B k y j, 0 ≤ tr.time k → tr.time k + C.hold ≤ b →
      ReadyProposal tr H C.catchUp C.hold B k →
      tr.time k + C.margin ≤ tr.time j → tr.time j ≤ b →
      ReadyCut tr H C.catchUp y j →
      C.payload B ⊆ C.payload (tr.confirmedAt y j)
  /-- Bounded L6; healing and the real healed slot remain separate inputs. -/
  healedTips : ∀ proposer dg H tr ΔF g b s₁,
    C.healing.Run proposer dg H tr → Compose.NoCollRun dg tr →
    HealthyPrefix tr H ΔF g b → HealedFrom tr H proposer s₁ b →
    max g 0 ≤ P.slotTime s₁ →
    (∀ y z i j, P.slotTime s₁ + C.margin ≤ tr.time i → tr.time i ≤ b →
      P.slotTime s₁ + C.margin ≤ tr.time j → tr.time j ≤ b →
      ReadyCut tr H C.catchUp y i → ReadyCut tr H C.catchUp z j →
      Compatible (tr.HonestBlocksAt H) (tr.confirmedAt y i) (tr.confirmedAt z j)) ∧
    ∀ z k X, HonestProposal tr H proposer s₁ z k X →
      0 ≤ tr.time k → tr.time k + C.hold ≤ b →
      ∀ y j, tr.time k + C.margin ≤ tr.time j → tr.time j ≤ b →
        ReadyCut tr H C.catchUp y j →
        Anc (tr.HonestBlocksAt H) X (tr.confirmedAt y j)
  /-- Bounded L7; actual proposal existence is not a field of this record. -/
  healthyConfirmedSupply : ∀ proposer dg H tr ΔF g healed b,
    Growing.LocalRun proposer dg H sg tr → Compose.NoCollRun dg tr →
    HealthyPrefix tr H ΔF g b → max g 0 + C.margin ≤ healed →
    ∀ B k y j, ReadyProposal tr H C.catchUp C.hold B k →
      healed ≤ tr.time k → tr.time k + C.hold ≤ b →
      tr.time k + C.latency ≤ tr.time j → tr.time j ≤ b →
      ReadyCut tr H C.catchUp y j →
      Anc (tr.HonestBlocksAt H) B (tr.confirmedAt y j)

end Consensus.Goldilocks.Generic

end
