module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ReadPoint
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ProgressBudget

@[expose] public section

/-! # Open claim-consumer transports

These are admission-free interface rows, not evidence. Every row is UNPROVED; no
inhabitation or sufficiency theorem is claimed. In particular the witness refinements and
deadline production below are NEW UNRESOLVED SUFFICIENCY TARGETS, not consequences of
the existing budget contracts. One map and the actual block/cut witnesses are retained.
-/

set_option autoImplicit false
namespace Consensus.Goldilocks.Generic
open Shape Blocks

variable {P : Params} {A : NodeAC P} {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V} {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}

/-- OPEN numerical matching. Source consumers: ReadPoint.sleepy/healthy proposal and
healed, versus Shape.ProposalLiveReady and ShapeClaimsAt.healedSafe. These inequalities
are NEW UNRESOLVED SUFFICIENCY TARGETS for an arbitrary advertised contract. -/
structure ClaimDeadlineFit (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop where
  catchUp : C.catchUp ≤ (Sys F V).cDur K ⟨E, rho⟩
  latency_le_margin : C.latency ≤ C.margin
  healthy_start : ∀ cap idx gst, (cap = .available ∨ cap = .stable) →
    max gst 0 + C.margin ≤ (Sys F V).heal K cap idx gst ⟨E, rho⟩
  accountable : K.params.α * (P.n : ℚ) ≤ (2 * P.q - P.n : Nat)
  final_faults : ∀ t, 0 ≤ t → t ≤ rho.horizon →
    3 * (M.honest t)ᶜ.ncard ≤ P.n - 1 →
    (M.honest t)ᶜ.ncard < 2 * P.q - P.n

/-- OPEN admissibility of an actual proposal witness. Source: Concrete/Fields.lean
sleepyLive and healthyLive_confirmed use ConfirmedQueryAt's ready serviced proposal.
ReadyProposal alone has neither the engine cDur awake interval nor a surviving hold. -/
def AdmissibleProposal (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) (B : A.Blk) (k : Nat) : Prop :=
  B.root ≠ P.genesisRoot ∧
    0 ≤ M.trace.time k ∧ M.trace.time k + C.hold ≤ rho.horizon ∧
    rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩)
      (M.validator B.proposer) (M.trace.time k)

/-- OPEN same-query witness refinement, not an arbitrary callback or a claim output.
NEW UNRESOLVED SUFFICIENCY TARGET: selecting an admissible witness needs stronger
production than ProposalBudgetSupply/SleepyProposalBudgetSupply currently state.
No claim is made that every witness of either old supplier is admissible. -/
structure ProposalWitnessRefinement (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop where
  sleepy : rho.ExecutionValid → ∀ cap idx t,
    (cap = .available ∨ cap = .stable) → (Sys F V).Sleepy K ⟨E, rho⟩ →
    (Sys F V).prog (shapeProgress F V) K cap idx 0 rho.horizon ⟨E, rho⟩ →
    0 ≤ t → t + (K.params.latency cap idx : Time) * E.ΔAC ≤ rho.horizon →
    (∃ v, rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) v
      (t + (K.params.latency cap idx : Time) * E.ΔAC)) →
    ∃ B k, t < M.trace.time k ∧ ReadyProposal M.trace M.honest C.catchUp C.hold B k ∧
      M.trace.time k + C.margin ≤ t + (K.params.latency cap idx : Time) * E.ΔAC ∧
      AdmissibleProposal M K C B k
  healthy : rho.ExecutionValid → ∀ cap idx gst t,
    (cap = .available ∨ cap = .stable) → (Sys F V).Healthy K gst ⟨E, rho⟩ →
    (Sys F V).prog (shapeProgress F V) K cap idx ((Sys F V).ready K gst ⟨E, rho⟩)
      rho.horizon ⟨E, rho⟩ →
    (Sys F V).heal K cap idx gst ⟨E, rho⟩ ≤ t →
    t + (K.params.latency cap idx : Time) * E.ΔAC ≤ rho.horizon →
    (∃ v, rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) v
      (t + (K.params.latency cap idx : Time) * E.ΔAC)) →
    ∃ B k, t < M.trace.time k ∧ ReadyProposal M.trace M.honest C.catchUp C.hold B k ∧
      M.trace.time k + C.margin ≤ t + (K.params.latency cap idx : Time) * E.ΔAC ∧
      AdmissibleProposal M K C B k

/-- OPEN exact end-of-time state/read adapter. Source: Endpoint/Outputs.prefix_reader_at
and confirmed_payload_projection_at; consumers are inclusion and outage reads.
Unlike EngineReadPoint this evaluates at t, not cutTime(endCut t). No clock equality
or honesty at the next micro-cut is asserted. The state identity is a NEW UNRESOLVED
SUFFICIENCY TARGET for an arbitrary RunMap. -/
structure EndReadTransport (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop where
  ready : rho.ExecutionValid → ∀ v t, 0 ≤ t → t ≤ rho.horizon →
    rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) v t →
    ReadyReadPoint M.trace M.honest rho.horizon C.catchUp (M.validator.symm v)
      (M.cut ((chainTrace rho).endCut t)) t
  boundary : rho.ExecutionValid → ∀ v t, 0 ≤ t → t ≤ rho.horizon →
    rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) v t →
    ReadBoundary M.trace (M.validator.symm v) (M.cut ((chainTrace rho).endCut t))
  output : rho.ExecutionValid → ∀ v t, 0 ≤ t → t ≤ rho.horizon →
    rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) v t → ∀ g,
    (chainTrace rho).readAt g v t =
      (M.chain (M.trace.state (M.validator.symm v) (M.cut ((chainTrace rho).endCut t)))
        (M.tip g (M.trace.state (M.validator.symm v)
          (M.cut ((chainTrace rho).endCut t))) t)).map M.header

/-- OPEN precise deadline premises; source: concrete healthy preparation/final queries
and Premises in Generic/Obligations. NEW UNRESOLVED SUFFICIENCY TARGET, not a consequence
of FinalWindowSupply. Every Premises field, including service, snapshot, noRestart,
catch-up, slot arithmetic and nonempty, must be independently discharged. -/
def DeadlinePremisesSupply (M : RunMap rho payload) (K : Contract ProgressReq) : Prop :=
  rho.ExecutionValid → ¬ rho.HashCollision → ∀ idx gst query,
    (Sys F V).Healthy K gst ⟨E, rho⟩ →
    (Sys F V).prog (shapeProgress F V) K .final idx ((Sys F V).ready K gst ⟨E, rho⟩)
      rho.horizon ⟨E, rho⟩ →
    (Sys F V).heal K .final idx gst ⟨E, rho⟩ ≤ query →
    query + (K.params.latency .final idx : Time) * E.ΔAC ≤ rho.horizon →
    (∃ v, rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) v
      (query + (K.params.latency .final idx : Time) * E.ΔAC)) →
    Premises M.trace M.honest M.proposer M.digest M.signer gst E.ΔFG
      (query + (K.params.latency .final idx : Time) * E.ΔAC)

/-- OPEN final anchor readiness; source: final payload projection's serviced proposer.
NEW UNRESOLVED SUFFICIENCY TARGET: FinalProductionWindow.ready uses the local duration,
not the advertised engine duration. The first anchor and its cut are not replaced. -/
def FinalProposerTransport (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop :=
  ∀ query deadline (W : FinalProductionWindow M C.catchUp C.hold query deadline),
    rho.ExecutionValid → 0 ≤ query → deadline ≤ rho.horizon →
    (W.block 0).root ≠ P.genesisRoot ∧
      rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩)
        (M.validator (W.block 0).proposer) (M.trace.time (W.cut 0))

/-- OPEN actual-read carrier/cache bridge. Source: concrete final carrier processing
and final payload projection. NEW UNRESOLVED SUFFICIENCY TARGET: the current
FinalCarrierSupply/FinalCacheSupply require ReadyCut at trace.time j, which cannot
be inferred from readiness at the earlier actual read t. This contract retains the
real processing witness and separately consumes all anchor-height inputs. -/
structure FinalReadTransport (M : RunMap rho payload) (C : ACCorrectLocal A M.signer) : Prop where
  processed : rho.ExecutionValid → ∀ query deadline
    (W : FinalProductionWindow M C.catchUp C.hold query deadline) y j t,
    deadline ≤ t → ReadyReadPoint M.trace M.honest rho.horizon C.catchUp y j t →
    ReadBoundary M.trace y j →
    CarrierProcessed M (W.block 3) y j (M.trace.time (W.cut 3)) deadline
  cache : ∀ gst query deadline
    (W : FinalProductionWindow M C.catchUp C.hold query deadline),
    A.Requirements → C.healing.Run M.proposer M.digest M.honest M.trace →
    Premises M.trace M.honest M.proposer M.digest M.signer gst E.ΔFG deadline →
    HealedFrom M.trace M.honest M.proposer W.start deadline →
    (∀ a, M.trace.AcceptAt (W.block a).proposer (W.cut a) (W.block a)) →
    (∀ a b, a ≤ b → Anc (M.trace.HonestBlocksAt M.honest) (W.block a) (W.block b)) →
    (∀ a : Fin 3, ∃ z i j, z ∈ M.honest (M.trace.time i) ∧
      z ∈ M.honest (M.trace.time j) ∧
      W.block a.castSucc ∈ (M.trace.state z i).fg.tree ∧
      W.block a.succ ∈ (M.trace.state z j).fg.tree ∧
      ((M.trace.state z i).fg.σ (W.block a.castSucc).root).h + 1 ≤
        ((M.trace.state z j).fg.σ (W.block a.succ).root).h) →
    ∀ y j t, deadline ≤ t →
    ReadyReadPoint M.trace M.honest rho.horizon C.catchUp y j t →
    ReadBoundary M.trace y j →
    (M.honest t)ᶜ.ncard < 2 * P.q - P.n →
    CarrierProcessed M (W.block 3) y j (M.trace.time (W.cut 3)) deadline →
    Anc (M.trace.HonestBlocksAt M.honest) (W.block 0) (M.trace.finalizedAt y j)

/-- OPEN actual-read population evidence. Source: growing Endpoint/Accountable,
finalAccountable_readPoint (not the cut-time-only Generic.FinalAccountable).
The population cardinality and ChainAtts are unchanged; E1's chain_att_view,
att_signer and att_conflict separately bind these witnesses to engine evidence.
NEW UNRESOLVED SUFFICIENCY TARGET for an arbitrary AC. -/
def ActualReadAccountability (M : RunMap rho payload) : Prop :=
  A.Requirements → (P.genesisBlock A.genesisPayload).RootOk M.digest →
  Growing.LocalRun M.proposer M.digest M.honest M.signer M.trace →
  Compose.NoCollRun M.digest M.trace → ∀ y z i j t u,
  HonestReadPoint M.trace M.honest rho.horizon y i t →
  HonestReadPoint M.trace M.honest rho.horizon z j u →
  ¬ Compatible (M.trace.HonestBlocksAt M.honest)
    (M.trace.finalizedAt y i) (M.trace.finalizedAt z j) →
  ∃ X ∈ (M.trace.state y i).fg.tree, ∃ Y ∈ (M.trace.state z j).fg.tree,
    ∃ W : Finset (Fin P.n), 2 * P.q - P.n ≤ W.card ∧
      ∀ v ∈ W, ∃ a ∈ BlockFinality.ChainAtts M.trace y i X ∪
          BlockFinality.ChainAtts M.trace z j Y,
        ∃ b ∈ BlockFinality.ChainAtts M.trace y i X ∪
          BlockFinality.ChainAtts M.trace z j Y,
          a.val = v ∧ FG.slashable a b

/-- OPEN actual reset production, independent of canonicality and the drain budget.
Source: Healthy/PreparationReset.healthy_preparation_reset_at. NEW UNRESOLVED
SUFFICIENCY TARGET for all advertised progress forms. -/
def ActualResetSupply (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop :=
  rho.ExecutionValid → ¬ rho.HashCollision → ∀ cap idx gst,
  (cap = .available ∨ cap = .stable) → (Sys F V).Healthy K gst ⟨E, rho⟩ →
  (Sys F V).prog (shapeProgress F V) K cap idx ((Sys F V).ready K gst ⟨E, rho⟩)
    ((Sys F V).heal K cap idx gst ⟨E, rho⟩) ⟨E, rho⟩ →
  (Sys F V).heal K cap idx gst ⟨E, rho⟩ ≤ rho.horizon →
  ∃ a, C.healing.Run M.proposer M.digest M.honest M.trace ∧
    Healing.Growing.IsReset M.trace M.honest gst a ∧ a ≤ rho.horizon

/-- OPEN source prerequisites of heal_after_reset, never obtained by applying that
field itself. Source: Generic/Obligations.HighCanonical and concrete healthy reset
premises. NEW UNRESOLVED SUFFICIENCY TARGET at the same full run and horizon. -/
def HighCanonicalSupply (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop :=
  rho.ExecutionValid → ¬ rho.HashCollision → ∀ gst a,
  (Sys F V).Healthy K gst ⟨E, rho⟩ →
  C.healing.Run M.proposer M.digest M.honest M.trace →
  Premises M.trace M.honest M.proposer M.digest M.signer gst E.ΔFG rho.horizon →
  Healing.Growing.IsReset M.trace M.honest gst a → a ≤ rho.horizon →
  HighCanonical C.healing.Origin M.trace M.honest gst rho.horizon

/-- OPEN healthy-preparation premises at the same consuming horizon. Source:
Healthy/PreparationReset and Generic/Obligations.Premises. NEW UNRESOLVED
SUFFICIENCY TARGET; final-query DeadlinePremisesSupply cannot supply this row. -/
def PreparationPremisesSupply (M : RunMap rho payload) (K : Contract ProgressReq) : Prop :=
  rho.ExecutionValid → ¬ rho.HashCollision → ∀ cap idx gst,
  (cap = .available ∨ cap = .stable) → (Sys F V).Healthy K gst ⟨E, rho⟩ →
  (Sys F V).prog (shapeProgress F V) K cap idx ((Sys F V).ready K gst ⟨E, rho⟩)
    ((Sys F V).heal K cap idx gst ⟨E, rho⟩) ⟨E, rho⟩ →
  (Sys F V).heal K cap idx gst ⟨E, rho⟩ ≤ rho.horizon →
  Premises M.trace M.honest M.proposer M.digest M.signer gst E.ΔFG rho.horizon

/-- OPEN selected-reset drain/slot budget. Source: Healthy/PreparationInitialize,
healthy_preparation_initialize_late_at. NEW UNRESOLVED SUFFICIENCY TARGET: a reset
exists before this exact deadline, not merely before the horizon. Keeping selection
separate from ActualResetSupply avoids asserting that every possible reset is early. -/
def ResetHealBudgetSupply (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop :=
  rho.ExecutionValid → ¬ rho.HashCollision → ∀ cap idx gst,
  (cap = .available ∨ cap = .stable) → (Sys F V).Healthy K gst ⟨E, rho⟩ →
  (Sys F V).prog (shapeProgress F V) K cap idx ((Sys F V).ready K gst ⟨E, rho⟩)
    ((Sys F V).heal K cap idx gst ⟨E, rho⟩) ⟨E, rho⟩ →
  (Sys F V).heal K cap idx gst ⟨E, rho⟩ ≤ rho.horizon →
  ∃ a, Healing.Growing.IsReset M.trace M.honest gst a ∧ a ≤ rho.horizon ∧
    max gst 0 ≤ P.slotTime (P.slotOf a + C.healing.drain) ∧
    P.slotTime (P.slotOf a + C.healing.drain) + C.margin ≤
      (Sys F V).heal K cap idx gst ⟨E, rho⟩

/-- OPEN exact matching of the fixed local outage policy to the advertised duration.
NEW UNRESOLVED SUFFICIENCY TARGET: neither a concrete recovery equation nor its
adequacy is supplied. Equality is this interface's restriction, not necessary for
persistence: a larger advertised duration may safely dominate the local floor.
Rewriting this equation makes the local guard reflexive at System.recoveryAt;
it does not establish either guarded protection supplier. -/
structure OutageRecoveryBinding (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop where
  /-- One fixed local duration matches the same run's advertised recovery duration. -/
  duration : C.recovery = (K.params.recovery : Time) * E.ΔAC

/-- OPEN pre-outage service at the consuming bound. Source:
Outage/Engine/Query.outage_pre_service_at supplies SleepyServiceBefore, NOT this
SyncRunAt package. NEW UNRESOLVED SUFFICIENCY TARGET: the precise service-type
derivation remains open, as does the Delta reserve mismatch with ServiceTransport.sync.
The original service transport is not strengthened. -/
def OutageServiceSupply (M : RunMap rho payload) (K : Contract ProgressReq) : Prop :=
  rho.ExecutionValid → ¬ rho.HashCollision → ∀ T b₀ b₁,
  (Sys F V).Outage (shapeProgress F V).toExternal K T b₀ b₁ ⟨E, rho⟩ →
  M.trace.SyncRunAt M.honest E.ΔFG 0 b₀ ∧ M.trace.GSTRunAt M.honest E.ΔFG b₁

/-- OPEN schema representation, not protection. Source: Concrete/Fields.persists
and Outage/Engine/Repair.outage_protected_at use the confirmed alias for both
provided nonfinal capabilities. NEW UNRESOLVED SUFFICIENCY TARGET for arbitrary F. -/
def ResilienceTipTransport (M : RunMap rho payload) : Prop :=
  ∀ g, O.output .stable = some g → ∀ st t,
    M.tip (resilienceTarget O g) st t = A.confirmed st.ac (Node.frame st) t

/-- OPEN source read context: concrete realization must use lastOwn/cutMap and
stateAt.now/readAfter from Healthy/CutTips.healthy_cut_tips_ancestor_at, not simply
the current mapped cut. This data supplies no correspondence by itself. -/
structure StoredReadContext (M : RunMap rho payload) where
  cut : V → Nat → Nat
  now : V → Nat → Time
  tip : V → Nat → A.Blk

/-- OPEN explicit source/current-read correspondence. NEW UNRESOLVED SUFFICIENCY
TARGET: no generic implementation of the stored-clock context is supplied. In
particular the equalities below do not assert equality of either pair of clocks. -/
structure StoredReadTransport (M : RunMap rho payload) (R : StoredReadContext M) : Prop where
  source_tip : ∀ v i, R.tip v i = confirmedRead M.trace (M.validator.symm v)
    (R.cut v i) (R.now v i)
  current_tip : rho.ExecutionValid → ∀ v i, i ≤ rho.events.length →
    rho.point.HonestAt v (rho.cutTime i) →
    R.tip v i = confirmedRead M.trace (M.validator.symm v) (M.cut i) (rho.cutTime i)
  now_bound : rho.ExecutionValid → ∀ v i, i ≤ rho.events.length →
    rho.point.HonestAt v (rho.cutTime i) → R.now v i ≤ rho.horizon

/-- OPEN local block ancestry at two actual reads. Source shape is
Healthy/CutTips.healthy_cut_tips_ancestor_at at E1; its concrete query, actual
ready→heal progress, both ready reads, ordered cuts and later stored-now bound
are retained below. NEW UNRESOLVED SUFFICIENCY TARGET for arbitrary M/R;
StoredReadTransport is a separate missing realization, not that concrete theorem.
No ReadySafe or chain-prefix conclusion is hidden in this interface. -/
def HealedReadAncestry (M : RunMap rho payload) (K : Contract ProgressReq)
    (R : StoredReadContext M) : Prop :=
  rho.ExecutionValid → ¬ rho.HashCollision → ∀ cap idx gst,
  (cap = .available ∨ cap = .stable) → (Sys F V).Healthy K gst ⟨E, rho⟩ →
  (Sys F V).prog (shapeProgress F V) K cap idx ((Sys F V).ready K gst ⟨E, rho⟩)
    ((Sys F V).heal K cap idx gst ⟨E, rho⟩) ⟨E, rho⟩ →
  0 ≤ (Sys F V).heal K cap idx gst ⟨E, rho⟩ →
  (Sys F V).heal K cap idx gst ⟨E, rho⟩ ≤ rho.horizon →
  ∀ v i j, (chainTrace rho).InCuts ((Sys F V).heal K cap idx gst ⟨E, rho⟩) i →
  i ≤ j → (chainTrace rho).InCuts ((Sys F V).heal K cap idx gst ⟨E, rho⟩) j →
  rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) v (rho.cutTime i) →
  rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) v (rho.cutTime j) →
  R.now v j ≤ rho.horizon →
  Anc (M.trace.HonestBlocksAt M.honest) (R.tip v i) (R.tip v j)

end Consensus.Goldilocks.Generic

end
