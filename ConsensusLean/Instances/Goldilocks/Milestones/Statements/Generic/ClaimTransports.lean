module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ReadPoint
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ProgressBudget
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.SleepyLayer1

@[expose] public section

/-! # Claim-consumer suppliers

These are admission-free interface rows, not evidence. Every row is UNPROVED; no
inhabitation or sufficiency theorem is claimed. Named concrete sources identify the
instance proof routes; they do not supply generic adapters automatically. One map
and the actual block/cut witnesses are retained.
-/

set_option autoImplicit false
namespace Consensus.Goldilocks.Generic
open Shape Blocks

variable {P : Params} {A : NodeAC P} {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V} {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}

/-- The population quorum needed by shared FG reasoning, independently of the committee
count. An arbitrary admissible threshold need not imply this inequality. -/
def PopulationQuorumSupply (M : RunMap rho payload) (K : Contract ProgressReq) : Prop :=
  rho.ExecutionValid →
    (Sys F V).Sleepy (shapeProgress F V).toExternal K ⟨E, rho⟩ →
    ∀ t, 0 ≤ t → t ≤ rho.horizon → 2 * (M.honest t)ᶜ.ncard < P.n

/-- One point on the mapped validator indices, with independent look-ahead fits.
The population and committee transports retain their own charge times. -/
def SleepyWindowSupply (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop :=
  ∃ p : EnvPoint (Fin P.n), RunPointBinding M.trace M.honest p ∧
    p.horizon = rho.horizon ∧ C.θ = K.params.θ ∧ 0 ≤ C.θ ∧ C.θ ≤ 1 ∧
    C.look = (Sys F V).aheadDur K ⟨E, rho⟩ ∧
    C.committeeLook = (Sys F V).committeeAheadDur K ⟨E, rho⟩ ∧
    (rho.ExecutionValid →
      (Sys F V).Sleepy (shapeProgress F V).toExternal K ⟨E, rho⟩ →
      p.SleepyOn C.θ ((Sys F V).cDur K ⟨E, rho⟩) C.look 0 rho.horizon ∧
      p.CommitteeSleepyOn M.committee C.θ 0 ((Sys F V).cDur K ⟨E, rho⟩)
        C.committeeLook 0 rho.horizon)

/-- Numerical matching from `confirmed_duration_supply_at` and the contract
catch-up/heal/latency equations in `Lemmas/Obligations/ContractDefs`.
The chosen local parameters and FG threshold arithmetic must satisfy every field. -/
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

/-- Admissibility of the witness selected by `confirmed_query_slot_at` and
`confirmed_slot_event_at`, as consumed by `confirmed_payload_projection_at`.
ReadyProposal alone has neither the engine cDur awake interval nor a surviving hold. -/
def AdmissibleProposal (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) (B : A.Blk) (k : Nat) : Prop :=
  B.root ≠ P.genesisRoot ∧
    0 ≤ M.trace.time k ∧ M.trace.time k + C.hold ≤ rho.horizon ∧
    rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩)
      (M.validator B.proposer) (M.trace.time k)

/-- Same-query production from `sleepy_query_producer_at` and
`healthy_confirmed_supply_at`. Advertised readiness is retained jointly with the
selected proposal; arbitrary locally ready proposals need not be admissible.
Collision freedom is used only in the collision-excused liveness reductions. -/
structure ProposalWitnessRefinement (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop where
  sleepy : rho.ExecutionValid → ¬ rho.HashCollision → ∀ cap idx t,
    (cap = .available ∨ cap = .stable) →
    (Sys F V).Sleepy (shapeProgress F V).toExternal K ⟨E, rho⟩ →
    (Sys F V).prog (shapeProgress F V) K cap idx 0 rho.horizon ⟨E, rho⟩ →
    0 ≤ t → t + (K.params.latency cap idx : Time) * E.ΔAC ≤ rho.horizon →
    (∃ v, rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) v
      (t + (K.params.latency cap idx : Time) * E.ΔAC)) →
    ∃ B k, t < M.trace.time k ∧ ReadyProposal M.trace M.honest C.catchUp C.hold B k ∧
      M.trace.time k + C.margin ≤ t + (K.params.latency cap idx : Time) * E.ΔAC ∧
      AdmissibleProposal M K C B k
  healthy : rho.ExecutionValid → ¬ rho.HashCollision → ∀ cap idx gst t,
    (cap = .available ∨ cap = .stable) →
    (Sys F V).Healthy (shapeProgress F V).toExternal K gst ⟨E, rho⟩ →
    (Sys F V).prog (shapeProgress F V) K cap idx ((Sys F V).ready K gst ⟨E, rho⟩)
      rho.horizon ⟨E, rho⟩ →
    (Sys F V).heal K cap idx gst ⟨E, rho⟩ ≤ t →
    t + (K.params.latency cap idx : Time) * E.ΔAC ≤ rho.horizon →
    (∃ v, rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) v
      (t + (K.params.latency cap idx : Time) * E.ΔAC)) →
    ∃ B k, t < M.trace.time k ∧ ReadyProposal M.trace M.honest C.catchUp C.hold B k ∧
      M.trace.time k + C.margin ≤ t + (K.params.latency cap idx : Time) * E.ΔAC ∧
      AdmissibleProposal M K C B k

/-- OPEN end-of-time read adapter along `confirmed_payload_projection_at`/`confirmed_inBy_at`.
`ready` and `boundary` are stated at the claim time `t`, not at `cutTime (endCut t)`.
`output` reads the tip at the stored clock `M.clock` of the state at `endCut t`,
which need not equal either time. No clock equality or honesty at the next micro-cut is asserted.
The step from readiness at `t` to a ready read point at the stored clock is a NEW UNRESOLVED
SUFFICIENCY TARGET; this structure does not supply it. -/
structure EndReadTransport (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop where
  strict_cut : rho.ExecutionValid → ∀ t, 0 ≤ t → t ≤ rho.horizon →
    t < M.trace.time (M.cut ((chainTrace rho).endCut t))
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
          (M.cut ((chainTrace rho).endCut t)))
          (M.clock (rho.stateBefore ((chainTrace rho).endCut t) v).st.1))).map M.header

/-- Deadline premises assembled from `final_reset_premises_at` and healthy
service transport. The chosen forwarding delay and snapshot must fit this exact
deadline. Every `Premises` field, including committee counts, remains required;
this is not obtained from the final-window conclusion. -/
def DeadlinePremisesSupply (M : RunMap rho payload) (K : Contract ProgressReq) : Prop :=
  rho.ExecutionValid → ¬ rho.HashCollision → ∀ idx gst query,
    (Sys F V).Healthy (shapeProgress F V).toExternal K gst ⟨E, rho⟩ →
    (Sys F V).prog (shapeProgress F V) K .final idx ((Sys F V).ready K gst ⟨E, rho⟩)
      rho.horizon ⟨E, rho⟩ →
    (Sys F V).heal K .final idx gst ⟨E, rho⟩ ≤ query →
    query + (K.params.latency .final idx : Time) * E.ΔAC ≤ rho.horizon →
    (∃ v, rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) v
      (query + (K.params.latency .final idx : Time) * E.ΔAC)) →
    Premises M.trace M.honest M.committee K.params.βK M.proposer M.digest M.signer gst E.ΔFG
      (query + (K.params.latency .final idx : Time) * E.ΔAC)

/-- Actual-read carrier/cache bridge. The processing supplier is
`carrier_processed_of_honest_at`: healthy service, an honest anchor and a
deadline-ready reader. Cache ancestry uses `cacheCoverage_of_anchor_window_upTo_at`.
The exact generic adapters remain proof obligations. -/
structure FinalReadTransport (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop where
  processed : rho.ExecutionValid → ¬ rho.HashCollision → ∀ idx gst query deadline
    (W : FinalProductionWindow M C.catchUp C.hold query deadline),
    (Sys F V).Healthy (shapeProgress F V).toExternal K gst ⟨E, rho⟩ →
    (Sys F V).prog (shapeProgress F V) K .final idx ((Sys F V).ready K gst ⟨E, rho⟩)
      rho.horizon ⟨E, rho⟩ →
    (Sys F V).heal K .final idx gst ⟨E, rho⟩ ≤ query →
    deadline = query + (K.params.latency .final idx : Time) * E.ΔAC →
    deadline ≤ rho.horizon →
    HonestProposal M.trace M.honest M.proposer (W.block 3).slot
      (W.block 3).proposer (W.cut 3) (W.block 3) →
    ∀ y j, rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) (M.validator y) deadline →
    ReadyReadPoint M.trace M.honest rho.horizon C.catchUp y j deadline →
    ReadBoundary M.trace y j → deadline < M.trace.time j →
    CarrierProcessed M (W.block 3) y j (M.trace.time (W.cut 3)) deadline
  cache : ∀ (βK : ℚ) gst query deadline
    (W : FinalProductionWindow M C.catchUp C.hold query deadline),
    βK ≤ 1 / 2 →
    C.run.Run M.committee M.proposer M.digest M.honest M.trace →
    Premises M.trace M.honest M.committee βK M.proposer M.digest M.signer gst E.ΔFG deadline →
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

/-- Actual-read population evidence from `finalAccountable_readPoint`
(not the cut-time-only `Generic.FinalAccountable`).
The population cardinality and ChainAtts are unchanged; E1's chain_att_view,
att_signer and att_conflict separately bind these witnesses to engine evidence.
The shared FG proof supplies the route; its generic adapter remains to be proved. -/
def ActualReadAccountability (M : RunMap rho payload) (runs : ACRun A M.signer) : Prop :=
  runs.Run M.committee M.proposer M.digest M.honest M.trace →
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

/-- Canonical-high assembly from `high_row_source_at`, `no_high_contest_at`
and `high_entry_eq_at`, with reset premises at the same horizon. This supplies
prerequisites of `heal_after_reset`, never by invoking that field itself. -/
def HighCanonicalSupply (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop :=
  CommitteeHalfFit K → rho.ExecutionValid → ¬ rho.HashCollision → ∀ gst a,
  (Sys F V).Healthy (shapeProgress F V).toExternal K gst ⟨E, rho⟩ →
  C.run.Run M.committee M.proposer M.digest M.honest M.trace →
  Premises M.trace M.honest M.committee K.params.βK M.proposer M.digest M.signer
    gst E.ΔFG rho.horizon →
  Healing.Growing.IsReset M.trace M.honest gst a → a ≤ rho.horizon →
  HighCanonical C.healing.Origin M.trace M.honest gst rho.horizon

/-- Full-horizon preparation from `healthy_preparation_service_at`,
`healthy_preparation_awake_at`, `healthy_preparation_faults_at`,
`healthy_preparation_noRestart_at` and the snapshot/catch-up assembly in
`healthy_preparation_reset_at`. Committee transport and delay fit remain required;
the final-query deadline supplier is not this full-horizon assembly. -/
def PreparationPremisesSupply (M : RunMap rho payload) (K : Contract ProgressReq) : Prop :=
  HealthyBetaFit K → rho.ExecutionValid → ¬ rho.HashCollision → ∀ cap idx gst,
  (cap = .available ∨ cap = .stable) →
  (Sys F V).Healthy (shapeProgress F V).toExternal K gst ⟨E, rho⟩ →
  (Sys F V).prog (shapeProgress F V) K cap idx ((Sys F V).ready K gst ⟨E, rho⟩)
    ((Sys F V).heal K cap idx gst ⟨E, rho⟩) ⟨E, rho⟩ →
  (Sys F V).heal K cap idx gst ⟨E, rho⟩ ≤ rho.horizon →
  Premises M.trace M.honest M.committee K.params.βK M.proposer M.digest M.signer
    gst E.ΔFG rho.horizon

/-- Selected-reset existence and drain/slot budget. Source:
`healthy_preparation_initialize_late_at`, using `healthy_preparation_reset_at`.
The same selected reset meets the deadline; arbitrary resets need not be early.
The local drain/margin arithmetic remains an instance proof obligation. -/
def ResetHealBudgetSupply (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop :=
  rho.ExecutionValid → ¬ rho.HashCollision → ∀ cap idx gst,
  (cap = .available ∨ cap = .stable) →
  (Sys F V).Healthy (shapeProgress F V).toExternal K gst ⟨E, rho⟩ →
  (Sys F V).prog (shapeProgress F V) K cap idx ((Sys F V).ready K gst ⟨E, rho⟩)
    ((Sys F V).heal K cap idx gst ⟨E, rho⟩) ⟨E, rho⟩ →
  (Sys F V).heal K cap idx gst ⟨E, rho⟩ ≤ rho.horizon →
  ∃ a, Healing.Growing.IsReset M.trace M.honest gst a ∧ a ≤ rho.horizon ∧
    max gst 0 ≤ P.slotTime (P.slotOf a + C.healing.drain) ∧
    P.slotTime (P.slotOf a + C.healing.drain) + C.margin ≤
      (Sys F V).heal K cap idx gst ⟨E, rho⟩

/-- Exact matching of the fixed local outage policy to the advertised contract.
These equations supply numerical rewriting, not the protection obligation OC-K.
`RunMap.delta_eq` fixes the delay across all environments covered by one local record. -/
structure OutageRecoveryBinding (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop where
  /-- One fixed local duration matches the same run's advertised recovery duration. -/
  duration : C.recovery = (K.params.recovery : Time) * E.ΔAC
  threshold : C.θ = K.params.θ
  catchUp : C.catchUp = (Sys F V).cDur K ⟨E, rho⟩
  look : C.look = (Sys F V).aheadDur K ⟨E, rho⟩
  committeeLook : C.committeeLook = (Sys F V).committeeAheadDur K ⟨E, rho⟩
  eta : C.outageEta = (K.params.η : Time) * E.ΔAC
  lag : C.outageLag = (K.params.lag : Time) * E.ΔAC
  budget : C.outageBudget = (K.params.budget : Time) * E.ΔAC

/-- Pre-outage recipient-deadline service and post-outage synchrony.
The concrete supplier is `outage_pre_service_at`; its message interpretation permits
fresh processing or retained evidence. Instance transport remains an obligation. -/
def OutageServiceSupply (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop :=
  rho.ExecutionValid → ¬ rho.HashCollision → ∀ T b₀ b₁,
  (Sys F V).Outage (shapeProgress F V).toExternal K T b₀ b₁ ⟨E, rho⟩ →
  ACServiceBefore C M.trace M.honest E.ΔFG b₀ ∧ M.trace.GSTRunAt M.honest E.ΔFG b₁

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
TARGET: no generic implementation of the stored-clock context is supplied.
The current read is at the map stored clock `M.clock`. Neither
`R.now v i = M.clock (rho.stateBefore i v).st.1` nor `R.cut v i = M.cut i`
is asserted; the two equalities below only identify the tips. -/
structure StoredReadTransport (M : RunMap rho payload) (R : StoredReadContext M) : Prop where
  source_tip : ∀ v i, R.tip v i = confirmedRead M.trace (M.validator.symm v)
    (R.cut v i) (R.now v i)
  current_tip : rho.ExecutionValid → ∀ v i, i ≤ rho.events.length →
    rho.point.HonestAt v (rho.cutTime i) →
    R.tip v i = confirmedRead M.trace (M.validator.symm v) (M.cut i)
      (M.clock (rho.stateBefore i v).st.1)
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
  (cap = .available ∨ cap = .stable) →
  (Sys F V).Healthy (shapeProgress F V).toExternal K gst ⟨E, rho⟩ →
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
