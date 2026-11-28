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
    {fgHold : Time} (C : ACCorrectLocal A M.signer fgHold) : Prop :=
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
    {fgHold : Time} (C : ACCorrectLocal A M.signer fgHold) : Prop where
  /-- One unit of readiness slack permits the local read at the stored clock. -/
  catchUp : C.catchUp + 1 ≤ (Sys F V).cDur K ⟨E, rho⟩
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
    {fgHold : Time} (C : ACCorrectLocal A M.signer fgHold) (B : A.Blk) (k : Nat) : Prop :=
  B.root ≠ P.genesisRoot ∧
    0 ≤ M.trace.time k ∧ M.trace.time k + C.hold ≤ rho.horizon ∧
    rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩)
      (M.validator B.proposer) (M.trace.time k)

/-- Same-query production from `sleepy_query_producer_at`, in the sleepy and in the healthy
regime. Advertised readiness is retained jointly with the
selected proposal; arbitrary locally ready proposals need not be admissible.
Collision freedom is used only in the collision-excused liveness reductions. -/
structure ProposalWitnessRefinement (M : RunMap rho payload) (K : Contract ProgressReq)
    {fgHold : Time} (C : ACCorrectLocal A M.signer fgHold) : Prop where
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

/-- Deadline premises assembled from `final_reset_premises_of_shared_within_at` and healthy
service transport, on the honest sets truncated after this exact deadline
(`premises_truncH`): restarts are bounded only through the deadline, so no whole-run
`NoRestartAfter` is required of a finite healthy query. The chosen forwarding delay and
snapshot must fit this exact deadline; truncation discharges neither. Every `Premises`
field, including committee counts, remains required; this is not obtained from the
final-window conclusion. The premises are at release hold `hold` and FG delay `ΔF` (defaults `0`
and `E.ΔFG`). -/
def DeadlinePremisesSupply (M : RunMap rho payload) (K : Contract ProgressReq) (hold : Time := 0)
    (ΔF : Time := E.ΔFG) : Prop :=
  rho.ExecutionValid → ¬ rho.HashCollision → ∀ idx gst query,
    (Sys F V).Healthy (shapeProgress F V).toExternal K gst ⟨E, rho⟩ →
    (Sys F V).prog (shapeProgress F V) K .final idx ((Sys F V).ready K gst ⟨E, rho⟩)
      rho.horizon ⟨E, rho⟩ →
    (Sys F V).heal K .final idx gst ⟨E, rho⟩ ≤ query →
    query + (K.params.latency .final idx : Time) * E.ΔAC ≤ rho.horizon →
    (∃ v, rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) v
      (query + (K.params.latency .final idx : Time) * E.ΔAC)) →
    Premises M.trace (truncH M.honest (query + (K.params.latency .final idx : Time) * E.ΔAC))
      M.committee K.params.βK M.proposer M.digest M.signer gst ΔF
      (query + (K.params.latency .final idx : Time) * E.ΔAC) hold

/-- Actual-read cache bridge: the first anchor of a selected final window, with its acceptance,
chaining and height evidence, is below the finalized block of every ready reader from the
deadline on. Cache ancestry uses `cacheCoverage_of_anchor_window_upTo_at`.
The cache's `Premises` are on the honest sets truncated after `deadline`, as
`DeadlinePremisesSupply` returns them. Nobody is honest on that truncation after the
deadline, since `truncH H b t = H t ∩ {t ≤ b}`, so a reader at `deadline ≤ t` keeps its
honesty, its run and the population threshold at `t` on `M.honest`, and the window ancestry
and the conclusion stay over `M.honest`'s honest blocks; ancestry over the truncated honest
blocks is ancestry over `M.honest`'s, as `honestBlocksAt_truncH_subset` gives. The premises are
at `C`'s release hold and FG delay `ΔF` (default `E.ΔFG`). -/
structure FinalReadTransport (M : RunMap rho payload) {fgHold : Time}
    (C : ACCorrectLocal A M.signer fgHold) (ΔF : Time := E.ΔFG) : Prop where
  cache : ∀ (βK : ℚ) gst query deadline
    (W : FinalProductionWindow M C.catchUp C.hold query deadline),
    βK ≤ 1 / 2 →
    C.run.Run M.committee M.proposer M.digest M.honest M.trace →
    Premises M.trace (truncH M.honest deadline) M.committee βK M.proposer M.digest M.signer gst
      ΔF deadline fgHold →
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
    Anc (M.trace.HonestBlocksAt M.honest) (W.block 0) (M.trace.finalizedAt y j)

/-- Actual-read population evidence from `finalAccountable_readPoint`
(not a cut-time-only form).
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

/-- Full-horizon preparation from `healthy_preparation_service_at`,
`healthy_preparation_awake_at`, `healthy_preparation_faults_at`,
`healthy_preparation_noRestart_at` and the snapshot/catch-up assembly in
`healthy_preparation_reset_at`. Committee transport and delay fit remain required;
the final-query deadline supplier is not this full-horizon assembly. The premises are at release
hold `hold` and FG delay `ΔF` (defaults `0` and `E.ΔFG`). -/
def PreparationPremisesSupply (M : RunMap rho payload) (K : Contract ProgressReq)
    (hold : Time := 0) (ΔF : Time := E.ΔFG) : Prop :=
  HealthyBetaFit K → rho.ExecutionValid → ¬ rho.HashCollision → ∀ cap idx gst,
  (cap = .available ∨ cap = .stable) →
  (Sys F V).Healthy (shapeProgress F V).toExternal K gst ⟨E, rho⟩ →
  (Sys F V).prog (shapeProgress F V) K cap idx ((Sys F V).ready K gst ⟨E, rho⟩)
    ((Sys F V).heal K cap idx gst ⟨E, rho⟩) ⟨E, rho⟩ →
  (Sys F V).heal K cap idx gst ⟨E, rho⟩ ≤ rho.horizon →
  Premises M.trace M.honest M.committee K.params.βK M.proposer M.digest M.signer
    gst ΔF rho.horizon hold

/-- Selected-reset existence and drain/slot budget. Source:
`healthy_preparation_initialize_late_at`, using `healthy_preparation_reset_at`.
The same selected reset meets the deadline; arbitrary resets need not be early.
The `+ 1` absorbs the stored clock's lag: a healed read at the stored clock is at
`R.now ≥ cutTime i − 1 ≥ heal − 1` (`StoredReadTransport.ready_point`).
The same selection supplies the healed reads' opening: an honest proposal of a slot `s₁` at or
after the drain and at least four delays past `ḡ`, with its service reserve `t_{s₁} + 6Δ`
inside the horizon and `t_{s₁} + margin + 2 ≤ heal`, so that healed reads at the stored clock are
strictly after the opening's margin (source:
`healthy_bounded_repairing_opening_at` within the heal reserve). This is the opening that
`HealthyReadPoint.healed` requires.
The local drain/margin arithmetic remains an instance proof obligation. -/
def ResetHealBudgetSupply (M : RunMap rho payload) (K : Contract ProgressReq)
    {fgHold : Time} (C : ACCorrectLocal A M.signer fgHold) : Prop :=
  rho.ExecutionValid → ¬ rho.HashCollision → ∀ cap idx gst,
  (cap = .available ∨ cap = .stable) →
  (Sys F V).Healthy (shapeProgress F V).toExternal K gst ⟨E, rho⟩ →
  (Sys F V).prog (shapeProgress F V) K cap idx ((Sys F V).ready K gst ⟨E, rho⟩)
    ((Sys F V).heal K cap idx gst ⟨E, rho⟩) ⟨E, rho⟩ →
  (Sys F V).heal K cap idx gst ⟨E, rho⟩ ≤ rho.horizon →
  ∃ a, Healing.Growing.IsReset M.trace M.honest gst a ∧ a ≤ rho.horizon ∧
    ResetInBudget P C.healing.deepBudget C.healing.drain gst a ∧
    max gst 0 ≤ P.slotTime (P.slotOf a + C.healing.drain) ∧
    P.slotTime (P.slotOf a + C.healing.drain) + C.margin + 1 ≤
      (Sys F V).heal K cap idx gst ⟨E, rho⟩ ∧
    ∃ s₁ z k X, P.slotOf a + C.healing.drain ≤ s₁ ∧ AC.gbar gst + 4 * P.Δ ≤ P.slotTime s₁ ∧
      P.slotTime s₁ + 6 * P.Δ ≤ rho.horizon ∧
      P.slotTime s₁ + C.margin + 2 ≤ (Sys F V).heal K cap idx gst ⟨E, rho⟩ ∧
      HonestProposal M.trace M.honest M.proposer s₁ z k X

/-- Matching of the fixed local outage policy to the advertised contract.
Catch-up has one unit of slack; readiness and sleepy counts transport monotonically.
The remaining equations supply numerical rewriting, not the protection obligation OC-K.
`RunMap.delta_eq` fixes the delay across all environments covered by one local record. -/
structure OutageRecoveryBinding (M : RunMap rho payload) (K : Contract ProgressReq)
    {fgHold : Time} (C : ACCorrectLocal A M.signer fgHold) : Prop where
  /-- One fixed local duration matches the same run's advertised recovery duration. -/
  duration : C.recovery = (K.params.recovery : Time) * E.ΔAC
  threshold : C.θ = K.params.θ
  catchUp : C.catchUp + 1 ≤ (Sys F V).cDur K ⟨E, rho⟩
  look : C.look = (Sys F V).aheadDur K ⟨E, rho⟩
  committeeLook : C.committeeLook = (Sys F V).committeeAheadDur K ⟨E, rho⟩
  eta : C.outageEta = (K.params.η : Time) * E.ΔAC
  lag : C.outageLag = (K.params.lag : Time) * E.ΔAC
  budget : C.outageBudget = (K.params.budget : Time) * E.ΔAC

/-- Pre-outage recipient-deadline service and post-stop service (`PostStopService`: message
service and the unguarded acceptance relay the recovery consumes). Concrete suppliers:
`outage_pre_service_at`, whose message interpretation permits fresh processing or retained
evidence, and `goldilocks_postStopService`. Instance transport remains an obligation. -/
def OutageServiceSupply (M : RunMap rho payload) (K : Contract ProgressReq)
    {fgHold : Time} (C : ACCorrectLocal A M.signer fgHold) : Prop :=
  rho.ExecutionValid → ¬ rho.HashCollision → ∀ T b₀ b₁,
  (Sys F V).Outage (shapeProgress F V).toExternal K T b₀ b₁ ⟨E, rho⟩ →
  ACServiceBefore C M.trace M.honest E.ΔFG b₀ ∧ PostStopService M.trace M.honest b₁

/-- OPEN schema representation, not protection. Source: Outage/Engine/Repair.outage_protected_at
and the Goldilocks run map (`goldilocksRunMap_resilienceTipTransport`) use the confirmed alias
for both provided nonfinal capabilities. NEW UNRESOLVED SUFFICIENCY TARGET for arbitrary F. -/
def ResilienceTipTransport (M : RunMap rho payload) : Prop :=
  ∀ g, O.output .stable = some g → ∀ st t,
    M.tip (resilienceTarget O g) st t = A.confirmed st.ac (Node.frame st) t

/-- The reader's own read behind each engine cut: the trace cut after its last own event, its
stored clock, and the confirmed tip read there. Data only; `StoredReadTransport` supplies the laws.
Goldilocks: `goldilocksStoredReadContext` (`cutMap (lastOwn …)`, `stateAt.now`). -/
structure StoredReadContext (M : RunMap rho payload) where
  cut : V → Nat → Nat
  now : V → Nat → Time
  tip : V → Nat → A.Blk

/-- The single read binding of engine outputs, at engine cuts and at claim times.
At an engine cut `i` the output is read at the stored read `(R.cut v i, R.now v i)`: `source_tip`
and `current_tip` identify its tip with the mapped tip at the stored clock `M.clock`, and
`source_state` identifies the reader's whole local state at the two cuts, so held trees and chains
transfer, not only the tip. Under engine readiness with catch-up `c + 1` the stored read is a ready
read point with catch-up `c` and a read boundary, at most one unit before the cut time; stored reads
of one reader are ordered in both cut and time. At a claim time `t` read through `endCut t`, a
reader ready at `t` has stored clock exactly `t`, read strictly before the mapped cut.
No global clock equality: neither `R.now v i = rho.cutTime i` nor `R.cut v i = M.cut i` is
asserted. Goldilocks sources: `readAfter_lastOwn`, `stateAt_lastOwn`, `now_mono`, `lastOwn_mono`,
`engine_read_point`, `stored_now_ge_cutTime_sub_one`, `ready_read_cut_at`. -/
structure StoredReadTransport (M : RunMap rho payload) (R : StoredReadContext M) : Prop where
  source_tip : ∀ v i, R.tip v i = confirmedRead M.trace (M.validator.symm v)
    (R.cut v i) (R.now v i)
  current_tip : rho.ExecutionValid → ∀ v i, i ≤ rho.events.length →
    rho.point.HonestAt v (rho.cutTime i) →
    R.tip v i = confirmedRead M.trace (M.validator.symm v) (M.cut i)
      (M.clock (rho.stateBefore i v).st.1)
  source_state : rho.ExecutionValid → ∀ v i, i ≤ rho.events.length →
    M.trace.state (M.validator.symm v) (R.cut v i) =
      M.trace.state (M.validator.symm v) (M.cut i)
  now_bound : rho.ExecutionValid → ∀ v i, i ≤ rho.events.length →
    rho.point.HonestAt v (rho.cutTime i) → R.now v i ≤ rho.horizon
  now_mono : rho.ExecutionValid → ∀ v, Monotone (R.now v)
  cut_mono : ∀ v, Monotone (R.cut v)
  ready_point : rho.ExecutionValid → ∀ c, 0 ≤ c → ∀ v i, i ≤ rho.events.length →
    rho.point.Ready (c + 1) v (rho.cutTime i) →
    ReadyReadPoint M.trace M.honest rho.horizon c (M.validator.symm v) (R.cut v i)
        (R.now v i) ∧
      ReadBoundary M.trace (M.validator.symm v) (R.cut v i) ∧ rho.cutTime i - 1 ≤ R.now v i
  end_read : rho.ExecutionValid → ∀ c, 0 ≤ c → ∀ v t, 0 ≤ t → t ≤ rho.horizon →
    rho.point.Ready c v t →
    R.now v ((chainTrace rho).endCut t) = t ∧
      t < M.trace.time (M.cut ((chainTrace rho).endCut t)) ∧
      ReadyReadPoint M.trace M.honest rho.horizon c (M.validator.symm v)
        (M.cut ((chainTrace rho).endCut t)) t ∧
      ReadBoundary M.trace (M.validator.symm v) (M.cut ((chainTrace rho).endCut t))

/-- OPEN local block ancestry at two actual reads. Source shape is
Healthy/CutTips.healthy_cut_tips_ancestor_at at E1; its concrete query, actual
ready→heal progress, both ready reads, ordered cuts and later stored-now bound
are retained below. NEW UNRESOLVED SUFFICIENCY TARGET for arbitrary M/R;
StoredReadTransport binds the tips to the outputs, not this ancestry.
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
