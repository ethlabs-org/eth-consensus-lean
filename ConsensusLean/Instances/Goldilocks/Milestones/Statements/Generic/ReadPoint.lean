module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.CorrectLocal
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.EngineRepresentation

@[expose] public section

/-! # Explicit-time local reads

The state index and evaluation time are independent. These contracts supply no evidence
and create no cut. In particular, honesty is never required at the next trace cut.
Source: Run/Model.confirmedAt; Growing/Simulation/Endpoint/Outputs.prefix_reader_at,
engine_outputValid_at and engine_nested_at; lead LeadHeldInView and LeadTipsValid.
-/

namespace Consensus.Goldilocks.Generic

open SA (gbar)
open Healing.Growing (IsReset)

variable {P : Params} {A : NodeAC P}

/-- Source: Regimes/Sleepy.ReadPoint. No equality with the next cut time is asserted. -/
def ReadPointAt (tr : RunTrace A) (i : Nat) (t : Time) : Prop :=
  (∀ k < i, tr.time k ≤ t) ∧ t ≤ tr.time i

/-- Source: Regimes/Sleepy.Boundary. Engine reads do not observe an intermediate own call. -/
def ReadBoundary (tr : RunTrace A) (y : Fin P.n) (i : Nat) : Prop :=
  tr.IsCall y i → tr.pos i = 0

/-- Source: lead LeadHeldInView. Honesty and finite bounds refer only to the actual read. -/
def HonestReadPoint (tr : RunTrace A) (H : Time → Set (Fin P.n)) (b : Time)
    (y : Fin P.n) (i : Nat) (t : Time) : Prop :=
  y ∈ H t ∧ ReadPointAt tr i t ∧ 0 ≤ t ∧ t ≤ b

/-- Source: E1 ReadyRead and Regimes/Sleepy.ReadyAt; no future awake interval. -/
def ReadyReadPoint (tr : RunTrace A) (H : Time → Set (Fin P.n)) (b c : Time)
    (y : Fin P.n) (i : Nat) (t : Time) : Prop :=
  HonestReadPoint tr H b y i t ∧
    ∀ u, max 0 (t - c - 1) ≤ u → u ≤ t → tr.awake y u

/-- Source: Run/Model.confirmedAt, with its time argument made explicit. -/
noncomputable def confirmedRead (tr : RunTrace A) (y : Fin P.n) (i : Nat)
    (t : Time) : A.Blk := A.confirmed (tr.state y i).ac (Node.frame (tr.state y i)) t

/-- Source: Run/Model.headAt, with its time argument made explicit. -/
noncomputable def headRead (tr : RunTrace A) (y : Fin P.n) (i : Nat)
    (t : Time) : A.Blk := A.head (tr.state y i).ac (Node.frame (tr.state y i)) t

/-- L1/L2 targets at the engine read time. No collision or regime premise is added.
Sources: CorrectLocal.tipsValid; lead LeadTipsValid/LeadHeldInView;
Growing/Simulation/Endpoint/Outputs.engine_outputValid_at and engine_nested_at.
The held-tree-to-view, root, chain and codec suppliers remain separate E1 contracts. -/
structure LocalReadPoint {sg : A.Msg → Fin P.n} (C : ACCorrectLocal A sg) : Prop where
  tips : ∀ cm proposer dg H (tr : RunTrace A),
    C.run.Run cm proposer dg H tr → ∀ b y i t,
    HonestReadPoint tr H b y i t →
      confirmedRead tr y i t ∈ (Node.frame (tr.state y i)).tree ∧
      (Node.frame (tr.state y i)).Anc (tr.finalizedAt y i) (confirmedRead tr y i t) ∧
      (Node.frame (tr.state y i)).Anc (confirmedRead tr y i t) (headRead tr y i t)
  held : ∀ cm proposer dg H (tr : RunTrace A),
    C.run.Run cm proposer dg H tr → ∀ b y i t,
    HonestReadPoint tr H b y i t → confirmedRead tr y i t ∈ (tr.state y i).fg.tree

/-- L6/L7 use the shared finite healthy regime, never an all-future schedule. -/
structure HealthyReadPoint {sg : A.Msg → Fin P.n} (C : ACCorrectLocal A sg) : Prop where
  /-- L6: healed agreement requires an honest opening proposal; reads use actual times. -/
  healed : ∀ cm βK proposer dg H (tr : RunTrace A) ΔF g a b s₁,
    βK ≤ 1 / 2 →
    C.run.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b →
    IsReset tr H g a → a ≤ b → P.slotOf a + C.healing.drain ≤ s₁ →
    HealedFrom tr H proposer s₁ b →
    max g 0 ≤ P.slotTime s₁ →
    ((∃ z k X, HonestProposal tr H proposer s₁ z k X) →
      P.slotTime s₁ + 6 * P.Δ ≤ b → gbar g + 4 * P.Δ ≤ P.slotTime s₁ →
      ∀ y z i j t u, P.slotTime s₁ + C.margin < t →
      P.slotTime s₁ + C.margin < u →
      ReadyReadPoint tr H b C.catchUp y i t → ReadyReadPoint tr H b C.catchUp z j u →
      ReadBoundary tr y i → ReadBoundary tr z j →
      Compatible (tr.HonestBlocksAt H) (confirmedRead tr y i t) (confirmedRead tr z j u)) ∧
    ∀ z k X, HonestProposal tr H proposer s₁ z k X → 0 ≤ tr.time k → tr.time k ≤ b →
      ∀ y j t, tr.time k + C.margin ≤ t → ReadyReadPoint tr H b C.catchUp y j t →
      ReadBoundary tr y j → t < tr.time j →
      Anc (tr.HonestBlocksAt H) X (confirmedRead tr y j t)
  /-- L7: a ready proposal after the reset drain is confirmed within the latency. -/
  proposal : ∀ cm βK proposer dg H (tr : RunTrace A) ΔF g a b healed,
    βK ≤ 1 / 2 →
    C.run.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF b →
    IsReset tr H g a → a ≤ b → max g 0 + C.margin ≤ healed →
    ∀ B k y j t, ReadyProposal tr H C.catchUp C.hold B k →
    P.slotOf a + C.healing.drain ≤ B.slot → gbar g + 4 * P.Δ ≤ P.slotTime B.slot →
    0 ≤ tr.time k → tr.time k ≤ b → tr.time k + C.hold ≤ b → healed ≤ tr.time k →
    tr.time k + C.latency ≤ t → ReadyReadPoint tr H b C.catchUp y j t →
    ReadBoundary tr y j → t < tr.time j →
    Anc (tr.HonestBlocksAt H) B (confirmedRead tr y j t)

/-- L9 preserves the actual source and destination reads under the fixed outage policy.
Population and committee look-aheads are independent. Reads remain non-strict.
Certificate: cert obligation open: OC-K. -/
structure OutageReadPoint {sg : A.Msg → Fin P.n} (C : ACCorrectLocal A sg) : Prop where
  protection : ∀ cm proposer dg H (tr : RunTrace A) (p : EnvPoint (Fin P.n))
    ΔF T b₀ b₁ recoveryTime,
    C.run.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    RunPointBinding tr H p → 0 ≤ T → T + C.outageLag ≤ b₀ →
    b₀ ≤ b₁ → b₁ ≤ b₀ + C.outageBudget → b₁ ≤ recoveryTime →
    b₁ + C.recovery ≤ recoveryTime →
    ACServiceBefore C tr H ΔF b₀ → tr.GSTRunAt H ΔF b₁ →
    p.EtaSleepyOn C.θ C.outageEta (max C.catchUp (C.outageEta - 1)) C.look 0 p.horizon →
    (∀ δ, 0 ≤ δ → δ ≤ C.outageEta →
      p.CommitteeSleepyOn (fun t => cm (max 0 (t - δ))) C.θ C.outageEta
        (max C.catchUp (C.outageEta - 1)) C.committeeLook 0 p.horizon) → ∀ x i y j t,
    ReadyReadPoint tr H p.horizon C.catchUp x i T → ReadBoundary tr x i →
    recoveryTime ≤ t → ReadyReadPoint tr H p.horizon C.catchUp y j t →
    ReadBoundary tr y j →
      Anc (tr.HonestBlocksAt H) (confirmedRead tr x i T) (confirmedRead tr y j t)

section Engine

open Shape Blocks

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V} {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}

/-- The actual mapped cut is a read boundary at the engine time. Source:
Growing/Simulation/Endpoint/Outputs.cutMap_time_le and prefix_reader_at.
This is an open map supplier, not a new cut or a future-honesty assumption. -/
structure EngineReadPoint (M : RunMap rho payload) : Prop where
  honest : rho.ExecutionValid → ∀ v i, i ≤ rho.events.length →
    rho.point.HonestAt v (rho.cutTime i) →
    HonestReadPoint M.trace M.honest rho.horizon (M.validator.symm v) (M.cut i)
      (rho.cutTime i)
  boundary : rho.ExecutionValid → ∀ v i, i ≤ rho.events.length →
    rho.point.HonestAt v (rho.cutTime i) →
    ReadBoundary M.trace (M.validator.symm v) (M.cut i)
  ready : ∀ c y i t, ReadyRead M c y i t →
    ReadyReadPoint M.trace M.honest rho.horizon c y i t

end Engine

end Consensus.Goldilocks.Generic

end
