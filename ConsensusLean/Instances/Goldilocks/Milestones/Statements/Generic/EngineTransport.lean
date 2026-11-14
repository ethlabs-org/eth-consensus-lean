module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.EngineRepresentation
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Healing

@[expose] public section

set_option autoImplicit false
namespace Consensus.Goldilocks.Generic
open Shape Blocks Generic
variable {P : Params} {A : NodeAC P} {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V}

variable {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}
structure GrowingRunTransport (M : RunMap rho payload) : Prop where
  local_run : rho.ExecutionValid →
    Growing.LocalRun M.proposer M.digest M.honest M.signer M.trace
  no_collision : rho.ExecutionValid → ¬ rho.HashCollision → Compose.NoCollRun M.digest M.trace

structure PrefixTransport (M : RunMap rho payload) : Prop where
  reader : rho.ExecutionValid → ∀ i, i ≤ rho.events.length →
    Node.LocalRun M.proposer M.digest (M.honest (rho.cutTime i)) M.signer
      (M.trace.upTo (rho.cutTime i))
  state : ∀ i, i ≤ rho.events.length → ∀ y,
    (M.trace.upTo (rho.cutTime i)).state y (M.cut i) = M.trace.state y (M.cut i)
  no_collision : ∀ d, Compose.NoCollRun M.digest M.trace →
    Compose.NoCollRun M.digest (M.trace.upTo d)

structure ServiceTransport (M : RunMap rho payload) : Prop where
  sync : rho.ExecutionValid → ¬ rho.HashCollision → ∀ b,
    rho.log.SyncUntil rho.point b →
    M.trace.SyncRunAt M.honest E.ΔFG 0 (b - P.Δ)
  gst : rho.ExecutionValid → ¬ rho.HashCollision → ∀ g, rho.log.PSync rho.point g →
    M.trace.GSTRunAt M.honest E.ΔFG g

structure RegimeTransport (M : RunMap rho payload) (K : Contract ProgressReq)
    (look : Time) : Prop where
  sleepy : rho.ExecutionValid → ¬ rho.HashCollision → (Sys F V).Sleepy K ⟨E, rho⟩ →
    M.trace.SleepyPrefixAt M.honest E.ΔFG look rho.horizon
  healthy : rho.ExecutionValid → ¬ rho.HashCollision → ∀ g,
    (Sys F V).Healthy K g ⟨E, rho⟩ →
    M.trace.GSTRunAt M.honest E.ΔFG g ∧
    (∀ y t, max g 0 ≤ t → t ≤ rho.horizon → y ∈ M.honest t → M.trace.awake y t) ∧
    (∀ t, 0 ≤ t → t ≤ rho.horizon → 3 * (M.honest t)ᶜ.ncard ≤ P.n - 1)
  ready : ∀ c v i, i ≤ rho.events.length → rho.point.Ready c v (rho.cutTime i) →
    ReadyRead M c (M.validator.symm v) (M.cut i) (rho.cutTime i)

structure ProposalProgressTransport (M : RunMap rho payload) (K : Contract ProgressReq)
    (healing : ACHealing A M.signer)
    (catchUp hold margin : Time) : Prop where
  sleepy : rho.ExecutionValid → ∀ cap idx t,
    (cap = .available ∨ cap = .stable) → (Sys F V).Sleepy K ⟨E, rho⟩ →
    (Sys F V).prog (shapeProgress F V) K cap idx 0 rho.horizon ⟨E, rho⟩ →
    0 ≤ t → t + (K.params.latency cap idx : Time) * E.ΔAC ≤ rho.horizon →
    (∃ v, rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) v
      (t + (K.params.latency cap idx : Time) * E.ΔAC)) →
    ∃ B k, t < M.trace.time k ∧ ReadyProposal M.trace M.honest catchUp hold B k ∧
      M.trace.time k + margin ≤ t + (K.params.latency cap idx : Time) * E.ΔAC
  healthy : rho.ExecutionValid → ∀ cap idx gst t,
    (cap = .available ∨ cap = .stable) →
    (Sys F V).Healthy K gst ⟨E, rho⟩ →
    (Sys F V).prog (shapeProgress F V) K cap idx ((Sys F V).ready K gst ⟨E, rho⟩)
      rho.horizon ⟨E, rho⟩ →
    (Sys F V).heal K cap idx gst ⟨E, rho⟩ ≤ t →
    t + (K.params.latency cap idx : Time) * E.ΔAC ≤ rho.horizon →
    (∃ v, rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) v
      (t + (K.params.latency cap idx : Time) * E.ΔAC)) →
    ∃ B k, t < M.trace.time k ∧ ReadyProposal M.trace M.honest catchUp hold B k ∧
      M.trace.time k + margin ≤ t + (K.params.latency cap idx : Time) * E.ΔAC
  healing_gap : rho.ExecutionValid → ∀ cap idx gst (recurrence : Recurrence),
    (cap = .available ∨ cap = .stable) → (Sys F V).Healthy K gst ⟨E, rho⟩ →
    K.progress cap idx = .recur recurrence → recurrence.pattern = Pattern.single →
    (Sys F V).prog (shapeProgress F V) K cap idx ((Sys F V).ready K gst ⟨E, rho⟩)
      ((Sys F V).heal K cap idx gst ⟨E, rho⟩) ⟨E, rho⟩ →
    ∀ a b, (Sys F V).ready K gst ⟨E, rho⟩ ≤ P.slotTime a →
    a + resetSlots healing.warmup (recurrence.gap : Nat) P.δt ≤ b + 1 →
    P.slotTime b + 2 * P.Δ ≤ (Sys F V).heal K cap idx gst ⟨E, rho⟩ →
    ProposalGap M.trace M.honest M.proposer (recurrence.gap : Nat) a b
  proposal : ∀ B k, M.trace.ProposesAt B.proposer k B →
    B.proposer ∈ M.honest (M.trace.time k) →
    Shape.HonestProposal rho (M.trace.time k) (M.keyIndex B.proposer) (M.header B)

structure OutagePolicy (M : RunMap rho payload) where
  point : EnvPoint (Fin P.n)
  committee : Time → Finset (Fin P.n)
  binding : RunPointBinding M.trace M.honest point
  horizon : point.horizon = rho.horizon

structure OutageTransport (M : RunMap rho payload) (D : OutagePolicy M)
    (K : Contract ProgressReq) (catchUp look : Time) : Prop where
  participation : rho.ExecutionValid → ∀ T b₀ b₁,
    (Sys F V).Outage (shapeProgress F V).toExternal K T b₀ b₁ ⟨E, rho⟩ →
    D.point.EtaSleepyOn (1 / 2) ((K.params.η : Time) * E.ΔAC)
      (max catchUp ((K.params.η : Time) * E.ΔAC - 1))
      ((Sys F V).aheadDur K ⟨E, rho⟩) 0 D.point.horizon ∧
    ∀ δ, 0 ≤ δ → δ ≤ (K.params.η : Time) * E.ΔAC →
      D.point.CommitteeSleepyOn (fun t => D.committee (max 0 (t - δ))) (1 / 2)
        ((K.params.η : Time) * E.ΔAC) (max catchUp ((K.params.η : Time) * E.ΔAC - 1))
        look 0 D.point.horizon

def CarrierProcessed (M : RunMap rho payload) (B : A.Blk) (y : Fin P.n)
    (j : Nat) (sent deadline : Time) : Prop :=
  ∃ k < j, y ∈ M.honest (M.trace.time k) ∧ sent ≤ M.trace.time k ∧
    M.trace.time k ≤ deadline ∧ M.trace.BlockCallAt y k B

end Consensus.Goldilocks.Generic
