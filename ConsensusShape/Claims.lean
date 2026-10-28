module
public import ConsensusShape.Run

@[expose] public section

/-! # Shape claims (L2)

What a shape family proves about its compiled runs, for a contract `K`
(numbers and progress requirements): the chain-level mirror of the L0
behaviour table (`Behaviour`), each claim on every valid run of every
validator set and environment, in the L0 regime (`ShapeSleepy`,
`ShapeHealthy`, `ShapeOutage`, `ShapeProg` are the L0 definitions at the
compiled run), and each "or an observed hash collision":

* always: output validity, nesting, final monotonicity;
* final: local accountability for fraction `α`, and `ProposalLive` from the
  heal point when healthy from a GST with progress from `readyFrom`;
* available and stable: ready-reader safety and `ProposalLive` when sleepy,
  and from the heal point when healthy from a GST (safety needs progress only
  on `[readyFrom, heal]`);
* stable: outage resilience into the resilience target.

`ProposalLive` replaces transaction liveness (the payload bridge,
`proposalLive_txLive`). Prefix forms are not restated: they follow from the
L0 prefix closure (`Good.*_prefix`). Non-framing is an L1 theorem, so there is
no field for it. `refinement` turns these into `Behaviour`. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (pubOf sysOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Encodable Info]

/-- A property of every run of the compiled family, over every finite
validator set and every environment. -/
def AllRuns (F : ShapeFamily O Info)
    (Q : ∀ {V : Type} [Fintype V] [DecidableEq V] (E : Env V), Model.Run (compiled F) E → Prop) :
    Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (E : Env V) (rho : Model.Run (compiled F) E), Q E rho

/-- The chain-level claims of a shape family for contract `K`. -/
structure ShapeClaims (F : ShapeFamily O Info) (K : Contract O ProgressReq) : Prop where
  /-- Every provided output is valid in every valid run. -/
  outputValid : AllRuns F fun _ rho => rho.ExecutionValid →
    ∀ c g, O.output c = some g → OutputValid rho g
  /-- Lower-rank chains are prefixes of higher-rank ones. -/
  nested : ∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank → O.output c₁ = some g₁ → O.output c₂ = some g₂ →
    AllRuns F fun _ rho => rho.ExecutionValid → (chainTrace rho).Nested g₁ g₂
  /-- The final chain never rolls back. -/
  finalMonotone : ∀ g, O.output .final = some g →
    AllRuns F fun _ rho => rho.ExecutionValid → (chainTrace rho).Monotone g 0
  /-- Local accountability of the final chain for fraction `α`, in every
  environment: conflicting honest reads convict `α` from their own views. -/
  finalAccountable : ∀ g, O.output .final = some g → AllRuns F fun _ rho => rho.ExecutionValid →
    (chainTrace rho).AccountablySafe rho.ViewIdx rho.Slashable K.params.α g 0 ∨
      rho.HashCollision
  /-- Final liveness: healthy from `gst` with progress from `readyFrom` to the
  horizon, proposals are included from the heal point. -/
  finalLive : ∀ g, O.output .final = some g → ∀ (i : K.Idx) (gst : Time),
    AllRuns F fun _ rho => rho.ExecutionValid → ShapeHealthy K rho gst →
      ShapeProg K rho .final i (shapeReady K rho gst) rho.horizon →
      ProposalLive rho (shapeC K rho) g (shapeHeal K rho .final i gst)
        (K.params.latency .final i) ∨ rho.HashCollision
  /-- Sleepy safety of an available or stable chain, for ready readers. -/
  sleepySafe : ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
    AllRuns F fun _ rho => rho.ExecutionValid → ShapeSleepy K rho →
      (chainTrace rho).ReadySafe (shapeC K rho) g 0 ∨ rho.HashCollision
  /-- Sleepy liveness, with progress on the whole run. -/
  sleepyLive : ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
    ∀ i : K.Idx, AllRuns F fun _ rho => rho.ExecutionValid → ShapeSleepy K rho →
      ShapeProg K rho cap i 0 rho.horizon →
      ProposalLive rho (shapeC K rho) g 0 (K.params.latency cap i) ∨ rho.HashCollision
  /-- Healed safety: healthy from `gst` with progress on `[readyFrom, heal]`,
  ready readers are safe from the heal point. -/
  healedSafe : ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
    ∀ (i : K.Idx) (gst : Time), AllRuns F fun _ rho => rho.ExecutionValid →
      ShapeHealthy K rho gst →
      ShapeProg K rho cap i (shapeReady K rho gst) (shapeHeal K rho cap i gst) →
      (chainTrace rho).ReadySafe (shapeC K rho) g (shapeHeal K rho cap i gst) ∨ rho.HashCollision
  /-- Healed liveness: healthy from `gst` with progress from `readyFrom` to the
  horizon, proposals are included from the heal point. -/
  healedLive : ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
    ∀ (i : K.Idx) (gst : Time), AllRuns F fun _ rho => rho.ExecutionValid →
      ShapeHealthy K rho gst → ShapeProg K rho cap i (shapeReady K rho gst) rho.horizon →
      ProposalLive rho (shapeC K rho) g (shapeHeal K rho cap i gst) (K.params.latency cap i) ∨
        rho.HashCollision
  /-- Outage resilience of the stable chain, into the resilience target. -/
  persists : ∀ g, O.output .stable = some g → ∀ T b₀ b₁,
    AllRuns F fun _ rho => rho.ExecutionValid → ShapeOutage K rho T b₀ b₁ →
      (chainTrace rho).ProtectedThrough (shapeC K rho) g (resilienceTarget O g) T b₀ b₁ ∨
        rho.HashCollision

end Consensus.Shape

end
