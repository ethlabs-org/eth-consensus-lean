module
public import ConsensusShape.Run

@[expose] public section

/-! # Shape claims (layer 1)

What a shape family proves about its compiled runs, for a contract `K` over
progress requirements: structural obligations (well-formedness, positive
catch-up, provided ⇔ specified, mandatory parts, `sync` in every liveness and
recovery premise), output validity, nesting and final monotonicity of the
chains, and per capability the chain-level forms of the layer-0 claims:
safety, `ProposalLive` (instead of transaction liveness), local
accountability, resilience and recovery. `refinement` turns these into
`ProblemClaims`. `ShapeClaims` is not a non-vacuity certificate (D-24): it is
paired with `Contract.Realizable`. There is no `honestNeverSlashed` field:
non-framing is a layer-½ theorem. -/

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

/-- "X, or an observed hash collision, or (if the escape is `some α`) the run
is globally slashable for `α`" on a compiled run. -/
def Escaped {F : ShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (esc : Option ℚ) (X : Prop) (rho : Model.Run (compiled F) E) : Prop :=
  X ∨ rho.HashCollision ∨ ∃ α, esc = some α ∧ (sysOf O (compiled F) V).GloballySlashable α ⟨E, rho⟩

/-- The chain-level claims for one capability served by output `g` with
spec `s`. -/
structure ShapeCapClaims (F : ShapeFamily O Info) (K : Contract O ProgressReq) (g : O.Id)
    (s : CapSpec ProgressReq K.Idx) : Prop where
  /-- Safety of the chain from time 0 (or escape). -/
  safe : AllRuns F fun _ rho => ∀ σ, rho.ExecutionValid → ShapePremise K s.safety.premise σ rho →
    Escaped s.safety.escape ((chainTrace rho).Safe g 0) rho
  /-- Proposal liveness (D-14). -/
  live : AllRuns F fun E rho => ∀ i σ, rho.ExecutionValid →
    ShapePremise K (s.live.premise i) σ rho →
    ProposalLive rho (((K.catchUp : Nat) : Time) * E.Δ) g ((s.live.start i).eval rho.point σ)
      (s.live.latency i) ∨ rho.HashCollision
  /-- Local accountability: conflicting honest reads convict `α` from their own
  views. -/
  accountable : ∀ α, s.accountable = some α → AllRuns F fun _ rho => rho.ExecutionValid →
    (chainTrace rho).AccountablySafe rho.ViewIdx rho.Slashable α g 0 ∨ rho.HashCollision
  /-- Resilience: parameters `σ 0 = T`, `σ 1 = b₀`. -/
  resilient : ∀ P, s.resilience = some P → AllRuns F fun E rho => ∀ σ, rho.ExecutionValid →
    ShapePremise K P σ rho →
    (chainTrace rho).ProtectedThrough (((K.catchUp : Nat) : Time) * E.Δ) g (resilienceTarget O g)
      (σ 0) (σ 1) ∨ rho.HashCollision
  /-- Recovery, safety half (or escape). -/
  recoverySafe : ∀ R, s.recovery = some R → AllRuns F fun E rho => ∀ i σ, rho.ExecutionValid →
    ShapePremise K (R.premise i) σ rho →
    Escaped R.escape ((chainTrace rho).ReadySafe (((K.catchUp : Nat) : Time) * E.Δ) g
      ((R.start i).eval rho.point σ)) rho
  /-- Recovery, liveness half. -/
  recoveryLive : ∀ R, s.recovery = some R → AllRuns F fun E rho => ∀ i σ, rho.ExecutionValid →
    ShapePremise K (R.premise i) σ rho →
    ProposalLive rho (((K.catchUp : Nat) : Time) * E.Δ) g ((R.start i).eval rho.point σ)
      (R.latency i) ∨ rho.HashCollision

/-- The shape's headline: structural obligations plus per-capability claims.
Not a non-vacuity certificate (D-24): pair it with `Contract.Realizable`. -/
structure ShapeClaims (F : ShapeFamily O Info) (K : Contract O ProgressReq) : Prop where
  /-- The contract is structurally well-formed (D-8). -/
  wf : K.WellFormed
  /-- Readers catch up for at least one `Δ` (used by the transaction bridge). -/
  catchUp_pos : 0 < K.catchUp
  /-- A capability is provided exactly when it is specified (D-7). -/
  provided : ∀ c, (O.output c).isSome = (K.spec c).isSome
  /-- Every spec has its mandatory parts (D-6). -/
  complete : ∀ c s, K.spec c = some s → s.Complete c
  /-- D-20: liveness and recovery premises contain `sync`. -/
  liveSync : ∀ c s, K.spec c = some s → ∀ i, (s.live.premise i).HasSync ∧
    ∀ R, s.recovery = some R → (R.premise i).HasSync
  /-- Every provided output is valid in every valid run. -/
  outputValid : AllRuns F fun _ rho => rho.ExecutionValid →
    ∀ c g, O.output c = some g → OutputValid rho g
  /-- Lower-rank chains are prefixes of higher-rank ones. -/
  nested : ∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank → O.output c₁ = some g₁ → O.output c₂ = some g₂ →
    AllRuns F fun _ rho => rho.ExecutionValid → (chainTrace rho).Nested g₁ g₂
  /-- The final chain never rolls back. -/
  finalMonotone : ∀ g, O.output .final = some g →
    AllRuns F fun _ rho => rho.ExecutionValid → (chainTrace rho).Monotone g 0
  /-- The claims of every provided capability. -/
  caps : ∀ c g s, O.output c = some g → K.spec c = some s → ShapeCapClaims F K g s

end Consensus.Shape

end
