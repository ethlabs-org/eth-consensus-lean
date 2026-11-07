module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.ReadPoint
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.State
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Chains
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Cuts
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EngineSteps
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Finite sleepy safety of the engine under growing faults

* `sleepy_safe_finite_at`: ready-reader safety of the canonical growing trace through `b`, from
  the finite service and the two count shapes through `b` (the static `sleepy_safe_finite`
  without a constant-fault premise).
* `sleepy_safe_engine_at`: the engine's confirmed output is `ReadySafe` with catch-up
  `catchUp + 1` under the L0 sleepy budget with look-ahead `5Δ` through the horizon.

An engine reader is read at the read point of `Engine/ReadPoint` (the trace cut after its last
own event, at its stored clock), where `Regimes.Growing.ReadySafeOn` applies; coherence of the
blocks held while honest turns ancestry of the reads into prefixes of the confirmed chains. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation
open Blocks Shape Node
open Consensus.Model (pubOf)


variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **Finite ready-reader safety of the canonical growing trace** through `b ≥ 0`, from the finite
service and the two count shapes through `b`. -/
theorem sleepy_safe_finite_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn)) {b : Time} (hb0 : 0 ≤ b)
    (hsync : Compose.Growing.SleepyServiceBefore (simTraceAt S rho hn) (honestKeysAt S rho)
      (S.params (pubOf E) hn).Δ b)
    (hB : Compose.Growing.SleepyBounds (simTraceAt S rho hn) (honestKeysAt S rho) b) :
    Regimes.Growing.ReadySafeOn (simTraceAt S rho hn) (honestKeysAt S rho)
      (Regimes.catchUp (S.params (pubOf E) hn)) 0 b :=
  Regimes.Growing.sleepy_safe_at (simTraceAt_goldilocksRun S rho hn hv) hnc hb0 hsync hB

/-- **Finite safety of the engine's confirmed output under growing faults.** Under the finite
service and the L0 sleepy budget with look-ahead `5Δ` through the horizon, the confirmed reads of
nodes ready with catch-up `catchUp + 1` at their engine cuts agree, and each such node's reads
only extend. No constant-fault premise: each reader is honest at its own engine cut. -/
theorem sleepy_safe_engine_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    (hsync : Compose.Growing.SleepyServiceBefore (simTraceAt S rho hn) (honestKeysAt S rho)
      (S.params (pubOf E) hn).Δ rho.horizon)
    (hhalf : rho.point.SleepyOn (1 / 2) (Regimes.catchUp (S.params (pubOf E) hn))
      (5 * (S.params (pubOf E) hn).Δ) 0 rho.horizon) :
    (chainTrace rho).ReadySafe (Regimes.catchUp (S.params (pubOf E) hn) + 1) .confirmed 0 := by
  have hc0 : 0 ≤ Regimes.catchUp (S.params (pubOf E) hn) := by
    unfold Regimes.catchUp
    linarith [(S.params (pubOf E) hn).toParams.hΔ]
  have hsafe := sleepy_safe_finite_at S rho hn hv hnc hv.horizon_nonneg hsync
    (sleepy_bounds_at S rho hn hv le_rfl hhalf)
  constructor
  · intro u v i j hi hj hu hv'
    obtain ⟨hrp, h0, hh, hra, hread⟩ := engine_read_point S rho hn hv hc0 hi.1 hu
    obtain ⟨hrp', h0', hh', hra', hread'⟩ := engine_read_point S rho hn hv hc0 hj.1 hv'
    rw [hread, hread']
    rcases hsafe.agree _ _ _ _ _ _ hrp hrp' (cutMap_boundary S rho hn _ _)
        (cutMap_boundary S rho hn _ _) h0 hh h0' hh' hra hra' with hc | hc
    · exact Or.inl (read_prefix S rho hn hv hnc h0 hrp.1 hra.1 h0' hrp'.1 hra'.1 hc)
    · exact Or.inr (read_prefix S rho hn hv hnc h0' hrp'.1 hra'.1 h0 hrp.1 hra.1 hc)
  · intro v i j hi hij hj hvi hvj
    obtain ⟨hrp, h0, hh, hra, hread⟩ := engine_read_point S rho hn hv hc0 hi.1 hvi
    obtain ⟨hrp', h0', hh', hra', hread'⟩ := engine_read_point S rho hn hv hc0 hj.1 hvj
    rw [hread, hread']
    exact read_prefix S rho hn hv hnc h0 hrp.1 hra.1 h0' hrp'.1 hra'.1
      (hsafe.mono _ _ _ _ _ hrp hrp' (cutMap_boundary S rho hn _ _)
        (cutMap_boundary S rho hn _ _) (cutMap_mono S rho hn (lastOwn_mono S rho v hij))
        (now_mono S rho hn hv v hij) h0 hh' hra hra')

end Consensus.Goldilocks.Obligations.Growing

end
