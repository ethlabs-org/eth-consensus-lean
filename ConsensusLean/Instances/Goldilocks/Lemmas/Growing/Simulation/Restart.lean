module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Events

public section

/-! # Restarts while honesty is time-indexed

The wake required by validity precedes the observation where the node is honest.
Monotonic compromise therefore supplies precisely the honesty needed at that wake.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- A node honest at the later awake time has restarted since an earlier sleep. -/
theorem simTraceAt_restart_at_wake (hv : rho.ExecutionValid) :
    ∀ y (u v : Time), y ∈ honestKeysAt S rho v → 0 ≤ u → u < v →
      ¬ (simTraceAt S rho hn).awake y u → (simTraceAt S rho hn).awake y v →
        ∃ k, (simTraceAt S rho hn).RestartAt y k ∧ u < (simTraceAt S rho hn).time k ∧
          (simTraceAt S rho hn).time k ≤ v := by
  intro y u v hy hu0 huv hsu hav
  rw [simTraceAt_eq, (simTrace_encoding S rho hn).1] at hsu hav ⊢
  rw [mem_honestKeysAt_iff, ← NodeAsChainShape.CanonicalTrace.mem_honestKeysAt_iff] at hy
  exact NodeAsChainShape.CanonicalTrace.restart_at_wake (traceEncoding S hn) rho hv
    hy hu0 huv hsu hav

/-- The first call after a sleep is the restart required at the intervening wake. -/
theorem simTraceAt_restart_of_sleep (hv : rho.ExecutionValid) :
    ∀ y i (u : Time), y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i) →
      (simTraceAt S rho hn).IsCall y i → 0 ≤ u →
      u < (simTraceAt S rho hn).time i → ¬ (simTraceAt S rho hn).awake y u →
      (∀ j < i, (simTraceAt S rho hn).IsCall y j → (simTraceAt S rho hn).time j < u) →
        (simTraceAt S rho hn).RestartAt y i := by
  intro y i u hy hc hu0 hut hsleep hprev
  simp only [simTraceAt_eq, (simTrace_encoding S rho hn).1] at hy hc hut hsleep hprev ⊢
  rw [mem_honestKeysAt_iff, ← NodeAsChainShape.CanonicalTrace.mem_honestKeysAt_iff] at hy
  exact NodeAsChainShape.CanonicalTrace.restart_of_sleep (traceEncoding S hn) rho hv
    hy hc hu0 hut hsleep hprev

/-- An observed restart has the same preceding sleep as in the canonical static trace.
Only node-local history is used; honesty at the restart implies honesty at zero. -/
theorem simTraceAt_sleep_of_restart (hv : rho.ExecutionValid) :
    ∀ y i, y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i) →
      (simTraceAt S rho hn).RestartAt y i →
      ∃ u : Time, 0 ≤ u ∧ u < (simTraceAt S rho hn).time i ∧
        ¬ (simTraceAt S rho hn).awake y u ∧
        ∀ j < i, (simTraceAt S rho hn).IsCall y j → (simTraceAt S rho hn).time j < u := by
  intro y i hy hr
  have hy0 : y ∈ honestKeys S rho := by
    rw [mem_honestKeys_iff]
    rw [mem_honestKeysAt_iff] at hy
    exact fun hf => hy (rho.faultyAt_mono
      (le_min (simTraceAt_time_nonneg S rho hn hv i) hv.horizon_nonneg) hf)
  rw [simTraceAt_eq] at hr ⊢
  exact simTrace_sleep_of_restart S rho hn hv y hy0 i hr

end Consensus.Goldilocks.Simulation
