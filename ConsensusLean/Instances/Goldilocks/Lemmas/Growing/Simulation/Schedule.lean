module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSchedule

public section

/-! # Timing and wakefulness of the growing simulation

These properties depend only on the canonical event expansion and execution validity.
Unlike origin and signature laws, they do not require a static honest set.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- Every observation cut, including the unlabelled tail, has nonnegative time. -/
theorem simTraceAt_time_nonneg (hv : rho.ExecutionValid) :
    ∀ i, 0 ≤ (simTraceAt S rho hn).time i := by
  rw [simTraceAt_eq]
  exact simTrace_time_nonneg S rho hn hv

/-- Trace cut times preserve engine event order. -/
theorem simTraceAt_time_mono (hv : rho.ExecutionValid) :
    Monotone (simTraceAt S rho hn).time := by
  rw [simTraceAt_eq]
  exact simTrace_time_mono S rho hn hv

/-- A trace observation in the horizon stays within the engine horizon. -/
theorem simTraceAt_inHorizon_le (hv : rho.ExecutionValid) {t : Time}
    (ht : (simTraceAt S rho hn).InHorizon t) : t ≤ rho.horizon := by
  rw [simTraceAt_eq] at ht
  exact simTrace_inHorizon_le S rho hn hv ht

/-- Wakefulness is exactly environment wakefulness inside the observation horizon. -/
theorem simTraceAt_awake_bounds (y : Fin (Fintype.card V)) (t : Time) :
    (simTraceAt S rho hn).awake y t ↔
      E.awake (rho.key y) t = true ∧ 0 ≤ t ∧ t ≤ rho.horizon := by
  rw [simTraceAt_eq]
  exact awake_iff' S rho hn y t

/-- Awake transport does not need an honesty premise: honesty is classified separately
at each consumer's time. -/
theorem simTraceAt_awake_to (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)}
    {t : Time} (hw : E.awake (rho.key y) t = true) (ht : 0 ≤ t)
    (hh : (simTraceAt S rho hn).InHorizon t) : (simTraceAt S rho hn).awake y t := by
  exact (simTraceAt_awake_bounds S rho hn y t).mpr
    ⟨hw, ht, simTraceAt_inHorizon_le S rho hn hv hh⟩

/-- Every call takes place while its node is awake, without requiring it to remain
honest after that call. -/
theorem simTraceAt_awake_of_call (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} {i : Nat} (hc : (simTraceAt S rho hn).IsCall y i) :
    (simTraceAt S rho hn).awake y ((simTraceAt S rho hn).time i) := by
  obtain ⟨c, hc⟩ := hc
  have hy := simTraceAt_call_honest S rho hn hv hc
  have hy0 : y ∈ honestKeys S rho := by
    rw [mem_honestKeys_iff]
    rw [mem_honestKeysAt_iff] at hy
    intro hf
    exact hy (rho.faultyAt_mono
      (le_min (simTraceAt_time_nonneg S rho hn hv i) hv.horizon_nonneg) hf)
  rw [simTraceAt_eq] at hc ⊢
  exact simTrace_awake_of_call S rho hn hv y hy0 i ⟨c, hc⟩

end Consensus.Goldilocks.Simulation
