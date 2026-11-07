module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Cuts

public section

/-! # Honest events in the canonical growing trace

Every labelled cut comes from an engine event. Validity's event-local honesty therefore
supplies the exact honesty test at that cut, without a constant-fault premise.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- A labelled growing-trace cut is within the observation horizon. -/
theorem simTraceAt_labelled_time_le (hv : rho.ExecutionValid) {k : Nat}
    (hk : (simTraceAt S rho hn).label k ≠ none) :
    (simTraceAt S rho hn).time k ≤ rho.horizon := by
  rw [simTraceAt_eq] at hk ⊢
  obtain ⟨_, _, ev, _, he, _, _, _, _, ht, _⟩ := simTrace_cut S rho hn hk
  rw [ht]
  exact (hv.in_horizon ev (List.mem_of_getElem? he)).2

/-- Every labelled cut's node is honest at that cut's time. -/
theorem simTraceAt_labelled_honest (hv : rho.ExecutionValid) {k : Nat}
    (hk : (simTraceAt S rho hn).label k ≠ none) :
    (simTraceAt S rho hn).node k ∈ honestKeysAt S rho ((simTraceAt S rho hn).time k) := by
  rw [simTraceAt_eq] at hk ⊢
  obtain ⟨_, _, ev, _, he, _, _, _, hnode, ht, _⟩ := simTrace_cut S rho hn hk
  rw [hnode, ht]
  exact honest_ownKey_at S rho (hv.honest_only ev (List.mem_of_getElem? he))
    (hv.in_horizon ev (List.mem_of_getElem? he)).2

/-- A trace call's node is honest when it runs, even if compromised later. -/
theorem simTraceAt_call_honest (hv : rho.ExecutionValid) {y k c}
    (hc : (simTraceAt S rho hn).CallAt y k c) :
    y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time k) := by
  obtain ⟨hy, hl⟩ := hc
  subst y
  exact simTraceAt_labelled_honest S rho hn hv (by rw [hl]; simp)

end Consensus.Goldilocks.Simulation
