module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.TraceDefs

public section

/-! # Time-local engine simulation vocabulary

The canonical trace already records all engine events, independently of the faulty set.
Growing simulation therefore reuses that construction. Honesty is read at the observation
time, clamped to the engine horizon, rather than fixed at time zero. The definitions
`honestKeysAt` and `simTraceAt` and their characterising lemmas are untrusted statement
vocabulary in `Results/Spec/CanonicalTrace`, re-exported through `Lemmas/Simulation/TraceDefs`;
this module derives further facts from them.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E)

omit [DecidableEq V] in
/-- Permanent compromise makes the time-indexed honest keys antitone. -/
theorem honestKeysAt_antitone : Antitone (honestKeysAt S rho) := by
  intro s t hst y hy
  rw [mem_honestKeysAt_iff] at hy ⊢
  exact fun hf => hy (rho.faultyAt_mono (min_le_min_right _ hst) hf)

omit [DecidableEq V] in
/-- An engine node honest at an in-horizon time has an honest trace key then. -/
theorem honest_ownKey_at {v : V} {t : Time} (hv : v ∉ rho.faultyAt t)
    (ht : t ≤ rho.horizon) : rho.ownKey v ∈ honestKeysAt S rho t := by
  rw [mem_honestKeysAt_iff, min_eq_left ht]
  simpa only [Model.Run.ownKey, Equiv.apply_symm_apply] using hv

/-- Growing simulation preserves the canonical horizon-clamped awake predicate. -/
theorem simTraceAt_awake_iff (hn : 1 ≤ Fintype.card V)
    (y : Fin (Fintype.card V)) (t : Time) :
    (simTraceAt S rho hn).awake y t ↔ awakeAt S rho hn y t := by
  rw [simTraceAt_eq, simTrace_awake_iff]

end Consensus.Goldilocks.Simulation
