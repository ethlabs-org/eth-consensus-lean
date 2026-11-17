module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.TraceDefs

public section

/-! # Time-local engine simulation vocabulary

The canonical trace already records all engine events, independently of the faulty set.
Growing simulation therefore reuses that construction. Honesty is read at the observation
time, clamped to the engine horizon, rather than fixed at time zero.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E)

/-- Keys uncompromised at `t`, with observations beyond the horizon clamped to it. -/
def honestKeysAt (t : Time) : Set (Fin (Fintype.card V)) :=
  {k | rho.key k ∉ rho.faultyAt (min t rho.horizon)}

omit [DecidableEq V] in
/-- Membership reads the engine's faulty set at the clamped observation time. -/
theorem mem_honestKeysAt_iff (t : Time) (y : Fin (Fintype.card V)) :
    y ∈ honestKeysAt S rho t ↔ rho.key y ∉ rho.faultyAt (min t rho.horizon) := by
  rfl

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

/-- Growing simulation uses the same event expansion as static simulation. -/
noncomputable def simTraceAt (hn : 1 ≤ Fintype.card V) :
    GoldilocksTrace (S.params (pubOf E) hn) (S.ro _) := simTrace S rho hn

/-- The growing trace is the canonical engine trace, not a choice of simulation witness. -/
theorem simTraceAt_eq (hn : 1 ≤ Fintype.card V) :
    simTraceAt S rho hn = simTrace S rho hn := by rfl

/-- Growing simulation preserves the canonical horizon-clamped awake predicate. -/
theorem simTraceAt_awake_iff (hn : 1 ≤ Fintype.card V)
    (y : Fin (Fintype.card V)) (t : Time) :
    (simTraceAt S rho hn).awake y t ↔ awakeAt S rho hn y t := by
  rw [simTraceAt_eq, simTrace_awake_iff]

end Consensus.Goldilocks.Simulation
