module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.TraceDefs
import ConsensusLean.Lemmas.Model.Constant

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
/-- The honesty map used by `SimulatesAt.run` clamps exactly as the L0 regimes do. -/
theorem honestKeysAt_clamp (t : Time) :
    honestKeysAt S rho (min t rho.horizon) = honestKeysAt S rho t := by
  ext y
  simp only [mem_honestKeysAt_iff, min_assoc, min_self]

omit [DecidableEq V] in
/-- Beyond the observation horizon the trace's honest set stays frozen. -/
theorem honestKeysAt_after_horizon {t : Time} (ht : rho.horizon ≤ t) :
    honestKeysAt S rho t = honestKeysAt S rho rho.horizon := by
  ext y
  simp only [mem_honestKeysAt_iff, min_eq_right ht, min_self]

omit [DecidableEq V] in
/-- Permanent compromise makes the time-indexed honest keys antitone. -/
theorem honestKeysAt_antitone : Antitone (honestKeysAt S rho) := by
  intro s t hst y hy
  rw [mem_honestKeysAt_iff] at hy ⊢
  exact fun hf => hy (rho.faultyAt_mono (min_le_min_right _ hst) hf)

omit [DecidableEq V] in
/-- In constant-fault runs the time-local set is exactly the static honest-key set. -/
theorem honestKeysAt_of_constant (hc : rho.point.ConstantFaults) (t : Time) :
    honestKeysAt S rho t = honestKeys S rho := by
  ext y
  rw [mem_honestKeysAt_iff, mem_honestKeys_iff, rho.faultyAt_eq_zero hc]

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
