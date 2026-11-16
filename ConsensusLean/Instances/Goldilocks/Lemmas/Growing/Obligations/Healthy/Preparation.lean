module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl

public section

/-! # Healthy preparation under growing faults -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- Healthy partial synchrony catches historical acceptances at the first snapshot after GST,
given health through the snapshot node's publication window `[ḡ, ḡ + Δ − 1]`. Both the source and
the receiver use honesty at their own cuts. -/
theorem healthy_repair_catch_at (Q : HealthyPreparationQueryAt S A V)
    (hb : SA.gbar Q.gst + Q.params.Δ ≤ Q.bound) :
    Healing.Growing.CatchRun Q.trace Q.keys Q.gst (2 * Q.params.Δ) := by
  have hnet : Q.run.2.log.PSync Q.run.2.point Q.gst :=
    (Model.sysOf_delivers_iff _ _ _ _).mp Q.healthy.1
  have hb' : max Q.gst 0 + Q.run.1.ΔAC ≤ Q.bound := hb
  exact catchRun_of_psync_at S Q.run.2 Q.hn Q.valid
    (noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision)
    hnet (fun v t ht _ htw hv => Q.healthy.2.1.2 v t ht (by linarith only [htw, hb']) hv)

end Consensus.Goldilocks.Obligations.Growing

end
