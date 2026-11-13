module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Query
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Reader
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.S5Step
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage engine part under growing faults: the repair of a ready reader's read

`outage_protected_at`, the growing-fault form of `Obligations/OutageRepair`: from the recovery
point, the confirmed read of every source ready at `T` is a prefix of the read of every reader
ready at `t`. The source is armed (`outage_arming_at`); the lock module's premise package and
invariant come from the arming (`outageLockPremises_of_arming_at`, `outage_lock_inv_at` with the
restored-vote step `outage_s5_step_at`); the reader reads above the armed read tip
(`outage_reader_bridge_at`), and ancestry of the two read tips is the engine read prefix
(`outage_reader_prefix_at`). -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Blocks Shape

variable {S : BoundSetup} {A : ContractAssumptions S.toSetup} {V : Type} [Fintype V] [DecidableEq V]

/-- **Slow-only recovery for ready readers under growing faults**: from the recovery point, the
read of every source ready at `T` is a prefix of the read of every reader ready at `t`. -/
theorem outage_protected_at (Q : OutageQueryAt S A V) :
    (chainTrace Q.run.2).ProtectedReadyFrom Q.duration .confirmed
      (resilienceTarget schema .confirmed) Q.T
      ((Sys (goldilocksWith S) V).recoveryAt (K S.toSetup A) Q.stop Q.run) := by
  intro v hv t ht hth w hw
  have hTs : Q.T ≤ Q.start := by
    obtain ⟨-, hlag, -, -⟩ := Q.outage.times
    have : (0 : Time) ≤ ((K S.toSetup A).params.lag : Time) * Q.run.1.ΔAC := by
      have := Q.run.1.ΔAC_pos; positivity
    change Q.T + _ * Q.run.1.ΔAC ≤ Q.start at hlag
    linarith
  have hst : Q.start ≤ Q.stop := Q.outage.times.2.2.1
  have hrec : Q.stop ≤ t := by
    have : (0 : Time) ≤ ((K S.toSetup A).params.recovery : Time) * Q.run.1.ΔAC := by
      have := Q.run.1.ΔAC_pos; positivity
    change Q.stop + _ * Q.run.1.ΔAC ≤ t at ht
    linarith
  have hsh : Q.start ≤ Q.run.2.horizon := hst.trans (hrec.trans hth)
  have hTh : Q.T ≤ Q.run.2.horizon := hTs.trans hsh
  have service := outage_pre_service_at Q
  obtain ⟨ar⟩ := outage_arming_at Q service v hv hTh
  have hSD : ∀ y, Compose.Growing.ReceiverServiceAfterAt Q.keys (Q.trace.HonestBlocksAt Q.keys)
      (outageLockPremises_of_arming_at Q service hsh ar).b₁ y Q.trace.projAC := fun y => by
    rw [outageLockPremises_of_arming_at_b₁]
    exact outage_receiver_service_at Q y
  have hinv := Compose.Growing.outage_lock_inv_at _ (Compose.Growing.outage_s5_step_at _ hSD)
  refine outage_reader_prefix_at Q hv (hTs.trans (hst.trans hrec)) hth hw ?_
  rw [← ar.tip_eq]
  exact outage_reader_bridge_at Q service hsh ar hinv ht hth hw

end Consensus.Goldilocks.Obligations.Growing

end
