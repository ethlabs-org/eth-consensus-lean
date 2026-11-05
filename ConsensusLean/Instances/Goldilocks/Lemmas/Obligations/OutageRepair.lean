module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageSuppliers
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageArming
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Arming
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageReaderGate
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageBridge
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageS5.Suppliers
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks outage: the repair of a ready reader's read (slow-only recovery)

`outage_repair` and its consumer `outage_protected`, moved unchanged from `OutageSuppliers.lean`
so that the assembly can import the arming, the lock module, the `OutageS5` suppliers and the reader
bridge, which all import `OutageSuppliers.lean`. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation
open Blocks Shape
variable (S : Setup) (A : ContractAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

set_option linter.unusedVariables false in
/-- Slow-only recovery for ready readers from the recovery point `b₁ + recovery·Δe`
(`recovery = 18`): the reader's read extends the ready source's read. The source is armed
(`outage_arming`); the lock module's premise package and invariant come from the arming
(`outageLockPremises_of_arming`, `outage_locks`) with the step `OutageS5Step`
(`outage_s5_step_query`); the reader reads above the armed read tip (`outage_reader_bridge`, with
the suppliers `outage_reader_head`, `outage_reader_early`, `outage_reader_late`), and the ancestry
of the two read tips is the engine read prefix (`outage_reader_prefix`). The armed-read witness
`armed` of `outage_arm` is not needed. -/
theorem outage_repair (Q : OutageQuery S A V)
    (service : Compose.SleepyServiceBefore Q.trace (honestKeys S Q.run.2) Q.params.Δ Q.start)
    (v : V) (hv : Q.run.2.point.Ready Q.duration v Q.T)
    (armed : OutageArmedRead S A V Q v)
    (t : Time) (ht : (Sys (goldilocks S) V).recoveryAt (K S A) Q.stop Q.run ≤ t)
    (hth : t ≤ Q.run.2.horizon)
    (w : V) (reader : Q.run.2.point.Ready Q.duration w t) :
    (chainTrace Q.run.2).readAt .confirmed v Q.T <+:
      (chainTrace Q.run.2).readAt (resilienceTarget schema .confirmed) w t := by
  have hTs : Q.T ≤ Q.start := by
    obtain ⟨⟨-, hlag, -, -⟩, -⟩ := Q.outage
    have : (0 : Time) ≤ ((K S A).params.lag : Time) * Q.run.1.ΔAC := by
      have := Q.run.1.ΔAC_pos; positivity
    change Q.T + _ * Q.run.1.ΔAC ≤ Q.start at hlag
    linarith
  have hst : Q.start ≤ Q.stop := Q.outage.1.2.2.1
  have hrec : Q.stop ≤ t := by
    have : (0 : Time) ≤ ((K S A).params.recovery : Time) * Q.run.1.ΔAC := by
      have := Q.run.1.ΔAC_pos; positivity
    change Q.stop + _ * Q.run.1.ΔAC ≤ t at ht
    linarith
  have hsh : Q.start ≤ Q.run.2.horizon := hst.trans (hrec.trans hth)
  have hTh : Q.T ≤ Q.run.2.horizon := hTs.trans hsh
  obtain ⟨ar⟩ := outage_arming S A V Q service v hv hTh
  have hS5 := outage_s5_step_query Q service hv hTh hsh ar
  refine outage_reader_prefix S A V Q hv (hTs.trans (hst.trans hrec)) hth reader ?_
  rw [← ar.tip_eq]
  exact outage_reader_bridge Q service hv hTh hsh ar hS5 ht hth reader
    (outage_reader_head Q service hv hTh hsh ar hS5 reader)
    (outage_reader_early Q service hv hTh hsh ar hS5 reader)
    (outage_reader_late Q service hv hTh hsh ar hS5 ht hth reader)

/-- Assembly preserves the reader and time quantifiers of persists. -/
theorem outage_protected (Q : OutageQuery S A V) :
    (chainTrace Q.run.2).ProtectedReadyFrom Q.duration .confirmed
      (resilienceTarget schema .confirmed) Q.T
      ((Sys (goldilocks S) V).recoveryAt (K S A) Q.stop Q.run) := by
  intro v hv t ht hth w hw
  have service := outage_pre_service S A V Q
  obtain ⟨armed⟩ := outage_arm S A V Q service v hv
  exact outage_repair S A V Q service v hv armed t ht hth w hw


end Consensus.Goldilocks.Obligations
end
