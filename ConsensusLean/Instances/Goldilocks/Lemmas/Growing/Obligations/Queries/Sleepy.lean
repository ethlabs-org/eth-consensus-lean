module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Service
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Growing-fault sleepy queries: proposal production

The sleepy suppliers of `Obligations/NonfinalSuppliers` for a `ConfirmedQueryAt` in the sleepy
regime, on the canonical growing trace:

* `sleepyOn_of_duration`: a shorter readiness duration keeps the sleepy participation;
* `sleepy_query_producer_at`: a proposal of the selected slot, its proposer ready at the slot time
  and honest through its hold. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation Obligations
open Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Shortening the readiness duration preserves sleepy participation. -/
theorem sleepyOn_of_duration (p : EnvPoint V) {c d W a b : Time} (hcd : c ≤ d)
    (h : p.SleepyOn (1 / 2) d W a b) : p.SleepyOn (1 / 2) c W a b :=
  fun t hat htb => half_ready_of_duration V _ hcd (h t hat htb)

/-- Actual production from the selected slot: the canonical proposal event and its own
acceptance, with the proposer's hold, for progress from a readiness start `ready ≤ query`. -/
theorem sleepy_query_producer_at (Q : ConfirmedQueryAt S A V) {ready : Time}
    (hprogress : (Sys (goldilocks S) V).prog
      (shapeProgress (goldilocks S) V) (K S A)
      Q.cap Q.index ready Q.run.2.horizon Q.run)
    (hquery : max ready 0 ≤ Q.query) :
    ∃ P : ConfirmedProposalAt Q, Q.trace.time P.cut + 6 * Q.params.Δ ≤ Q.deadline ∧
      P.block.proposer ∈ Q.keys (Q.trace.time P.cut + Regimes.Growing.hold Q.params) := by
  obtain ⟨W⟩ := confirmed_query_slot_at S A V Q hprogress hquery
  obtain ⟨B, k, hp, he, ht⟩ := confirmed_slot_event_at S A V Q W
  have hr : Regimes.Growing.ReadyAt Q.trace Q.keys Q.duration B.proposer (Q.trace.time k) := by
    rw [hp, ht]; exact W.ready
  have hacc := proposal_accepted_at (simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid)
    (noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision) hr.1 he
  have hmargin : Q.trace.time k + 6 * Q.params.Δ ≤ Q.deadline := by
    rw [ht]; exact W.margin
  have hbound : Q.trace.time k ≤ Q.deadline :=
    (le_add_of_nonneg_right (mul_nonneg (by norm_num) Q.params.toParams.hΔ.le)).trans hmargin
  exact ⟨⟨B, k, he, hacc, hr, ht ▸ W.fresh, hbound⟩, hmargin, by rw [hp, ht]; exact W.hold⟩

end Consensus.Goldilocks.Obligations.Growing

end
