module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Service
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Growing-fault sleepy queries: the serviced proposal

The sleepy suppliers of `Obligations/NonfinalSuppliers` for a `ConfirmedQueryAt` in the sleepy
regime, on the canonical growing trace:

* `sleepyOn_of_duration`: a shorter readiness duration keeps the sleepy participation;
* `sleepy_query_sync_at`: the finite service through the deadline from raw synchrony;
* `sleepy_query_bounds_at`: the two count shapes through the deadline from the L0 budget at the
  contract's look-ahead `5Δ`;
* `sleepy_query_producer_at`, `SleepyProposalServiceAt`, `sleepy_serviced_proposal_supply_at`: a
  proposal of the selected slot, its proposer ready at the slot time and still honest `Δ` later;
* `sleepy_serviced_proposal_coverage_at`: that proposal is in every ready read at the deadline. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation Obligations
open Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Shortening the readiness duration preserves sleepy participation. -/
theorem sleepyOn_of_duration (p : EnvPoint V) {c d W a b : Time} (hcd : c ≤ d)
    (h : p.SleepyOn (1 / 2) d W a b) : p.SleepyOn (1 / 2) c W a b :=
  fun t hat htb => half_ready_of_duration V _ hcd (h t hat htb)

/-- The finite sleepy service through the query deadline. -/
theorem sleepy_query_sync_at (Q : ConfirmedQueryAt S A V)
    (hsleepy : (Sys (goldilocks S) V).Sleepy (K S A) Q.run) :
    Compose.Growing.SleepyServiceBefore Q.trace Q.keys Q.params.Δ Q.deadline :=
  sleepyServiceBefore_of_syncUntil_at S Q.run.2 Q.hn Q.valid
    (noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision) Q.bounded
    (sleepy_raw_syncUntil S A V Q.run Q.valid hsleepy Q.deadline)

/-- The two sleepy count shapes through the query deadline. -/
theorem sleepy_query_bounds_at (Q : ConfirmedQueryAt S A V)
    (hsleepy : (Sys (goldilocks S) V).Sleepy (K S A) Q.run) :
    Compose.Growing.SleepyBoundsFrom Q.trace Q.keys 0 Q.deadline :=
  sleepy_bounds_at S Q.run.2 Q.hn Q.valid Q.bounded (fun t ht htb =>
    sleepyOn_of_duration V _ (confirmed_duration_supply_at S A V Q) hsleepy.2 t ht
      (htb.trans Q.bounded))
    (add_nonneg (Compose.Growing.ts_natCast_nonneg 0) Q.params.toParams.hΔ.le) (le_max_right _ _)

/-- Service inputs of the sleepy inclusion consumer for a confirmed proposal. These are supplier
conclusions, never additional assumptions of the endpoint. -/
structure SleepyProposalServiceAt (Q : ConfirmedQueryAt S A V)
    (P : ConfirmedProposalAt Q) : Prop where
  nonnegative : 0 ≤ Q.trace.time P.cut
  margin : Q.trace.time P.cut + 6 * Q.params.Δ ≤ Q.deadline
  duration : Regimes.catchUp Q.params ≤ Q.duration
  hold : P.block.proposer ∈ Q.keys (Q.trace.time P.cut + Regimes.Growing.hold Q.params)
  sync : Compose.Growing.SleepyServiceBefore Q.trace Q.keys Q.params.Δ Q.deadline
  bounds : Compose.Growing.SleepyBoundsFrom Q.trace Q.keys 0 Q.deadline

/-- Actual production from the selected slot: the canonical proposal event and its own
acceptance, with the proposer's hold, for progress from a readiness start `ready ≤ query`. -/
theorem sleepy_query_producer_at (Q : ConfirmedQueryAt S A V) {ready : Time}
    (hprogress : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A)
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

/-- A confirmed proposal with its sleepy service inputs. -/
theorem sleepy_serviced_proposal_supply_at (Q : ConfirmedQueryAt S A V)
    (hsleepy : (Sys (goldilocks S) V).Sleepy (K S A) Q.run)
    (hprogress : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A)
      Q.cap Q.index 0 Q.run.2.horizon Q.run)
    (hquery : 0 ≤ Q.query) :
    ∃ P : ConfirmedProposalAt Q, SleepyProposalServiceAt S A V Q P := by
  obtain ⟨P, hm, hh⟩ := sleepy_query_producer_at S A V Q hprogress (by simpa using hquery)
  exact ⟨P, ⟨hquery.trans P.fresh.le, hm, confirmed_duration_supply_at S A V Q, hh,
    sleepy_query_sync_at S A V Q hsleepy, sleepy_query_bounds_at S A V Q hsleepy⟩⟩

/-- Coverage of a serviced proposal: it is in every ready read at the deadline (finite sleepy
inclusion through the deadline). -/
theorem sleepy_serviced_proposal_coverage_at (Q : ConfirmedQueryAt S A V)
    (P : ConfirmedProposalAt Q) (W : SleepyProposalServiceAt S A V Q P) :
    ∀ y j, Regimes.Growing.ReadyAt Q.trace Q.keys Q.duration y Q.deadline →
      Regimes.CutAfter Q.trace j Q.deadline →
      Anc (Q.trace.HonestBlocksAt Q.keys) P.block (Regimes.readAfter Q.trace y j Q.deadline) := by
  intro y j hy hj
  exact sleepy_include_finite_at S Q.run.2 Q.hn Q.valid
    (noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision)
    (W.nonnegative.trans P.bounded) W.sync W.bounds
    ⟨P.block.proposer, P.cut, confirmed_ready_mono_at S A V Q W.duration P.ready, W.hold,
      P.proposal, rfl⟩ W.margin le_rfl
    (confirmed_ready_mono_at S A V Q W.duration hy) hj

end Consensus.Goldilocks.Obligations.Growing

end
