module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Proposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Inclusion
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Reads
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Inclusion
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NonfinalSuppliers
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.QuerySlot
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Suffix
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Growing-fault confirmed queries: producer slot and payload projection

The confirmed-chain suppliers for a `ConfirmedQueryAt`, on the canonical growing trace:

* `confirmed_ready_mono_at`, `confirmed_duration_supply_at`: readiness at a smaller duration;
* `ConfirmedProducerSlotAt`, `confirmed_query_slot_at`: the recurrence selects a slot whose
  proposer is ready at the slot time and still honest `hold = Δ` later (`HonestReadyIn` reads it
  at `lookAhead Δ`, which `honestKeysAt` also clamps at the horizon);
* `confirmed_slot_event_at`, `proposal_accepted_at`: the slot's actual proposal and its own
  acceptance;
* `confirmed_payload_projection_at`: coverage of a confirmed proposal at every ready read at the
  deadline is the engine payload obligation. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation Obligations
open Blocks Shape

section Node

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- An own proposal of a node honest at its cut is an acceptance, under collision freedom (the
static `proposal_accepted` on the prefix through the cut). -/
theorem proposal_accepted_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {p : Fin sp.n} {k : Nat} (hp : p ∈ H (tr.time k))
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : tr.ProposesAt p k P) : tr.AcceptAt p k P := by
  have hP' : (tr.upTo (tr.time k)).ProposesAt p k P :=
    ⟨(RunTrace.upTo_ownBlockAt tr).2 ⟨le_rfl, hP.1⟩, hP.2.1, hP.2.2⟩
  exact ((RunTrace.upTo_acceptAt tr).1
    (Compose.proposal_accepted (hrun.upTo (hrun.time_nonneg k)) (hnc.upTo _) hp hP')).2

end Node

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- Readiness at a larger duration is readiness at a smaller one. -/
theorem confirmed_ready_mono_at (Q : ConfirmedQueryAt S A V) {c d : Time} (hcd : c ≤ d) {y t}
    (h : Regimes.Growing.ReadyAt Q.trace Q.keys d y t) :
    Regimes.Growing.ReadyAt Q.trace Q.keys c y t := by
  refine ⟨h.1, fun τ hlo hhi => h.2 τ ?_ hhi⟩
  exact (max_le_max_left 0 (sub_le_sub_right (sub_le_sub_left hcd t) 1)).trans hlo

/-- The query's readiness duration covers the node catch-up. -/
theorem confirmed_duration_supply_at (Q : ConfirmedQueryAt S A V) :
    Regimes.catchUp Q.params ≤ Q.duration := by
  have hc : (19 : Time) ≤ (contract_catchUp S A : Nat) := by
    exact_mod_cast contract_catchUp_ge_sleepy S A
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  simp only [ConfirmedQueryAt.duration, System.cDur,
    Params.standard, contract_coefficients_catchUp]
  change 18 * Q.run.1.ΔAC ≤ (contract_catchUp S A : Nat) * Q.run.1.ΔAC
  linarith [mul_le_mul_of_nonneg_right hc (zero_le_one.trans hd)]

/-- A slot selected by the recurrence: after the query, its proposal margin `6Δ` before the
deadline, its proposer ready at the slot time with the query's duration and still honest `Δ`
later. -/
structure ConfirmedProducerSlotAt (Q : ConfirmedQueryAt S A V) where
  slot : Nat
  positive : 1 ≤ slot
  fresh : Q.query < Q.params.ts slot
  margin : Q.params.ts slot + 6 * Q.params.Δ ≤ Q.deadline
  ready : Regimes.Growing.ReadyAt Q.trace Q.keys Q.duration
    (runProposer ⟨S, stock⟩ Q.run.2 Q.hn slot) (Q.params.ts slot)
  hold : runProposer ⟨S, stock⟩ Q.run.2 Q.hn slot ∈
    Q.keys (Q.params.ts slot + Regimes.Growing.hold Q.params)

/-- Recurrence/grid selection after an explicit readiness start, at the exact readiness
duration, with the proposer's hold. -/
theorem confirmed_query_slot_at (Q : ConfirmedQueryAt S A V) {ready : Time}
    (hprogress : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A)
      Q.cap Q.index ready Q.run.2.horizon Q.run)
    (hquery : max ready 0 ≤ Q.query) : Nonempty (ConfirmedProducerSlotAt S A V Q) := by
  obtain ⟨s, hs1, hlo, hmargin, hts0, htsh, hR, hH⟩ := nonfinal_query_slot S A V Q.run Q.hn
    Q.nonfinal Q.index Q.bounded hprogress hquery
  have hnode := ready_transport_at ⟨S, stock⟩ Q.run.2 Q.hn Q.valid hts0 htsh hR
  have hkey : Q.run.2.ownKey (Q.run.2.key (runProposer ⟨S, stock⟩ Q.run.2 Q.hn s)) =
      runProposer ⟨S, stock⟩ Q.run.2 Q.hn s := Q.run.2.key.symm_apply_apply _
  erw [hkey] at hnode
  have hhold : runProposer ⟨S, stock⟩ Q.run.2 Q.hn s ∈
      Q.keys (Q.params.ts s + Regimes.Growing.hold Q.params) := by
    rw [mem_honestKeysAt_iff ⟨S, stock⟩ Q.run.2]
    exact hH
  exact ⟨⟨s, hs1, hlo, hmargin, hnode, hhold⟩⟩

/-- The selected slot's actual canonical proposal event, at the slot time. -/
theorem confirmed_slot_event_at (Q : ConfirmedQueryAt S A V)
    (W : ConfirmedProducerSlotAt S A V Q) :
    ∃ (B : SA.Blk Q.params.n (List (FG.Att Q.params.n))) (k : Nat),
      B.proposer = runProposer ⟨S, stock⟩ Q.run.2 Q.hn W.slot ∧
      Q.trace.ProposesAt B.proposer k B ∧ Q.trace.time k = Q.params.ts W.slot := by
  obtain ⟨k, B, hp, ht⟩ := Regimes.Growing.ready_proposer_proposes_at
    (simTraceAt_goldilocksRun ⟨S, stock⟩ Q.run.2 Q.hn Q.valid)
    (noCollRun_simTraceAt ⟨S, stock⟩ Q.run.2 Q.hn Q.valid Q.noCollision)
    W.positive (confirmed_ready_mono_at S A V Q (confirmed_duration_supply_at S A V Q) W.ready)
  exact ⟨B, k, hp.2.1, hp.2.1 ▸ hp, ht⟩

/-- Coverage of a confirmed proposal at every ready read at the deadline is the engine payload
obligation: a proposal after the query by a key ready then, in every ready engine read at the
deadline. -/
theorem confirmed_payload_projection_at (Q : ConfirmedQueryAt S A V)
    (h0 : 0 ≤ Q.query) (P : ConfirmedProposalAt Q)
    (coverage : ∀ y j, Regimes.Growing.ReadyAt Q.trace Q.keys Q.duration y Q.deadline →
      Regimes.CutAfter Q.trace j Q.deadline →
      Anc (Q.trace.HonestBlocksAt Q.keys) P.block (Regimes.readAfter Q.trace y j Q.deadline)) :
    ∃ τ k h, Q.query < τ ∧ Q.run.2.point.Ready Q.duration (Q.run.2.key k) τ ∧
      HonestProposal Q.run.2 τ k h ∧ InBy Q.run.2 Q.duration .confirmed h Q.deadline := by
  have hτ := h0.trans P.fresh.le
  have hprop : Regimes.Growing.ReadyProposalAt Q.trace Q.keys Q.duration
      (Q.trace.time P.cut) 0 P.block :=
    ⟨_, P.cut, P.ready, by simpa using P.ready.1, P.proposal, rfl⟩
  obtain ⟨k, hk, hr⟩ := ready_proposal_at S Q.run.2 Q.hn Q.valid
    (P.bounded.trans Q.bounded) hprop
  refine ⟨_, k, headerOf Q.params P.block, P.fresh, hk, hr, ?_⟩
  exact confirmed_inBy_at S Q.run.2 Q.hn Q.valid
    (noCollRun_simTraceAt ⟨S, stock⟩ Q.run.2 Q.hn Q.valid Q.noCollision)
    (mul_nonneg (Int.natCast_nonneg _) Q.run.1.ΔAC_pos.le)
    hτ P.bounded Q.bounded hprop coverage

end Consensus.Goldilocks.Obligations.Growing

end
