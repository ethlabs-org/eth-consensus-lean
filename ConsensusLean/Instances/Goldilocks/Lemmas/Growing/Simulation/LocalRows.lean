module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RegimeTransport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Query
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Family.ServiceEquivalence
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.CoefficientAdapters
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Local service suppliers at the canonical Goldilocks run map -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks Generic Obligations
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V]

private theorem deadline_data_cast {P : Params} {N : NodeAC P}
    {sg sg' : N.Msg → Fin P.n} (h : sg = sg') (C : ACCorrectLocal N sg) :
    (h ▸ C).catchUp = C.catchUp ∧ (h ▸ C).latency = C.latency ∧
      (h ▸ C).margin = C.margin := by
  subst h
  exact ⟨rfl, rfl, rfl⟩

private theorem hold_data_cast {P : Params} {N : NodeAC P}
    {sg sg' : N.Msg → Fin P.n} (h : sg = sg') (C : ACCorrectLocal N sg) :
    (h ▸ C).hold = C.hold := by
  subst h
  rfl

/-- The outage regime supplies pre-outage recipient service and post-stop service. -/
theorem goldilocks_outageServiceSupply (S : Setup) (A : ContractAssumptions S) {E : Env V}
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid)
    (C : ACCorrectLocal (goldilocksNode (S.params (pubOf E) hn) (S.ro _)) (fun v => v.val))
    (hC : GoldilocksLocalData (S.params (pubOf E) hn) (S.ro _) C)
    (hsg : (fun v => v.val) = (goldilocksRunMap S rho hn hv).signer) :
    OutageServiceSupply (goldilocksRunMap S rho hn hv) (K S A) (hsg ▸ C) := by
  classical
  obtain ⟨es, -⟩ := service_data_cast hsg C
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hserved⟩ := hC
  intro hv' hc T b₀ b₁ hout
  let Q : Growing.OutageQueryAt S A V :=
    { run := ⟨E, rho⟩, hn := hn, T := T, start := b₀, stop := b₁,
      valid := hv', noCollision := hc, outage := hout }
  have hrun := simTraceAt_goldilocksRun S rho hn hv'
  have hs := Growing.outage_pre_service_at Q
  simp only [goldilocksRunMap_trace, goldilocksRunMap_honest]
  refine ⟨⟨E.ΔFG_pos, ?_, hs.relay⟩, Growing.outage_postStopService_at Q⟩
  intro x i m hx hm hi0 y j ℓ hy hcall hdb hdl
  have hsrc : (simTraceAt S rho hn).projAC.SendOrAdmit x i m := by
    obtain ⟨ℓ₀, hc₀, hm₀⟩ := hm
    refine ⟨ℓ₀, Compose.projAC_callAt.mpr hc₀, ?_⟩
    rw [Compose.Growing.projAC_state_at hrun hx]
    exact hm₀
  have h := hs.message x i m hx hsrc hi0 y j ℓ hy (Compose.projAC_callAt.mpr hcall)
    (by rw [Compose.projAC_deadline]; exact hdb) (by rw [Compose.projAC_deadline]; exact hdl)
  rw [es, hserved]
  exact (SA.FamilyFacts.messageServedBefore_iff_old ..).mpr h

/-- The local read deadlines and quorum thresholds fit the endpoint contract. -/
theorem goldilocks_claimDeadlineFit (S : Setup) (A : ContractAssumptions S) {E : Env V}
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid)
    (C : ACCorrectLocal (goldilocksNode (S.params (pubOf E) hn) (S.ro _)) (fun v => v.val))
    (hC : GoldilocksLocalData (S.params (pubOf E) hn) (S.ro _) C)
    (hsg : (fun v => v.val) = (goldilocksRunMap S rho hn hv).signer) :
    ClaimDeadlineFit (goldilocksRunMap S rho hn hv) (K S A) (hsg ▸ C) := by
  have hdata : (hsg ▸ C).catchUp = 18 * E.ΔAC ∧ (hsg ▸ C).latency = 6 * E.ΔAC ∧
      (hsg ▸ C).margin = 6 * E.ΔAC := by
    obtain ⟨hc, hl, hm⟩ := deadline_data_cast hsg C
    exact ⟨hc.trans hC.2.2.1, hl.trans hC.2.2.2.2.2.2.2.1,
      hm.trans hC.2.2.2.2.2.2.1⟩
  refine ⟨?_, by rw [hdata.2.1, hdata.2.2], ?_, ?_, ?_⟩
  · exact (goldilocks_outageRecoveryBinding S A hn
      (goldilocksRunMap S rho hn hv) C hC hsg).catchUp
  · intro cap idx gst _
    rw [hdata.2.2]
    change max gst 0 + 6 * E.ΔAC ≤
      max gst 0 + (contract_heal S A cap idx : Time) * E.ΔAC
    have hh : (6 : Time) ≤ (contract_heal S A cap idx : Nat) := by
      exact_mod_cast (show 6 ≤ contract_heal S A cap idx by
        rw [contract_heal_val, contract_catchUp_val]; omega)
    exact add_le_add_right (mul_le_mul_of_nonneg_right hh E.ΔAC_pos.le) _
  · change (1 / 3 : ℚ) * Fintype.card V ≤
      ((2 * (S.params (pubOf E) hn).toParams.q - Fintype.card V : Nat) : ℚ)
    have hq : Fintype.card V ≤
        3 * (2 * (S.params (pubOf E) hn).toParams.q - Fintype.card V) := by
      simp only [Params.q]
      omega
    have hq' : (Fintype.card V : ℚ) ≤
        3 * ((2 * (S.params (pubOf E) hn).toParams.q - Fintype.card V : Nat) : ℚ) := by
      exact_mod_cast hq
    linarith
  · intro t _ _ hf
    exact (S.params (pubOf E) hn).toParams.fg.faults_lt_quorum_margin hf

private theorem query_proposal_witness (S : Setup) (A : ContractAssumptions S)
    (Q : Growing.ConfirmedQueryAt S A V) {ready : Time}
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A)
      Q.cap Q.index ready Q.run.2.horizon Q.run)
    (hq : max ready 0 ≤ Q.query) :
    ∃ B k, Q.query < Q.trace.time k ∧
      Generic.ReadyProposal Q.trace Q.keys (18 * Q.params.Δ) Q.params.Δ B k ∧
      Q.trace.time k + 6 * Q.params.Δ ≤ Q.deadline ∧
      B.root ≠ Q.params.genesisRoot ∧ 0 ≤ Q.trace.time k ∧
      Q.trace.time k + Q.params.Δ ≤ Q.run.2.horizon ∧
      Q.run.2.point.Ready Q.duration (Q.run.2.key B.proposer) (Q.trace.time k) := by
  obtain ⟨P, hm, hh⟩ := Growing.sleepy_query_producer_at S A V Q hp hq
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have ht0 := hrun.time_nonneg P.cut
  have hacc := (RunTrace.upTo_acceptAt Q.trace).mpr ⟨le_rfl, P.accepted⟩
  have hroot := (Compose.accept_facts (hrun.upTo ht0).toLocalRun P.ready.1 hacc).2.2.2
  have hth : Q.trace.time P.cut ≤ Q.run.2.horizon := P.bounded.trans Q.bounded
  refine ⟨P.block, P.cut, P.fresh,
    ⟨P.proposal, Growing.confirmed_ready_mono_at S A V Q
      (Growing.confirmed_duration_supply_at S A V Q) P.ready, hh⟩,
    hm, hroot, ht0, ?_, ?_⟩
  · have hd := Q.params.toParams.hΔ.le
    linarith [Q.bounded]
  · refine ⟨?_, ?_⟩
    · have h := (mem_honestKeysAt_iff S Q.run.2 _ _).mp P.ready.1
      rwa [min_eq_left hth] at h
    · intro u hu hut
      have h := P.ready.2 u hu hut
      rw [simTraceAt_awake_iff S Q.run.2 Q.hn, awakeAt_iff S Q.run.2 Q.hn] at h
      exact h.1

/-- The selected proposal retains the readiness and hold needed by the claim consumer. -/
theorem goldilocks_proposalWitnessRefinement (S : Setup) (A : ContractAssumptions S) {E : Env V}
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid)
    (C : ACCorrectLocal (goldilocksNode (S.params (pubOf E) hn) (S.ro _)) (fun v => v.val))
    (hC : GoldilocksLocalData (S.params (pubOf E) hn) (S.ro _) C)
    (hsg : (fun v => v.val) = (goldilocksRunMap S rho hn hv).signer) :
    ProposalWitnessRefinement (goldilocksRunMap S rho hn hv) (K S A) (hsg ▸ C) := by
  obtain ⟨hcatch, -, hmargin⟩ := deadline_data_cast hsg C
  have hc := hcatch.trans hC.2.2.1
  have hh := (hold_data_cast hsg C).trans hC.2.2.2.2.2.1
  have hm := hmargin.trans hC.2.2.2.2.2.2.1
  constructor
  · intro hv' hnc cap idx t hcap hs hp ht hb hr
    let Q : Growing.ConfirmedQueryAt S A V :=
      { run := ⟨E, rho⟩, hn := hn, cap := cap, nonfinal := hcap, index := idx,
        gst := 0, query := t, valid := hv', noCollision := hnc,
        regime := .inl ⟨hs, hp, ht⟩, bounded := hb, reader := hr }
    simpa only [goldilocksRunMap_trace, goldilocksRunMap_honest,
      AdmissibleProposal, goldilocksRunMap_validator, hc, hh, hm] using
      query_proposal_witness S A Q hp (by simpa using ht)
  · intro hv' hnc cap idx gst t hcap hs hp ht hb hr
    let Q : Growing.ConfirmedQueryAt S A V :=
      { run := ⟨E, rho⟩, hn := hn, cap := cap, nonfinal := hcap, index := idx,
        gst := gst, query := t, valid := hv', noCollision := hnc,
        regime := .inr (.inl ⟨hs, hp, ht⟩), bounded := hb, reader := hr }
    have hready : (Sys (goldilocks S) V).ready (K S A) gst ⟨E, rho⟩ ≤
        (Sys (goldilocks S) V).heal (K S A) cap idx gst ⟨E, rho⟩ := by
      apply ready_le_heal E.ΔAC_pos
      change ((contract_catchUp S A : Nat) : Time) + 1 ≤ (contract_heal S A cap idx : Nat)
      exact_mod_cast (show contract_catchUp S A + 1 ≤ contract_heal S A cap idx by
        rw [contract_heal_val, healMargin_val]; omega)
    have ht0 : 0 ≤ t := by
      have := (goldilocks_claimDeadlineFit S A rho hn hv C hC hsg).healthy_start
        cap idx gst hcap
      have hd := E.ΔAC_pos
      rw [hm] at this
      linarith [le_max_right gst 0]
    simpa only [goldilocksRunMap_trace, goldilocksRunMap_honest,
      AdmissibleProposal, goldilocksRunMap_validator, hc, hh, hm] using
      query_proposal_witness S A Q hp (max_le (hready.trans ht) ht0)

/-- An honest node proposal is the same honest proposal in the engine run. -/
theorem goldilocks_proposalProgressTransport (S : Setup) {E : Env V}
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) :
    ProposalProgressTransport (goldilocksRunMap S rho hn hv) := by
  constructor
  intro B k hB hh
  simp only [goldilocksRunMap_trace, goldilocksRunMap_honest] at hB hh ⊢
  have htime : (simTraceAt S rho hn).time k ≤ rho.horizon := by
    obtain ⟨acc, hc⟩ := hB.1.1
    exact simTraceAt_labelled_time_le S rho hn hv (by rw [hc.2]; simp)
  obtain ⟨r, cs, hr, he⟩ := (goldilocksRunMap S rho hn hv).proposal_role B
  refine ⟨?_, r, cs, hr, ?_⟩
  · rw [(goldilocksRunMap S rho hn hv).key_eq, goldilocksRunMap_validator]
    have h := (mem_honestKeysAt_iff S rho _ B.proposer).mp hh
    rwa [min_eq_left htime] at h
  · rw [← he, goldilocksRunMap_proposalObject,
      (goldilocksRunMap S rho hn hv).key_eq, goldilocksRunMap_validator]
    exact simTraceAt_block_released S rho hn hv B.proposer k B hh hB.1

end Consensus.Goldilocks.Simulation

end
