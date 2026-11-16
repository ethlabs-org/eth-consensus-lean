module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RegimeTransport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Query
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Family.ServiceEquivalence
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
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

end Consensus.Goldilocks.Simulation

end
