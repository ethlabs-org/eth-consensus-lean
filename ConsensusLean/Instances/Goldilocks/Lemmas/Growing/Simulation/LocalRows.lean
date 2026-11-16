module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RegimeTransport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Query
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Family.ServiceEquivalence

public section

/-! # Local service suppliers at the canonical Goldilocks run map -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks Generic Obligations
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V]

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

end Consensus.Goldilocks.Simulation

end
