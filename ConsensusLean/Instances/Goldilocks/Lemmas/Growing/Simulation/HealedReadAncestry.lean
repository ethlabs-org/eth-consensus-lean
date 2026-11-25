module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunMapReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.CutTips
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.SignCalendar
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.SignGap
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationInitialize
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.SignGap

public section

/-! # Temporal ancestry at actual Goldilocks stored reads -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks Generic Obligations

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The same reader's two healed stored reads are ordered by ancestry at every vote binding. -/
theorem goldilocks_healedReadAncestry (S : Setup) (A : ContractAssumptions S) {E : Env V}
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) :
    HealedReadAncestry (goldilocksRunMap S rho hn hv) (K S A)
      (goldilocksStoredReadContext S rho hn hv) := by
  intro hv' hc cap idx gst hcap hhealthy hp h0 hb v i j hi hij hj hvi hvj hjb
  let Q : Obligations.Growing.HealthyPreparationQueryAt S A V :=
    { run := ⟨E, rho⟩, hn := hn, cap := cap, nonfinal := hcap, index := idx,
      gst := gst, bound := rho.horizon, valid := hv', noCollision := hc, bound_le := le_rfl,
      healthy := ⟨hhealthy.1, hhealthy.2.1, hhealthy.2.2.1⟩,
      committeeHealthy := hhealthy.2.2.2 }
  simp only [goldilocksRunMap_trace, goldilocksRunMap_honest, goldilocksStoredReadContext_tip]
  rw [goldilocksStoredReadContext_now] at hjb
  exact Obligations.Growing.healthy_cut_tips_ancestor_at S A V Q h0 hb hp
    (simTraceAt_signCalendar S rho hn _) (Obligations.signGapAt_of_assumptions A _ _)
    (Obligations.signGap_δt A) (Obligations.contract_heal_ge_reset_signGap A Q.cap Q.index)
    A.fgSlots_releaseGap_signGap_le v i j hi hij hj hvi hvj hjb

end Consensus.Goldilocks.Simulation

end
