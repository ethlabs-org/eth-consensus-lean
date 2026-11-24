module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RepairDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RecordRead
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.CurrentSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Effective
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy

public section

/-! # The healthy cut adapter under growing faults

Temporal ancestry of one reader's read tips from the heal point. An engine reader ready at a cut
from the heal point is read at the trace cut after its last own event, at its stored clock
(`engine_read_point`), with ancestry inside the blocks held while honest.

Each read tip is the reader's effective record (`healthy_current_record_read_at`), and one
reader's effective record only extends between its read points
(`healthy_current_record_interval_at`, `effective_record_of_interval_at`). -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **Temporal ancestry of the read tips** of one reader ready at two cuts from the heal point,
the later read within the query's bound. -/
theorem healthy_cut_tips_ancestor_at
    (Q : HealthyPreparationQueryAt S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.bound)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V)
      (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    {sign : Fin Q.params.n → Time → Bool}
    (hcal : Q.trace.SignCalendarAt (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.keys sign)
    {Gs : Nat} (hgap : SignGapAt Q.params.toParams sign Gs 0)
    (hδG : 3 + (Gs + 3) / 4 ≤ Q.params.toParams.fg.δt)
    (hGs : (contract_catchUp S A : Nat) +
      (healthyResetCoeff S Q.index + 8 * S.k + 4 * (Q.index : Nat) + 34) + 3 + 5 * Gs ≤
        contract_heal S A Q.cap Q.index)
    (hGsT : 4 * A.fgSlots + Gs ≤ 4 * S.δt)
    (v : V) (i j : Nat)
    (hi : (chainTrace Q.run.2).InCuts Q.heal i) (hij : i ≤ j)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j)
    (hvi : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i))
    (hvj : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime j))
    (hjb : (stateAt S Q.run.2 Q.hn v j).now ≤ Q.bound) :
    Anc (Q.trace.HonestBlocksAt Q.keys)
      (Regimes.readAfter Q.trace (Q.run.2.ownKey v)
        (cutMap S Q.run.2 Q.hn (lastOwn S Q.run.2 v i)) (stateAt S Q.run.2 Q.hn v i).now)
      (Regimes.readAfter Q.trace (Q.run.2.ownKey v)
        (cutMap S Q.run.2 Q.hn (lastOwn S Q.run.2 v j)) (stateAt S Q.run.2 Q.hn v j).now) := by
  obtain ⟨D⟩ := healthy_repair_schedule_at S A V Q h0 hb hp hcal hgap hδG hGs hGsT
  obtain ⟨O⟩ := healthy_bounded_repairing_opening_at S A V Q hb hp D
  have hnn := cutMap_mono S Q.run.2 Q.hn (lastOwn_mono S Q.run.2 v hij)
  have htt := now_mono S Q.run.2 Q.hn Q.valid v hij
  obtain ⟨Ci⟩ := healthy_current_read_context_at S A V Q D O hi hvi
      (htt.trans hjb)
  obtain ⟨Cj⟩ := healthy_current_read_context_at S A V Q D O hj hvj hjb
  rw [healthy_current_record_read_at S A V Q D O hi hvi (htt.trans hjb),
    healthy_current_record_read_at S A V Q D O hj hvj hjb]
  exact effective_record_of_interval_at D.reset.run D.reset.noColl Cj.time_nonneg
    Cj.readPoint.1 Cj.honest hnn
    (healthy_current_record_interval_at D.toRepairSchedule O.toRepairOpening Ci.readPoint
      Cj.readPoint htt Cj.time_bound Cj.honest Ci.repaired Ci.repairedCut) .refl

end Consensus.Goldilocks.Obligations.Growing

end
