module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RepairDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RecordRead
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.CurrentSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Effective
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy

public section

/-! # The healthy cut adapters under growing faults

The two read-tip facts that healed safety reduces to (the growing forms of
`Obligations.healthy_cut_tips_comparable` and `Obligations.healthy_cut_tips_ancestor`). An engine
reader ready at a cut from the heal point is read at the trace cut after its last own event, at
its stored clock (`engine_read_point`), with ancestry inside the blocks held while honest.

Each read tip is the reader's effective record (`healthy_current_record_read_at`). Two readers'
covered records are compatible (`healthy_current_sources_compatible_at`), and one reader's
effective record only extends between its read points (`healthy_current_record_interval_at`,
`effective_record_of_interval_at`). -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **Comparability of the read tips** of two readers ready from the heal point, each read at
the trace cut after its last own event at its stored clock, within the query's bound. -/
theorem healthy_cut_tips_comparable_at (Q : HealthyPreparationQueryAt S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.bound)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (u v : V) (i j : Nat)
    (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j)
    (hu : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) u
      ((chainTrace Q.run.2).cutTime i))
    (hv : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime j))
    (hub : (stateAt S Q.run.2 Q.hn u i).now ≤ Q.bound)
    (hvb : (stateAt S Q.run.2 Q.hn v j).now ≤ Q.bound) :
    let C := fun v i => Regimes.readAfter Q.trace (Q.run.2.ownKey v)
      (cutMap S Q.run.2 Q.hn (lastOwn S Q.run.2 v i)) (stateAt S Q.run.2 Q.hn v i).now
    Anc (Q.trace.HonestBlocksAt Q.keys) (C u i) (C v j) ∨
      Anc (Q.trace.HonestBlocksAt Q.keys) (C v j) (C u i) := by
  obtain ⟨D⟩ := healthy_repair_schedule_at S A V Q h0 hb hp
  obtain ⟨O, hr⟩ := healthy_bounded_repairing_opening_at S A V Q hb hp D
  obtain ⟨Cu⟩ := healthy_current_read_context_at S A V Q D hi hu hub
  obtain ⟨Cv⟩ := healthy_current_read_context_at S A V Q D hj hv hvb
  dsimp only
  rw [healthy_current_record_read_at S A V Q hb hp D O hr hi hu hub,
    healthy_current_record_read_at S A V Q hb hp D O hr hj hv hvb]
  exact healthy_current_sources_compatible_at S A V Q D Cu.readPoint Cu.time_bound Cu.honest
    Cv.readPoint Cv.time_bound Cv.honest
    (healthy_current_record_sources_before_now_at S A V Q D O hr Cu.readPoint Cu.time_bound
      Cu.honest Cu.repaired)
    (healthy_current_record_sources_before_now_at S A V Q D O hr Cv.readPoint Cv.time_bound
      Cv.honest Cv.repaired)

/-- **Temporal ancestry of the read tips** of one reader ready at two cuts from the heal point,
the later read within the query's bound. -/
theorem healthy_cut_tips_ancestor_at (Q : HealthyPreparationQueryAt S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.bound)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
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
  obtain ⟨D⟩ := healthy_repair_schedule_at S A V Q h0 hb hp
  obtain ⟨O, hr⟩ := healthy_bounded_repairing_opening_at S A V Q hb hp D
  have hnn := cutMap_mono S Q.run.2 Q.hn (lastOwn_mono S Q.run.2 v hij)
  have htt := now_mono S Q.run.2 Q.hn Q.valid v hij
  obtain ⟨Ci⟩ := healthy_current_read_context_at S A V Q D hi hvi (htt.trans hjb)
  obtain ⟨Cj⟩ := healthy_current_read_context_at S A V Q D hj hvj hjb
  rw [healthy_current_record_read_at S A V Q hb hp D O hr hi hvi (htt.trans hjb),
    healthy_current_record_read_at S A V Q hb hp D O hr hj hvj hjb]
  exact effective_record_of_interval_at (simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid)
    (noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision) Cj.time_nonneg Cj.readPoint.1
    Cj.honest hnn
    (healthy_current_record_interval_at S A V Q hb D O hr Ci.readPoint Cj.readPoint hnn htt
      Cj.time_bound Cj.honest Ci.repaired) .refl

end Consensus.Goldilocks.Obligations.Growing

end
