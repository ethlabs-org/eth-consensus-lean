module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationInitialize
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Selection
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.ReadPoint

public section

/-! # Pending interface of the healthy confirmed supply under growing faults

The statement the healthy confirmed supply (`ConfirmedSupply`) consumes whose home module is not
on this branch yet, under its agreed name: `healthy_cut_tips_ancestor_at`, home
`Lemmas/Growing/Obligations/Healthy/CutTips`. The module re-exports the homes of the other
inputs: `Healing.Growing.operational_update_selection_at` (the growing kernel's selection
module), `healthy_preparation_initialize_at` and `healthy_repair_catch_at`
(`Healthy/PreparationInitialize`, `Healthy/Preparation`).

The theorem here is an open `sorry`; this module is deleted when its home lands. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- Temporal ancestry of the read tips of one reader ready at two cuts from the heal point. -/
theorem healthy_cut_tips_ancestor_at (Q : HealthyPreparationQueryAt S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (v : V) (i j : Nat)
    (hi : (chainTrace Q.run.2).InCuts Q.heal i) (hij : i ≤ j)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j)
    (hvi : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i))
    (hvj : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime j)) :
    Anc (Q.trace.HonestBlocksAt Q.keys)
      (Regimes.readAfter Q.trace (Q.run.2.ownKey v)
        (cutMap S Q.run.2 Q.hn (lastOwn S Q.run.2 v i)) (stateAt S Q.run.2 Q.hn v i).now)
      (Regimes.readAfter Q.trace (Q.run.2.ownKey v)
        (cutMap S Q.run.2 Q.hn (lastOwn S Q.run.2 v j)) (stateAt S Q.run.2 Q.hn v j).now) := by
  sorry

end Consensus.Goldilocks.Obligations.Growing

end
