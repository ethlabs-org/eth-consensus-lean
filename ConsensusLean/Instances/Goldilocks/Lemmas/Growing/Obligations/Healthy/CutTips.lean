module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RepairDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.ReadPoint

public section

/-! # The healthy cut adapters under growing faults (open)

The two read-tip facts that healed safety reduces to (the growing forms of
`Obligations.healthy_cut_tips_comparable` and `Obligations.healthy_cut_tips_ancestor`). An engine
reader ready at a cut from the heal point is read at the trace cut after its last own event, at
its stored clock (`engine_read_point`), with ancestry inside the blocks held while honest.

Both are open: their proofs are the current-read port of `Lemmas/Obligations/HealedSafety`
(the repair opening, the read context and the effective-record interval). -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- OPEN comparability of the read tips of two readers ready from the heal point, each read at
the trace cut after its last own event at its stored clock. -/
theorem healthy_cut_tips_comparable_at (Q : HealthyPreparationQueryAt S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (u v : V) (i j : Nat)
    (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j)
    (hu : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) u
      ((chainTrace Q.run.2).cutTime i))
    (hv : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime j)) :
    let C := fun v i => Regimes.readAfter Q.trace (Q.run.2.ownKey v)
      (cutMap S Q.run.2 Q.hn (lastOwn S Q.run.2 v i)) (stateAt S Q.run.2 Q.hn v i).now
    Anc (Q.trace.HonestBlocksAt Q.keys) (C u i) (C v j) ∨
      Anc (Q.trace.HonestBlocksAt Q.keys) (C v j) (C u i) := by
  sorry

/-- OPEN temporal ancestry of the read tips of one reader ready at two cuts from the heal point. -/
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
