module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthySuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Simulation

public section
namespace Consensus.Goldilocks.Refinement
open Blocks Shape
variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- OPEN comparability of actual stored-clock tips. Old-row realization,
label replacement and head/lock/frame comparability remain obligations. InCuts
includes cuts at heal before endCut heal; the state facts do not cover these. -/
theorem healthy_cut_tips_comparable (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (W : HealthyBaseTiming S A V Q)
    (states : ∀ k, Q.cut ≤ k → k ≤ cutMap S Q.run.2 Q.hn Q.run.2.events.length →
      HealthyStateFacts S A V Q W.slot k)
    (u v : V) (i j : Nat)
    (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j)
    (hu : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) u
      ((chainTrace Q.run.2).cutTime i))
    (hv : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime j)) :
    let C := fun v i => Regimes.readAfter Q.trace (Q.run.2.ownKey v)
      (cutMap S Q.run.2 Q.hn i) (stateAt S Q.run.2 Q.hn v i).now
    Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (C u i) (C v j) ∨
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (C v j) (C u i) := by
  sorry

/-- OPEN temporal ancestry, not merely common-chain membership. The stored
clock and equality-time boundary are retained exactly as in the engine reads. -/
theorem healthy_cut_tips_ancestor (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (W : HealthyBaseTiming S A V Q)
    (states : ∀ k, Q.cut ≤ k → k ≤ cutMap S Q.run.2 Q.hn Q.run.2.events.length →
      HealthyStateFacts S A V Q W.slot k)
    (v : V) (i j : Nat)
    (hi : (chainTrace Q.run.2).InCuts Q.heal i) (hij : i ≤ j)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j)
    (hvi : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i))
    (hvj : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime j)) :
    Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2))
      (Regimes.readAfter Q.trace (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)
        (stateAt S Q.run.2 Q.hn v i).now)
      (Regimes.readAfter Q.trace (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn j)
        (stateAt S Q.run.2 Q.hn v j).now) := by
  sorry

/-- Arbitrary-cut engine agreement reduces to the named open tip comparability
obligation. No equality between stored clock and cut time is assumed. -/
theorem healthy_cut_agreement (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (W : HealthyBaseTiming S A V Q)
    (states : ∀ k, Q.cut ≤ k → k ≤ cutMap S Q.run.2 Q.hn Q.run.2.events.length →
      HealthyStateFacts S A V Q W.slot k)
    (u v : V) (i j : Nat)
    (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j)
    (hu : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) u
      ((chainTrace Q.run.2).cutTime i))
    (hv : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime j)) :
    Consensus.Compatible ((chainTrace Q.run.2).read .confirmed u i)
      ((chainTrace Q.run.2).read .confirmed v j) := by
  have hs := simTrace_simulates S Q.run.2 Q.hn Q.valid
  have hnc := noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision
  rcases healthy_cut_tips_comparable S A V Q h0 hb hp W states u v i j hi hj hu hv with h | h
  · exact Or.inl (confirmed_prefix_of_anc hs hnc hu.1 hv.1 hi.1 hj.1 h)
  · exact Or.inr (confirmed_prefix_of_anc hs hnc hv.1 hu.1 hj.1 hi.1 h)

/-- Arbitrary-cut monotonicity reduces to directed tip ancestry. Agreement
alone is not used to infer temporal movement. -/
theorem healthy_cut_monotone (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (W : HealthyBaseTiming S A V Q)
    (states : ∀ k, Q.cut ≤ k → k ≤ cutMap S Q.run.2 Q.hn Q.run.2.events.length →
      HealthyStateFacts S A V Q W.slot k)
    (v : V) (i j : Nat)
    (hi : (chainTrace Q.run.2).InCuts Q.heal i) (hij : i ≤ j)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j)
    (hvi : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i))
    (hvj : Q.run.2.point.Ready ((Sys (family S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime j)) :
    (chainTrace Q.run.2).read .confirmed v i <+:
      (chainTrace Q.run.2).read .confirmed v j := by
  exact confirmed_prefix_of_anc (simTrace_simulates S Q.run.2 Q.hn Q.valid)
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision) hvi.1 hvj.1 hi.1 hj.1
    (healthy_cut_tips_ancestor S A V Q h0 hb hp W states v i j hi hij hj hvi hvj)

/-- Assembly with finite preparation; only the two named cut adapters remain
for projection. Their OPEN types retain the exact equality-time boundary case. -/
theorem healthy_ready_safety (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run) :
    (chainTrace Q.run.2).ReadySafe ((Sys (family S) V).cDur (K S A) Q.run)
      .confirmed Q.heal := by
  obtain ⟨W, inv⟩ := healthy_old_inventory_initialize S A V Q h0 hb hp
  have base := healthy_prepare S A V Q h0 hb hp W inv
  have states := healthy_preserve S A V Q h0 hb W base
  exact ⟨healthy_cut_agreement S A V Q h0 hb hp W states,
    healthy_cut_monotone S A V Q h0 hb hp W states⟩

end Consensus.Goldilocks.Refinement
end
