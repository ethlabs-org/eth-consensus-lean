module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthySuppliers

public section
namespace Consensus.Goldilocks.Refinement
open Blocks Shape
variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- OPEN arbitrary-cut agreement adapter. Concrete preserved state facts are
inputs; the conclusion reads the actual engine cuts, not endCut observations.
No post-heal progress is available. This is not derived from cache compatibility
alone: origin/lock/frame and engine output transport remain its obligations. -/
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
  sorry

/-- OPEN temporal adapter, separate from cross-reader agreement: actual engine
cut order and both readiness tests must yield prefix extension. In particular,
post-endCut state facts do not automatically cover earlier cuts at time heal. -/
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
  sorry

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
