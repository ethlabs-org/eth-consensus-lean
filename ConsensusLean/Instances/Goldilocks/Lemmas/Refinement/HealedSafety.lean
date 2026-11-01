module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthySuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Simulation
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain

public section
namespace Consensus.Goldilocks.Refinement
open Blocks Shape
variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- The four directed record/F cases. Compatibility alone is insufficient:
the producer must supply directed record evolution as well as cache growth. -/
theorem effective_tip_step (Q : HealthyPreparationQuery S A V)
    {C C' F F' R R' : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hC : Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) C C')
    (hF : Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) F F')
    (hR : (R = C ∧ Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) F C) ∨
      (R = F ∧ Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) C F))
    (hR' : (R' = C' ∧ Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) F' C') ∨
      (R' = F' ∧ Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) C' F')) :
    Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R R' := by
  rcases hR with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;>
    rcases hR' with ⟨rfl, hFC⟩ | ⟨rfl, hCF⟩
  · exact hC
  · exact hC.trans hCF
  · exact hF.trans hFC
  · exact hF

/-- Finite cut induction from explicit record evolution and effective-tip
dichotomies. The interval includes its start cut; no clock increase is needed. -/
theorem effective_tip_mono (Q : HealthyPreparationQuery S A V)
    (C F R : Nat → SA.Blk Q.params.n (List (FG.Att Q.params.n)))
    {i j : Nat} (hij : i ≤ j)
    (hC : ∀ k, i ≤ k → k < j →
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (C k) (C (k + 1)))
    (hF : ∀ k, i ≤ k → k < j →
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (F k) (F (k + 1)))
    (hR : ∀ k, i ≤ k → k ≤ j →
      (R k = C k ∧ Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (F k) (C k)) ∨
      (R k = F k ∧ Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (C k) (F k))) :
    Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (R i) (R j) := by
  have aux : ∀ k, i ≤ k → k ≤ j →
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (R i) (R k) := by
    intro k hik
    induction k, hik using Nat.le_induction with
    | base => intro _; exact .refl
    | succ k hik ih =>
      intro hkj
      exact (ih (by omega)).trans (effective_tip_step S A V Q
        (hC k hik (by omega)) (hF k hik (by omega))
        (hR k hik (by omega)) (hR (k + 1) (by omega) hkj))
  exact aux j hij le_rfl

/-- Actual tips below compatible origin witnesses are comparable. The read
producer must supply these witnesses at the actual stored-clock cuts, including
cuts preceding endCut heal; post-base preservation alone cannot do so. -/
theorem tips_comparable_of_origin_witnesses (Q : HealthyPreparationQuery S A V)
    {R R' C C' : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hR : Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R C)
    (hR' : Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R' C')
    (hCC : Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2)) C C') :
    Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R R' := by
  have hU := Compose.honest_blocks_coherent
    (simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid).toLocalRun
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision)
  rcases hCC with h | h
  · exact Anc.total hU (hR.trans h) hR'
  · exact Anc.total hU hR (hR'.trans h)

/-- Common recent-origin comparison, including the genesis alternative.
Membership and chain coverage must concern the actual read tips, not just caches. -/
theorem tips_comparable_of_origin_chain (Q : HealthyPreparationQuery S A V)
    {s₀ : Nat} {R R' : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hR : R ∈ Q.trace.HonestBlocks (honestKeys S Q.run.2))
    (hR' : R' ∈ Q.trace.HonestBlocks (honestKeys S Q.run.2))
    (hc : Compose.OnOriginChainFrom Q.trace (honestKeys S Q.run.2) R s₀)
    (hc' : Compose.OnOriginChainFrom Q.trace (honestKeys S Q.run.2) R' s₀)
    (hcomp : ∀ C p C' p', Compose.OriginFrom Q.trace (honestKeys S Q.run.2) C p s₀ →
      Compose.OriginFrom Q.trace (honestKeys S Q.run.2) C' p' s₀ →
      Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2)) C C') :
    Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R R' := by
  have hr := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hU := Compose.honest_blocks_coherent hr.toLocalRun
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision)
  rcases Compose.onOriginChainFrom_iff.1 hc with hg | ⟨C, p, hp, hRC⟩
  · rw [Compose.honest_eq_genesis hr hU hR hg]
    exact Or.inl (Compose.honest_genesis_anc hr hR').2
  rcases Compose.onOriginChainFrom_iff.1 hc' with hg | ⟨C', p', hp', hRC'⟩
  · rw [Compose.honest_eq_genesis hr hU hR' hg]
    exact Or.inr (Compose.honest_genesis_anc hr hR).2
  exact tips_comparable_of_origin_witnesses S A V Q hRC hRC' (hcomp C p C' p' hp hp')

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
