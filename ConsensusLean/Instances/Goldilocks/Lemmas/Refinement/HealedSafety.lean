module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthySuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Outputs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyEffective
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Sleepy
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

/-- A read-support producer at genuine read points suffices at stored engine clocks.
The representative is the last local event, not the original global cut. -/
theorem healthy_stored_read_eq_record (Q : HealthyPreparationQuery S A V)
    {c t₀ : Time} (hc : 0 ≤ c)
    (hread : ∀ y k t, (∃ q ≤ Q.run.2.events.length, k = cutMap S Q.run.2 Q.hn q) →
      Regimes.ReadPoint Q.trace k t →
      Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) c y t → t₀ ≤ t → t ≤ Q.run.2.horizon →
      Regimes.readAfter Q.trace y k t =
        (SA.lookup (Node.frame (Q.trace.state y k))
          (Q.trace.state y k).ac.latestConfirmed).getD (Q.trace.state y k).fg.F)
    {v : V} {i : Nat} (hi : i ≤ Q.run.2.events.length)
    (hfloor : t₀ ≤ (stateAt S Q.run.2 Q.hn v i).now)
    (hr : Q.run.2.point.Ready (c + 1) v (Q.run.2.cutTime i)) :
    Regimes.readAfter Q.trace (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)
        (stateAt S Q.run.2 Q.hn v i).now =
      (SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)))
        (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).ac.latestConfirmed).getD
          (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).fg.F := by
  have hready := ready_at_stored_now S Q.run.2 Q.hn Q.valid hi hc hr
  obtain ⟨q, hq, hs, hrp, hth⟩ : ∃ q ≤ Q.run.2.events.length,
      stateAt S Q.run.2 Q.hn v i = stateAt S Q.run.2 Q.hn v q ∧
      Regimes.ReadPoint Q.trace (cutMap S Q.run.2 Q.hn q)
        (stateAt S Q.run.2 Q.hn v i).now ∧
      (stateAt S Q.run.2 Q.hn v i).now ≤ Q.run.2.horizon := by
    rcases stateAt_last_local_event S Q.run.2 Q.hn Q.valid v i with hs | ⟨j, hj, e, he, hev, hs, ht⟩
    · refine ⟨0, Nat.zero_le _, hs, ?_, ?_⟩
      · rw [hs, cutMap_zero]
        exact ⟨fun k hk => by omega,
          (simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid).time_nonneg 0⟩
      · rw [hs]
        exact Q.valid.horizon_nonneg
    · refine ⟨j + 1, by omega, hs, ?_, ?_⟩
      · rw [ht]
        exact readPoint_after_event S Q.run.2 Q.hn Q.valid he
      · rw [ht]
        exact (Q.valid.in_horizon e (List.mem_of_getElem? he)).2
  have hnready := ready_transport S Q.run.2 Q.hn Q.valid
    (now_bounds_cut S Q.run.2 Q.hn Q.valid v hi).1 hth hready
  have heq := hread _ _ _ ⟨q, hq, rfl⟩ hrp hnready hfloor hth
  have hstate : Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i) =
      Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn q) := by
    rw [← simTrace_state S Q.run.2 Q.hn Q.valid v hr.1 i hi,
      ← simTrace_state S Q.run.2 Q.hn Q.valid v hr.1 q hq, hs]
  simpa only [Regimes.readAfter, hstate] using heq

/-- A finite record source is either the current finalized block or an actual late raw
write before this cut. It does not require a future fast-lock cover. -/
def HealthyRecordSource (Q : HealthyPreparationQuery S A V) (cleanLabel : Nat)
    (y : Fin Q.params.n) (n : Nat) (R : SA.Blk Q.params.n (List (FG.Att Q.params.n))) : Prop :=
  R = (Q.trace.state y n).fg.F ∨ ∃ q s CV, q < n ∧ Q.trace.time q ≤ Q.run.2.horizon ∧
    cleanLabel + 2 * Q.params.k + 1 ≤ s ∧
    (SA.ResultAt Q.trace.projAC y q s R CV ∨ SA.OptimisticLockAt Q.trace.projAC y q s R CV)

theorem healthyRecordSource_iff (Q : HealthyPreparationQuery S A V) (cleanLabel : Nat)
    (y : Fin Q.params.n) (n : Nat) (R : SA.Blk Q.params.n (List (FG.Att Q.params.n))) :
    HealthyRecordSource S A V Q cleanLabel y n R ↔
      R = (Q.trace.state y n).fg.F ∨ ∃ q s CV, q < n ∧ Q.trace.time q ≤ Q.run.2.horizon ∧
        cleanLabel + 2 * Q.params.k + 1 ≤ s ∧
        (SA.ResultAt Q.trace.projAC y q s R CV ∨ SA.OptimisticLockAt Q.trace.projAC y q s R CV) :=
  Iff.rfl

section ConditionalSafety
variable (Q : HealthyPreparationQuery S A V) {c t₀ ΔF a : Time}
  (hsync : Q.trace.GSTRun (honestKeys S Q.run.2) ΔF Q.gst)
  (hreset : Healing.IsReset Q.trace (honestKeys S Q.run.2) Q.gst a)
  (ha : a ≤ Q.run.2.horizon)
  (hsnapshot : ∃ k, Healing.FirstCutAfter Q.trace k
    (Healing.cutZ Q.params.toParams Q.gst) ∧ Q.trace.time k ≤ Q.run.2.horizon)
  (hc : 0 ≤ c)
  (hread : ∀ y k t, (∃ q ≤ Q.run.2.events.length, k = cutMap S Q.run.2 Q.hn q) →
    Regimes.ReadPoint Q.trace k t →
    Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) c y t → t₀ ≤ t → t ≤ Q.run.2.horizon →
    Regimes.readAfter Q.trace y k t =
      (SA.lookup (Node.frame (Q.trace.state y k))
        (Q.trace.state y k).ac.latestConfirmed).getD (Q.trace.state y k).fg.F)

include hsync hreset ha hsnapshot hc hread

/-- Directed record preservation is transported at the original ordered engine cuts;
only read support is evaluated at the last local event. -/
theorem healthy_cut_tips_ancestor_of_interval
    {v : V} {i j : Nat} (hi : i ≤ Q.run.2.events.length)
    (hj : j ≤ Q.run.2.events.length) (hij : i ≤ j)
    (hfloori : t₀ ≤ (stateAt S Q.run.2 Q.hn v i).now)
    (hfloorj : t₀ ≤ (stateAt S Q.run.2 Q.hn v j).now)
    (hvi : Q.run.2.point.Ready (c + 1) v (Q.run.2.cutTime i))
    (hvj : Q.run.2.point.Ready (c + 1) v (Q.run.2.cutTime j))
    (hinterval : EffectiveRecordInterval Q.trace (honestKeys S Q.run.2) (Q.run.2.ownKey v)
      (cutMap S Q.run.2 Q.hn i) (cutMap S Q.run.2 Q.hn j)
      (Regimes.readAfter Q.trace (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)
        (stateAt S Q.run.2 Q.hn v i).now)) :
    Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2))
      (Regimes.readAfter Q.trace (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)
        (stateAt S Q.run.2 Q.hn v i).now)
      (Regimes.readAfter Q.trace (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn j)
        (stateAt S Q.run.2 Q.hn v j).now) := by
  have hp := reset_premises_of_healthy_query S A V Q hsync hreset ha hsnapshot
  have hri := healthy_stored_read_eq_record S A V Q hc hread hi hfloori hvi
  have hrj := healthy_stored_read_eq_record S A V Q hc hread hj hfloorj hvj
  rw [hrj]
  exact effective_record_of_interval hp.run hp.noColl
    (honest_ownKey (S := S) hvi.1) (cutMap_mono S Q.run.2 Q.hn hij) hinterval
      (by rw [hri]; exact .refl)

omit hsync hreset ha hsnapshot in
/-- Actual raw record sources admit frontier reads without a future origin cover. -/
theorem healthy_cut_tips_comparable_of_sources
    (cleanLabel : Nat)
    {u v : V} {i j : Nat} (hi : i ≤ Q.run.2.events.length)
    (hj : j ≤ Q.run.2.events.length)
    (hfloori : t₀ ≤ (stateAt S Q.run.2 Q.hn u i).now)
    (hfloorj : t₀ ≤ (stateAt S Q.run.2 Q.hn v j).now)
    (hu : Q.run.2.point.Ready (c + 1) u (Q.run.2.cutTime i))
    (hv : Q.run.2.point.Ready (c + 1) v (Q.run.2.cutTime j))
    (hcover : ∀ w k, (w = u ∧ k = i) ∨ (w = v ∧ k = j) →
      HealthyRecordSource S A V Q cleanLabel (Q.run.2.ownKey w) (cutMap S Q.run.2 Q.hn k)
          ((SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey w) (cutMap S Q.run.2 Q.hn k)))
            (Q.trace.state (Q.run.2.ownKey w) (cutMap S Q.run.2 Q.hn k)).ac.latestConfirmed).getD
              (Q.trace.state (Q.run.2.ownKey w) (cutMap S Q.run.2 Q.hn k)).fg.F))
    (hcompare : ∀ B B',
      HealthyRecordSource S A V Q cleanLabel (Q.run.2.ownKey u) (cutMap S Q.run.2 Q.hn i) B →
      HealthyRecordSource S A V Q cleanLabel (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn j) B' →
      Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2)) B B') :
    Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2))
      (Regimes.readAfter Q.trace (Q.run.2.ownKey u) (cutMap S Q.run.2 Q.hn i)
        (stateAt S Q.run.2 Q.hn u i).now)
      (Regimes.readAfter Q.trace (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn j)
        (stateAt S Q.run.2 Q.hn v j).now) := by
  rw [healthy_stored_read_eq_record S A V Q hc hread hi hfloori hu,
    healthy_stored_read_eq_record S A V Q hc hread hj hfloorj hv]
  exact hcompare _ _ (hcover u i (Or.inl ⟨rfl, rfl⟩))
    (hcover v j (Or.inr ⟨rfl, rfl⟩))

end ConditionalSafety

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
