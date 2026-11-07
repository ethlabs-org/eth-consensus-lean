module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.ReadPoint

public section

/-! # Pending interface of the healthy confirmed supply under growing faults

Statements the healthy confirmed supply (`ConfirmedSupply`) consumes whose home modules are not on
this branch yet, under their agreed names:

* `Healing.Growing.operational_update_selection_at`, home the growing kernel's selection module;
* `healthy_preparation_initialize_at`, `healthy_repair_catch_at`, home
  `Lemmas/Growing/Obligations/Healthy/Preparation`;
* `healthy_cut_tips_ancestor_at`, home `Lemmas/Growing/Obligations/Healthy/CutTips`.

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- The frozen healthy-route selection contract. The proposer stays honest through its votes. -/
theorem operational_update_selection_at {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hhold : p ∈ H (sp.ts u + sp.Δ)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u)
    (hR : drainTime sp a ≤ sp.ts u) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hTb : sp.ts u + 6 * sp.Δ ≤ b) {y : Fin sp.n} {j : Nat}
    (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    (hup : SA.UpdateAt tr.projAC y j u ell) :
    P ∈ ell.frame.tree ∧
      SA.getConfirmation sp (tr.projAC.state y j) ell.frame u = some P ∧
      ¬ SA.conflictsWithLock sp (tr.projAC.state y j).locks ell.frame (tr.time j) P ∧
      SA.fastSelect sp (tr.projAC.state y j) ell.frame u P = some P ∧
      tr.projAC.post j = SA.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u ∧
      (tr.projAC.post j).latestConfirmed =
        (SA.updateLatestConfirmed sp (tr.projAC.state y j) ell.frame P).latestConfirmed := by
  sorry

end Consensus.Goldilocks.Healing.Growing

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The preparation initializer: a base timing and a finite reset schedule. -/
theorem healthy_preparation_initialize_at (Q : HealthyPreparationQueryAt S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run) :
    ∃ W : HealthyBaseTimingAt S A V Q, Nonempty (HealthyPreparationScheduleAt S A V Q W) := by
  sorry

/-- `Catch(2Δ)` over the canonical growing trace of a healthy preparation query. -/
theorem healthy_repair_catch_at (Q : HealthyPreparationQueryAt S A V) :
    Healing.Growing.CatchRun Q.trace Q.keys Q.gst (2 * Q.params.Δ) := by
  sorry

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
