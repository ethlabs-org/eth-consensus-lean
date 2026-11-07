module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RepairDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetSource
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.UpdateCalls
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync

public section

/-! # Stand-ins for the healed-safety port (open)

Statements published by their owners' modules, stated here under their final names and
signatures so the port compiles before they land:

* `Healing.Growing.operational_update_selection_at`: the operational selection at a bounded
  update after the drain, the counterpart of `Obligations.UpTo.operational_update_selection`;
* `Healing.Growing.ResetPremisesUpTo.late_result_prefix_votes_before_at`: the finite result
  induction of the reset kernel (its frozen boundary), consumed by the latest-votes wrapper;
* `Obligations.Growing.healthy_preparation_initialize_at`: the base timing and finite preparation
  schedule of a healed-safety query, the counterpart of
  `Obligations.healthy_preparation_initialize`.

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-- An honest post-drain proposal, by a proposer honest through its slot's votes, is selected at
every bounded update of a node honest at it. -/
theorem operational_update_selection_at {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hhold : p ∈ H (sp.ts u + sp.Δ)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hR : drainTime sp a ≤ sp.ts u)
    (hgu : gbar g + 4 * sp.Δ ≤ sp.ts u) (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    (hup : SA.UpdateAt tr.projAC y j u ell) :
    P ∈ ell.frame.tree ∧
      SA.getConfirmation sp (tr.projAC.state y j) ell.frame u = some P ∧
      ¬ SA.conflictsWithLock sp (tr.projAC.state y j).locks ell.frame (tr.time j) P ∧
      SA.fastSelect sp (tr.projAC.state y j) ell.frame u P = some P ∧
      tr.projAC.post j = SA.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u ∧
      (tr.projAC.post j).latestConfirmed =
        (SA.updateLatestConfirmed sp (tr.projAC.state y j) ell.frame P).latestConfirmed := by
  sorry

/-- Step 6 finite result induction, consumed by the latest-votes wrapper.
The explicit domain and stored-lock inputs are unchanged from the static boundary. -/
theorem ResetPremisesUpTo.late_result_prefix_votes_before_at {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x : Fin sp.n} {r s : Nat}
    (hx : x ∈ H (tr.time r))
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocksAt H) B C)
    (hrb : tr.time r ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts s)
    (hdomain : ∀ y i ell e, y ∈ H (tr.time i) → SA.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → s < e.msg.slot →
      (∀ z q e', q < i → Compose.Growing.HVoteAt tr H z q e' →
        s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B) →
      Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
        B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
    (hstored : ∀ y i ell e, y ∈ H (tr.time i) → SA.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → e.msg.slot = s + 1 → ∀ l ∈ (tr.projAC.state y i).locks,
        sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
        ∀ Y ∈ tr.HonestBlocksAt H, Y.root = l.block → Compatible (tr.HonestBlocksAt H) Y B) :
    ∀ i, tr.time i ≤ b → ∀ y, y ∈ H (tr.time i) → ∀ ell e,
      SA.CastAt tr.projAC y i ell e → s < e.msg.slot →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  sorry

end Consensus.Goldilocks.Healing.Growing

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape


variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- A healed-safety query with progress on `[ready, heal]` has a base timing and a finite
preparation schedule. -/
theorem healthy_preparation_initialize_at (Q : HealthyPreparationQueryAt S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run) :
    ∃ W : HealthyBaseTimingAt S A V Q, Nonempty (HealthyPreparationScheduleAt S A V Q W) := by
  sorry

end Consensus.Goldilocks.Obligations.Growing

end
