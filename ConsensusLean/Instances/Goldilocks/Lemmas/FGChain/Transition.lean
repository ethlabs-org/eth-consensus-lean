module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.State

public section

/-! # Goldilocks FG: one block of the state transition

The step facts that the chain-level proofs share: the chain fold one block at a time, the
counting of a block's attestations (it changes only `fin`, `prog` and `target`), and the
finality step (`bestFinal` picks the highest pending pair with a finality quorum; the prune
keeps the pairs above the new `h_F`). -/

namespace Consensus.Goldilocks.FG

namespace ChainState

variable {n : Nat}

/-- Counting attestations changes only the finality, progress and target bits. -/
theorem foldl_processAtt_eq (σ : ChainState n) (atts : List (Att n)) :
    ∃ fin prog target, atts.foldl processAtt σ =
      { σ with fin := fin, prog := prog, target := target } := by
  sorry

/-- Counting attestations keeps `Q_target ⊆ Q_prog`. -/
theorem foldl_processAtt_target_subset (σ : ChainState n) (atts : List (Att n))
    (h : σ.target ⊆ σ.prog) :
    (atts.foldl processAtt σ).target ⊆ (atts.foldl processAtt σ).prog := by
  sorry

end ChainState

namespace FGParams

variable (gp : FGParams)

theorem chainState_nil : gp.chainState [] = some (ChainState.init gp) := by
  sorry

theorem chainState_append (c : List (FGBlock gp.n)) (B : FGBlock gp.n) :
    gp.chainState (c ++ [B]) = (gp.chainState c).bind (gp.stateTransition · B) := by
  sorry

/-- Induction over the chains that have a state, one block at a time. -/
theorem chainState_induction {P : List (FGBlock gp.n) → ChainState gp.n → Prop}
    (init : P [] (ChainState.init gp))
    (step : ∀ c σ B σ', gp.chainState c = some σ → P c σ → gp.stateTransition σ B = some σ' →
      P (c ++ [B]) σ')
    {c : List (FGBlock gp.n)} {σ : ChainState gp.n} (h : gp.chainState c = some σ) : P c σ := by
  sorry

theorem stateTransition_eq_some {σ σ' : ChainState gp.n} {B : FGBlock gp.n} :
    gp.stateTransition σ B = some σ' ↔
      (B.proposer = gp.proposer B.slot ∧ σ.s < B.slot ∧
        ∀ a ∈ B.atts, a.WellFormed ∧ σ.validAtt a) ∧
      gp.heightEvents
        { B.atts.foldl ChainState.processAtt { σ with s := B.slot } with L := B.root } = σ' := by
  sorry

/-- `bestFinal` picks a pending pair with a finality quorum, of the greatest height among
them. -/
theorem bestFinal_eq_some {σ : ChainState gp.n} {r : Nat × Nat} (h : gp.bestFinal σ = some r) :
    r ∈ σ.pending ∧ gp.q ≤ (σ.fin r.1).card ∧
      ∀ p ∈ σ.pending, gp.q ≤ (σ.fin p.1).card → p.1 ≤ r.1 := by
  sorry

/-- `bestFinal` is none only when no pending pair has a finality quorum. -/
theorem bestFinal_eq_none {σ : ChainState gp.n} (h : gp.bestFinal σ = none) :
    ∀ p ∈ σ.pending, (σ.fin p.1).card < gp.q := by
  sorry

/-- The finality step moves `(F, h_F)` to a pending pair with a finality quorum or keeps it,
and the prune keeps the pairs above the new `h_F`. -/
theorem finalizePrune_eq (σ : ChainState gp.n) :
    ∃ F hF, gp.finalizePrune σ =
        { σ with F := F, hF := hF, pending := σ.pending.filter (fun p => hF < p.1) } ∧
      ((F = σ.F ∧ hF = σ.hF) ∨ ((hF, F) ∈ σ.pending ∧ gp.q ≤ (σ.fin hF).card)) := by
  sorry

end FGParams

end Consensus.Goldilocks.FG

end
