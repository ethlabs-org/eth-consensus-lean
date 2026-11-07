module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.FrozenFrame

public section

/-! # Frames of the suffix comparison, under growing faults

The frame suppliers of `reset_suffix_best_at` (static `Healing/Outcome/SupplierViews`,
`SupplierFrames`). The operational proposer is honest through `t_{s+1} + hold`, every voter at
its own cast, and every relayed acceptance at its own cut:

* `reset_winner_voter_tree_at`: an ancestor of a viable current proposal above the voter's
  anchor is in the voter's viable tree;
* `reset_competitor_reflect_at`: a voter's viable competitor of the proposal is in the
  proposer's viable tree (pre-freeze competitors by `reset_frozen_frame_at`). -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)
open Regimes.Growing (hold)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- Any ancestor of a viable current proposal above the voter's anchor is in the voter's viable
tree, for a voter honest at its cast. -/
theorem reset_winner_voter_tree_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {j u : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time j))
    (hc : SA.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u)
    {P C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame u))
    (hCP : Anc (tr.HonestBlocksAt H) C P)
    (haC : Anc (tr.HonestBlocksAt H) (SA.getAnchor sp e.readPoint ell.frame (tr.time j)) C) :
    C ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame u) := by
  sorry

/-- A viable competitor of the proposal at a slot-`(s+1)` voter honest at its cast, a child of a
viable head below the proposal's parent, is in the viable tree of the proposer, honest through
`t_{s+1} + hold`. -/
theorem reset_competitor_reflect_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H (sp.ts (s + 1 : Nat) + hold sp)) (hdesignated : p = proposer (s + 1))
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = s + 1)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ellp) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hy : y ∈ H (tr.time j)) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hjoin : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    {Q X B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hQt : Q ∈ ellp.frame.tree) (hPQ : P.parent = some Q.root)
    (hXQ : ellp.frame.Anc X Q) (hBP : B ≠ P)
    (hXv : X ∈ ellp.frame.viableHeads) (hBX : B.parent = some X.root)
    (hB : B ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1))) :
    B ∈ ellp.frame.viableTree ellp.frame.tree := by
  sorry

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
