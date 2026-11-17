module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Service

public section

/-! # Goldilocks runs under `Sleepy`: the head support at a cut (interface)

The Sleepy safety induction from time `0` (claims A1.6, its "own induction from time 0"; the same
induction is R.1, `sleepySafe`; `Lemmas/Compose/Sleepy`). This file holds what the reads of
it use, node-local at one cut of `y`:

* `HeadSupport R` (G1, G2): the anchor is compatible with `R`, and `R` is at or below the anchor,
  or `R` is in the viable tree with a strict majority of the latest view's voters as supporters
  (with `SA.anc_acHead`, the head extends `R`, and `ac_confirmed` is the record's block). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **G1, G2 for `R` at cut `i` of `y`**: the anchor is compatible with `R`; `R` is at or below
it, or `R` is viable and supported by a strict majority of the latest view's voters. -/
structure HeadSupport (tr : GoldilocksTrace sp ro) (y : Fin sp.n) (i : Nat)
    (R : SA.Blk sp.n (List (FG.Att sp.n))) : Prop where
  /-- G1: the anchor is compatible with `R`. -/
  anchor_compatible : Compatible (Node.frame (tr.state y i)).tree
    (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) (tr.time i)) R
  /-- G2: `R` is at or below the anchor, or viable with a strict supporter majority. -/
  support : (Node.frame (tr.state y i)).Anc R
      (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) (tr.time i)) ∨
    (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
      (SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i))
          (tr.time i)).1.votes).ncard <
        2 * (SA.supporters (Node.frame (tr.state y i))
          (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) (tr.time i)).1
          (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) (tr.time i)).2
          R).ncard)

end Consensus.Goldilocks.Compose

end
