module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Service

public section

/-! # Goldilocks runs under `Sleepy`: the facts the Service milestone reads (interface)

The Sleepy safety induction from time `0` (claims A1.6, its "own induction from time 0"; the same
induction is R.1, `sleepySafe`; workbench#11, `Lemmas/Compose/Sleepy`). This file holds what A1.6
and A1.7 read of it, node-local at one cut of `y`:

* `HeadSupport R` (G1, G2): the anchor is compatible with `R`, and `R` is at or below the anchor,
  or `R` is in the viable tree with a strict majority of the latest view's voters as supporters
  (with `SA.anc_acHead`, the head extends `R`, and `ac_confirmed` is the record's block);
* `ServedFacts` at a cut where `y` is served (`ServedAt`): `HeadSupport` of the record's block,
  and the record step (G3: across the cut the record moves to a descendant); supplied by
  `sleepy_served_facts` (`Lemmas/Compose/Sleepy/Served`, which imports this file);
* `HeadSupport` is also what A1.7 reads (`served_head_support` after the update of `slot(t) − 2` or
  `slot(t) − 1`). -/

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

/-- **The served-cut facts** of `y` at cut `i`: G1/G2 for the record's block, and the record
step (G3). -/
structure ServedFacts (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (y : Fin sp.n) (i : Nat) :
    Prop where
  /-- G1, G2 for the record's block. -/
  head : ∀ R, RecordAt tr y i R → HeadSupport tr y i R
  /-- G3: across the cut, the record moves to a descendant (inside the honest blocks). -/
  record_step : ∀ E ∈ tr.HonestBlocks H, E.root = (tr.state y i).ac.latestConfirmed →
    ∃ E' ∈ tr.HonestBlocks H, E'.root = (tr.state y (i + 1)).ac.latestConfirmed ∧
      Anc (tr.HonestBlocks H) E E'

end Consensus.Goldilocks.Compose

end
