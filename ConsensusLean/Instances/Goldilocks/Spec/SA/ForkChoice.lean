module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Locks

@[expose] public section

/-! # Goldilocks SA: fork choice

fgsa-spec.tex §"Fork choice" (Figure "Goldilocks: fork choice"). The Goldfish score of `B` is
its number of supporters plus the number of equivocators. A walk starts at a block (also when
it is not in the walked tree) and descends through the eligible children in the walked tree,
taking the one with the greatest score, ties by root order (the smaller root wins), until no
child is eligible. A child is eligible when its parent is not a viable head, it is of the
current slot, or its score is a strict majority of the voters.

The walk is bounded by the size of the frame tree: each step goes to a child, so a walk in a
finite tree whose slots increase along parent edges (a well-formed frame) ends within that many
steps. When the eligible children have no best one (only outside a well-formed frame), the walk
stops. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} (sp : SAParams)

/-- `goldfish_score(votes, support_votes, s, B)`: equivocators count for every block. -/
noncomputable def goldfishScore (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int) (B : Blk sp.n FGP) :
    Nat :=
  (equivocators V.votes).ncard + (supporters Φ V s B).ncard

/-- `goldfish_eligible(Φ, t, votes, support_votes, s, B)`. -/
def goldfishEligible (Φ : Frm sp.n FGP) (t : Time) (V : View sp.n) (s : Int) (B : Blk sp.n FGP) :
    Prop :=
  (¬ ∃ W ∈ Φ.viableHeads, B.parent = some W.root) ∨ B.slot = sp.slot t ∨
    (voters V.votes).ncard < 2 * goldfishScore sp Φ V s B

/-- `C` is the best of `S` by score, ties by root order (the smaller root wins). -/
def IsBest (score : Blk sp.n FGP → Nat) (S : Set (Blk sp.n FGP)) (C : Blk sp.n FGP) : Prop :=
  C ∈ S ∧ ∀ D ∈ S, D ≠ C → score D < score C ∨ (score D = score C ∧ C.root < D.root)

open Classical in
/-- `ghost(anchor, tree, score, eligible)`, with at most `fuel` steps. -/
noncomputable def ghost (tree : Set (Blk sp.n FGP)) (score : Blk sp.n FGP → Nat)
    (eligible : Blk sp.n FGP → Prop) : Nat → Blk sp.n FGP → Blk sp.n FGP
  | 0, H => H
  | fuel + 1, H =>
    let children := {B | B ∈ tree ∧ B.parent = some H.root ∧ eligible B}
    if h : ∃ C, IsBest sp score children C then ghost tree score eligible fuel h.choose else H

/-- `get_head(𝒜, Φ, t, tree, votes, support_votes, s)`: the walk of `tree` from the anchor of
the full viable tree, with the Goldfish score and eligibility of the view. -/
noncomputable def getHead (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (tree : Set (Blk sp.n FGP)) (V : View sp.n) (s : Int) : Blk sp.n FGP :=
  ghost sp tree (goldfishScore sp Φ V s) (goldfishEligible sp Φ t V s) Φ.tree.ncard
    (getAnchor sp A Φ t)

/-- `ac_head(𝒜, Φ, t)`: the walk of the full viable tree with the latest view. -/
noncomputable def acHead (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) : Blk sp.n FGP :=
  getHead sp A Φ t (Φ.viableTree Φ.tree) (latestView sp A Φ t).1 (latestView sp A Φ t).2

end Consensus.Goldilocks.SA

end
