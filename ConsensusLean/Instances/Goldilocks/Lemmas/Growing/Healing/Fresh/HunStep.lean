module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Actions
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # Step lemmas for the floor−1 contesting-writer case of warm vote unanimity

Two single-step facts over the Spec functions, read by the paper trace against the shadow
`honest_vote_heads_eq_at` at `u = s + 1` (a caster `y` keeps a slot-`s` lock on a block `D`
whose only viable descendant `W` it received after the vote freeze). These are **step lemmas,
not a refutation**: no run is constructed here.

* `getHead_eq_anchor_of_no_child`, `tryVote_head_eq_anchor_of_no_child`: when no block of the
  walked tree is a child of the anchor, the walk stops at the anchor, so the vote's head is the
  anchor.
* `viableAncestor_eq_self_iff`, `mem_liveLocks_self_iff`: a live lock on a block `D` strictly
  above `fc_root` keeps its block exactly when some viable head of the frame extends `D`.
-/

namespace Consensus.Goldilocks.Shadow.PU.HunStep

open AC

variable {FGP : Type} (sp : ACParams)

/-- The walk with no child of its start in the walked tree stops at its start. -/
theorem ghost_eq_of_no_child (tree : Set (Blk sp.n FGP)) (score : Blk sp.n FGP → Nat)
    (eligible : Blk sp.n FGP → Prop) (fuel : Nat) (H : Blk sp.n FGP)
    (hno : ∀ B ∈ tree, B.parent ≠ some H.root) :
    ghost sp tree score eligible fuel H = H := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have hnb : ¬ ∃ C, IsBest sp score
        {B | B ∈ tree ∧ B.parent = some H.root ∧ eligible B} C :=
      fun ⟨_, hC, _⟩ => hno _ hC.1 hC.2.1
    simp only [ghost, hnb, dite_false]

/-- **Step lemma (walk).** When no block of the walked tree is a child of the anchor, the head
is the anchor. -/
theorem getHead_eq_anchor_of_no_child (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (tree : Set (Blk sp.n FGP)) (V : View sp.n) (s : Int)
    (hno : ∀ B ∈ tree, B.parent ≠ some (getAnchor sp A Φ t).root) :
    getHead sp A Φ t tree V s = getAnchor sp A Φ t :=
  ghost_eq_of_no_child sp _ _ _ _ _ hno

/-- The state of `try_vote` after its unlock (`A₁` there). -/
def unlocked (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) : ACState sp.n :=
  if 0 < sp.slot t then
    { A with locks := unlock sp A.locks Φ t ((sp.slot t : Int) - 1)
                        (mergedVoteView sp A Φ (sp.slot t)) }
  else A

/-- **Step lemma (vote).** In `try_vote` at slot `s = slot(t)`, with `A₁` the state after the
unlock: if the anchor of `A₁` is `D` and no block of the viable tree of the vote domain is a child
of `D`, every emitted vote heads to `D`. -/
theorem tryVote_head_eq_anchor_of_no_child (self : Fin sp.n) (A : ACState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) {D : Blk sp.n FGP}
    (hanchor : getAnchor sp
      (unlocked sp A Φ t) Φ t = D)
    (hno : ∀ B ∈ Φ.viableTree (voteDomain sp
      (unlocked sp A Φ t) Φ (sp.slot t)),
      B.parent ≠ some D.root) :
    ∀ em ∈ (tryVote sp self A Φ t).2, em.msg.head = D.root := by
  intro em hem
  subst hanchor
  have hH := getHead_eq_anchor_of_no_child sp _ Φ t _ (mergedVoteView sp A Φ (sp.slot t))
    ((sp.slot t : Int) - 1) hno
  unfold unlocked at hno hH ⊢
  unfold tryVote at hem
  dsimp only at hem
  split_ifs at hem <;> simp_all

variable {n : Nat} {ACP : Type}

/-- **Step lemma (projection).** In a well-formed frame, a block `D` of the tree strictly above
`fc_root` is its own viable ancestor exactly when some viable head of the frame extends it. -/
theorem viableAncestor_eq_self_iff {Φ : Frame n FGP ACP} (hΦ : FrameOK Φ)
    {D : Block n FGP ACP} (hD : D ∈ Φ.tree) (hFD : Φ.Anc Φ.fcRoot D)
    (hDF : ¬ Φ.Anc D Φ.fcRoot) :
    Φ.viableAncestor D = D ↔ ∃ W ∈ Φ.tree, W ∈ Φ.viableHeads ∧ Φ.Anc D W := by
  constructor
  · intro he
    have hc := (AC.viableAncestor_spec hΦ hD).2.1
    rw [he] at hc
    rcases hc with h | ⟨-, -, W, hW, hWv, hDW⟩
    · exact absurd h hDF
    · exact ⟨W, hW, hWv, hDW⟩
  · rintro ⟨W, hW, hWv, hDW⟩
    exact AC.viableAncestor_self hΦ hD (Or.inl ⟨hD, hFD, W, hW, hWv, hDW⟩)

/-- **Step lemma (live lock).** In a well-formed frame, a live lock `l` on a block `D` of the tree
strictly above `fc_root` survives `live_locks` with its block unchanged exactly when some viable
head of the frame extends `D`; otherwise its image is a block strictly below `D`. -/
theorem mem_liveLocks_self_iff (Φ : Frm sp.n FGP) (hΦ : FrameOK Φ) {t : Time} {l : Lock}
    (hlive : l.LiveAt sp t) {D : Blk sp.n FGP} (hD : D ∈ Φ.tree) (hDr : D.root = l.block)
    (hFD : Φ.Anc Φ.fcRoot D) (hDF : ¬ Φ.Anc D Φ.fcRoot) :
    l ∈ liveLocks sp {l} Φ t ↔ ∃ W ∈ Φ.tree, W ∈ Φ.viableHeads ∧ Φ.Anc D W := by
  rw [← viableAncestor_eq_self_iff hΦ hD hFD hDF]
  constructor
  · rintro ⟨l₀, hl₀, B, hB, hBr, -, he⟩
    obtain rfl : l₀ = l := hl₀
    obtain rfl : B = D := hΦ.coherent.1 hB hD (hBr.trans hDr.symm)
    have hr : (Φ.viableAncestor B).root = B.root := by
      have := congrArg Lock.block he
      simp only at this
      rw [← this, hDr]
    exact hΦ.coherent.1 (AC.viableAncestor_anc hΦ hB).1 hB hr
  · intro he
    exact ⟨l, rfl, D, hD, hDr, hlive, by rw [he, hDr]⟩

end Consensus.Goldilocks.Shadow.PU.HunStep

end
