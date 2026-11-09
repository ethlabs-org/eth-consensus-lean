module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.RelTrace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain

public section

/-! # Goldilocks SA: the vote-transfer core

The head walk of a vote (or a proposal) from the anchor `get_anchor` over the viable tree of a
domain extends a block `C` when `C` is in that viable tree or at or below `fc_root`, every live
lock block is compatible with `C`, and at every block on the way the child towards `C` is the
best eligible child (lock compatibility is read inside a coherent `U ⊇ Φ.tree`: the
`U`-ancestry between two blocks of a well-formed frame's tree is the tree's). The anchor (the
deepest of the live lock blocks and `fc_root`) is then compatible with `C`: if it extends `C`
the walk, which only descends, does too; otherwise the walk passes `C` (`anc_ghost_of_best`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-- Structural facts about a walk start. Compatibility and floor obligations are local to
the block and regime of a transfer, not requirements on every call.

## Call-local start premises

`anc_getHeadFrom` takes `hfloor : Φ.Anc Φ.fcRoot (st A Φ t V σ)` and
`hcompatible : Compatible Φ.tree (st A Φ t V σ) C` for its target `C`.
The transfer proofs that use this kernel must supply these at the actual call, view and
label: neither compatibility with all possible targets nor dominance over all live locks
is a structural law. Membership and invariance under updating `votedSlot` are the only
unconditional requirements. -/
structure WalkStartLaw (st : WalkStartFn sp FGP) : Prop where
  mem : ∀ (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (V : View sp.n) (σ : Int),
    FrameOK Φ → st A Φ t V σ ∈ Φ.tree
  votedSlot : ∀ (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (V : View sp.n) (σ v : Int),
    st { A with votedSlot := v } Φ t V σ = st A Φ t V σ

/-- The parent's deepest-anchor start satisfies the walk-start laws. -/
theorem walkStartLaw_parentWalkStartFn : WalkStartLaw (parentWalkStartFn sp (FGP := FGP)) := by
  refine ⟨?_, ?_⟩
  · intro A Φ t V σ hΦ
    change getAnchor sp A Φ t ∈ Φ.tree
    unfold getAnchor
    cases hd : deepest Φ (liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}) with
    | none => exact hΦ.fcRoot_mem
    | some D =>
      rcases (deepest_mem hd).1 with h | h
      · exact h.1
      · exact (Set.mem_singleton_iff.1 h) ▸ hΦ.fcRoot_mem
  · intros; rfl

/-- Transfer from a structural start, with the floor and target compatibility supplied
at this walk. No dominance over unrelated live locks is needed. -/
theorem anc_getHeadFrom {st : WalkStartFn sp FGP} (hst : WalkStartLaw st)
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (A : SAState sp.n) (t : Time)
    (V : View sp.n) (σ : Int) {dom : Set (Blk sp.n FGP)} (hdom : dom ⊆ Φ.tree)
    (hdomA : ∀ B ∈ dom, ∀ X, Φ.Anc X B → X ∈ dom) {C : Blk sp.n FGP}
    (hviab : C ∈ Φ.viableTree dom ∨ Φ.Anc C Φ.fcRoot)
    (hfloor : Φ.Anc Φ.fcRoot (st A Φ t V σ))
    (hcompatible : Compatible Φ.tree (st A Φ t V σ) C)
    (hbest : ∀ X Cx : Blk sp.n FGP, Cx ∈ Φ.viableTree dom → Cx.parent = some X.root →
      Φ.Anc Cx C →
      IsBest sp (goldfishScore sp Φ V σ)
        {B | B ∈ Φ.viableTree dom ∧ B.parent = some X.root ∧ goldfishEligible sp Φ t V σ B}
        Cx) :
    Φ.Anc C (getHeadFrom sp (st A Φ t V σ) Φ t (Φ.viableTree dom) V σ) := by
  have hT : Φ.viableTree dom ⊆ Φ.tree := fun X hX => hdom hX.1
  have hCt : C ∈ Φ.tree := hviab.elim (fun h => hT h) fun h => mem_of_anc h hΦ.fcRoot_mem
  let a := st A Φ t V σ
  have hat : a ∈ Φ.tree := hst.mem A Φ t V σ hΦ
  have hroot : Φ.Anc a Φ.fcRoot → a = Φ.fcRoot := fun h => by
    exact Anc.antisymm hΦ.coherent h hfloor
  have key : Φ.Anc C a → Φ.Anc C (ghost sp (Φ.viableTree dom) (goldfishScore sp Φ V σ)
      (goldfishEligible sp Φ t V σ) Φ.tree.ncard a) := fun h => h.trans (anc_ghost hT _ hat)
  rcases hcompatible with haC | hCa
  swap; · exact key hCa
  rcases hviab with hCv | hCf
  swap; · exact key (hroot (haC.trans hCf) ▸ hCf)
  obtain ⟨hCdom, hfC, W, hWdom, hW, hCW⟩ := hCv
  have hfa : Φ.Anc Φ.fcRoot a :=
    (anc_total hΦ.coherent hfC haC).elim id fun h => hroot h ▸ Relation.ReflTransGen.refl
  refine anc_ghost_of_best hΦ.coherent hT (hΦ.finite.subset hT) hCt _ haC
    (Set.ncard_le_ncard (fun X hX => hT hX.1) hΦ.finite) fun X haX hXC hne => ?_
  obtain rfl | ⟨Cx, e, hCxC⟩ := Relation.ReflTransGen.cases_head_iff.1 hXC
  · exact absurd rfl hne
  have hCx : Cx ∈ Φ.viableTree dom :=
    ⟨hdomA C hCdom Cx hCxC, (hfa.trans haX).tail e, W, hWdom, hW, hCxC.trans hCW⟩
  exact ⟨Cx, hbest X Cx hCx e.2.2 hCxC, hCxC⟩

/-- **The vote-transfer core.** -/
theorem anc_getHead {U : Set (Blk sp.n FGP)} (hU : Coherent U) {Φ : Frm sp.n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) (A : SAState sp.n) (t : Time)
    (V : View sp.n) (σ : Int) {dom : Set (Blk sp.n FGP)} (hdom : dom ⊆ Φ.tree)
    (hdomA : ∀ B ∈ dom, ∀ X, Φ.Anc X B → X ∈ dom) {C : Blk sp.n FGP}
    (hviab : C ∈ Φ.viableTree dom ∨ Φ.Anc C Φ.fcRoot)
    (hlocks : ∀ L ∈ liveLockBlocks sp A.locks Φ t, Compatible U L C)
    (hbest : ∀ X Cx : Blk sp.n FGP, Cx ∈ Φ.viableTree dom → Cx.parent = some X.root →
      Φ.Anc Cx C →
      IsBest sp (goldfishScore sp Φ V σ)
        {B | B ∈ Φ.viableTree dom ∧ B.parent = some X.root ∧ goldfishEligible sp Φ t V σ B}
        Cx) :
    Φ.Anc C (getHead sp A Φ t (Φ.viableTree dom) V σ) := by
  have hS : liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot} ⊆ Φ.tree := by
    rintro B (hB | hB)
    · exact hB.1
    · exact (Set.mem_singleton_iff.1 hB) ▸ hΦ.fcRoot_mem
  obtain ⟨D, hD⟩ := exists_deepest hΦ hS ⟨Φ.fcRoot, Or.inr rfl⟩
  have ha : getAnchor sp A Φ t = D := by unfold getAnchor; rw [hD]; rfl
  have hCt : C ∈ Φ.tree := hviab.elim (fun h => hdom h.1) fun h => mem_of_anc h hΦ.fcRoot_mem
  have hcomp : Compatible Φ.tree (getAnchor sp A Φ t) C := by
    rw [ha]
    rcases (deepest_mem hD).1 with h | h
    · exact (hlocks D h).imp (anc_tree_of_anc_U hU hΦ hΦU h.1 · hCt)
        (anc_tree_of_anc_U hU hΦ hΦU hCt · h.1)
    · rw [Set.mem_singleton_iff.1 h]
      exact hviab.imp (fun h => h.2.1) id
  have hfloor : Φ.Anc Φ.fcRoot (getAnchor sp A Φ t) := by
    rw [ha]
    have hcomp : Compatible Φ.tree Φ.fcRoot D := by
      rcases (deepest_mem hD).1 with h | h
      · exact (liveLockBlock_candidate hΦ h).imp (fun h => h.2.1) id
      · exact (Set.mem_singleton_iff.1 h) ▸ Or.inl .refl
    rcases hcomp with h | h
    · exact h
    · by_cases he : D = Φ.fcRoot
      · exact he ▸ .refl
      · have := depth_lt_of_anc hΦ h he hΦ.fcRoot_mem
        rcases (deepest_mem hD).2 _ (Or.inr rfl) (Ne.symm he) with h | ⟨h, -⟩ <;> omega
  exact anc_getHeadFrom walkStartLaw_parentWalkStartFn hΦ A t V σ hdom hdomA hviab
    hfloor hcomp hbest

end Consensus.Goldilocks.SA

end
