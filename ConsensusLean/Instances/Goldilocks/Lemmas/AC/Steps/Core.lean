module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk

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
  have hT : Φ.viableTree dom ⊆ Φ.tree := fun X hX => hdom hX.1
  have hCt : C ∈ Φ.tree := hviab.elim (fun h => hT h) fun h => mem_of_anc h hΦ.fcRoot_mem
  unfold getHead
  set a := getAnchor sp A Φ t
  -- the anchor is a live lock block or `fc_root`, and at least as deep as `fc_root`
  obtain ⟨haS, hdep⟩ : a ∈ liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot} ∧
      depth Φ Φ.fcRoot ≤ depth Φ a := by
    unfold a getAnchor
    cases hd : deepest Φ (liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}) with
    | none => exact ⟨Or.inr rfl, le_rfl⟩
    | some D =>
      obtain ⟨hD, hmax⟩ := deepest_mem hd
      rw [Option.getD_some]
      refine ⟨hD, ?_⟩
      by_cases he : Φ.fcRoot = D
      · exact he ▸ le_rfl
      · rcases hmax _ (Or.inr rfl) he with h | h <;> omega
  have hat : a ∈ Φ.tree :=
    haS.elim (fun h => h.1) fun h => (Set.mem_singleton_iff.1 h) ▸ hΦ.fcRoot_mem
  have hroot : Φ.Anc a Φ.fcRoot → a = Φ.fcRoot := fun h => by
    by_contra hne
    have := depth_lt_of_anc hΦ h hne hΦ.fcRoot_mem
    omega
  have key : Φ.Anc C a → Φ.Anc C (ghost sp (Φ.viableTree dom) (goldfishScore sp Φ V σ)
      (goldfishEligible sp Φ t V σ) Φ.tree.ncard a) := fun h => h.trans (anc_ghost hT _ hat)
  have hcomp : Compatible Φ.tree a C := by
    rcases haS with h | h
    · exact (hlocks a h).imp (anc_tree_of_anc_U hU hΦ hΦU h.1 · hCt)
        (anc_tree_of_anc_U hU hΦ hΦU hCt · h.1)
    · rw [Set.mem_singleton_iff.1 h]
      exact hviab.imp (fun h => h.2.1) id
  rcases hcomp with haC | hCa
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

end Consensus.Goldilocks.SA

end
