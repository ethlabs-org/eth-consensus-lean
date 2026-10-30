module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant

public section

/-! # Goldilocks FG store: the frame (C0.2, the frame step, G0.4)

From the reachable-state statements: accepting a block moves `Σ.F` only to a descendant
(the finalized tip of the new block's chain, between the old tip and the block); the frame of
the new state is the frame step by the block; and the frame of a reachable state is well
formed (its tree, the accepted blocks above `Σ.F`, is finite, coherent and rooted, and the
fork-choice root `Σ.J` or `Σ.F` lies in it). -/
namespace Consensus.Goldilocks.Store

variable (P : Params) (ACP : Type)

/-- No accepted block names an unheld root as its parent. -/
private theorem parent_ne_of_none {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) {r : Nat} (hn : st.blocks r = none) :
    ∀ V ∈ st.tree, V.parent ≠ some r := by
  intro V hV hp
  obtain ⟨-, -, -, hG⟩ := accepted_tree P ACP acp₀ st hr
  rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hG V hV) with rfl | ⟨Z, -, hZ⟩
  · cases hp
  · have hZr : st.blocks Z.root = some Z := hZ.1
    rw [Option.some.inj (hZ.2.2.symm.trans hp), hn] at hZr
    cases hZr

/-- An accepted block keeps `Σ.F` or moves it to a descendant named by the block's state. -/
private theorem onBlock_F {P : Params} {ACP : Type} {st st' : Store P ACP}
    {B : NodeBlock P ACP} (h : st.onBlock B = some st') :
    st'.F = st.F ∨ (st'.blocks (st'.σ B.root).F = some st'.F ∧ st'.Anc st.F st'.F) := by
  obtain ⟨pr, σ', -, -, -, -, -, rfl⟩ := onBlock_eq_some h
  set st₁ : Store P ACP :=
    { st with blocks := Function.update st.blocks B.root (some B),
              σ := Function.update st.σ B.root σ' }
  obtain ⟨atts, he⟩ := addAtts_eq (updateFinality st₁ σ') B.fgPayload
  obtain ⟨hb, hσ, -, -, -, hF⟩ := updateFinality_spec st₁ σ'
  have ht : ({ updateFinality st₁ σ' with atts := atts } : Store P ACP).tree = st₁.tree := by
    simp only [tree, hb]
  have h₁ : st₁.σ B.root = σ' := Function.update_self ..
  rw [he, Store.Anc, ht]
  simp only [hb, hσ, h₁]
  exact hF.imp id fun h => ⟨h.1, h.2.1⟩

/-- The frame step from the facts of an accepted block `B`: `T'` is the tree with `B`, which no
block of `T` names as its parent, and `F ⪯ F' ⪯ B` in `T'`. -/
private theorem frameStep_of {n : Nat} {FGP ACP : Type} {T T' : Set (Block n FGP ACP)}
    {B F F' c c' : Block n FGP ACP} {v v' : Set (Block n FGP ACP)} (hT' : T' = insert B T)
    (hB : B ∉ T) (hX : ∀ V ∈ T, V.parent ≠ some B.root) (hBB : B.parent ≠ some B.root)
    (hF : F ∈ T) (hFB : Goldilocks.Anc T' F B) (hFF' : Goldilocks.Anc T' F F')
    (hF'B : Goldilocks.Anc T' F' B) :
    FrameStep ⟨{X | X ∈ T ∧ Goldilocks.Anc T F X}, F, c, v⟩ B
      ⟨{X | X ∈ T' ∧ Goldilocks.Anc T' F' X}, F', c', v'⟩ := by
  subst hT'
  have hR : insert B {X | X ∈ T ∧ Goldilocks.Anc T F X} =
      {Y | Y ∈ insert B T ∧ Goldilocks.Anc (insert B T) F Y} := by
    ext Y
    simp only [Set.mem_insert_iff, Set.mem_ofPred_eq]
    constructor
    · rintro (rfl | ⟨hY, hFY⟩)
      · exact ⟨Or.inl rfl, hFB⟩
      · exact ⟨Or.inr hY, hFY.mono (Set.subset_insert _ _)⟩
    · rintro ⟨rfl | hY, hFY⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hY, hFY.of_insert hY hX⟩
  obtain ⟨Y, hFY, e⟩ := ((Relation.ReflTransGen.cases_tail_iff _ _ _).1 hFB).resolve_left
    fun h => hB (h ▸ hF)
  have hYT : Y ∈ T := e.1.resolve_left fun h => by subst h; exact hBB e.2.2
  refine ⟨fun h => hB h.1, ⟨Y, ⟨hYT, Anc.of_insert hFY hYT hX⟩, e.2.2⟩, ?_, ?_, ?_⟩ <;>
    dsimp only <;> rw [hR]
  · exact Anc.restrict .refl hFF'
  · exact Anc.restrict hFF' hF'B
  · ext X
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hXT, hF'X⟩
      exact ⟨⟨hXT, hFF'.trans hF'X⟩, Anc.restrict hFF' hF'X⟩
    · rintro ⟨hXT, hF'X⟩
      exact ⟨hXT.1, hF'X.mono fun _ h => h.1⟩

/-- **C0.2, the `Σ` half.** -/
theorem finalized_monotone : FinalizedMonotone P ACP := by
  intro acp₀ st _
  refine ⟨fun B st' h => ?_, fun a => ?_⟩
  · rcases onBlock_F h with he | ⟨-, hFF'⟩
    · rw [he]
      exact .refl
    · exact hFF'
  · obtain ⟨atts, he⟩ := st.onAttestation_eq a
    rw [he]

/-- **The FG kernel of the frame step.** -/
theorem accept_is_frame_step : AcceptIsFrameStep P ACP := by
  intro acp₀ st hr
  refine ⟨fun B st' h => ?_, fun a => ?_⟩
  · obtain ⟨pr, -, hpr, hnew, hpr', hFB, -, -⟩ := onBlock_eq_some h
    have hr' : st'.Reachable acp₀ := hr.tail (Or.inl ⟨B, h⟩)
    have hT' : st'.tree = insert B st.tree := (tree_grows P ACP acp₀ st hr).1 B st' h
    have hF'B : st'.Anc st'.F B := by
      rcases onBlock_F h with he | ⟨hb, -⟩
      · rw [he, Store.Anc, hT']
        exact hFB
      · obtain ⟨-, ⟨X, hXT, hXr, hXB⟩, -⟩ :=
          entry_state_of_source P ACP acp₀ st' hr' B (hT' ▸ Set.mem_insert _ _)
        have hX : st'.blocks X.root = some X := hXT
        rw [hXr, hb] at hX
        obtain rfl := Option.some.inj hX
        exact hXB
    refine frameStep_of hT' (fun hB => by cases hnew.symm.trans hB) (parent_ne_of_none hr hnew)
      (fun he => ?_) (cache_invariants P ACP acp₀ st hr).1 (hT' ▸ hFB)
      ((finalized_monotone P ACP acp₀ st hr).1 B st' h) hF'B
    rw [hpr, Option.some.injEq] at he
    rw [he, hnew] at hpr'
    cases hpr'
  · obtain ⟨atts, he⟩ := st.onAttestation_eq a
    rw [he]
    rfl

/-- **G0.4 (height).** -/
theorem frame_realization : FrameRealization P ACP := by
  intro acp₀ st hr
  obtain ⟨hfin, hcoh, -, -⟩ := accepted_tree P ACP acp₀ st hr
  obtain ⟨hF, hJ, hFJ, -⟩ := cache_invariants P ACP acp₀ st hr
  have hfc : st.fcRoot ∈ st.tree ∧ st.Anc st.F st.fcRoot := by
    unfold fcRoot
    split_ifs
    exacts [⟨hJ, hFJ⟩, ⟨hF, .refl⟩]
  refine ⟨⟨hfin.subset fun _ h => h.1, hcoh.mono fun _ h => h.1,
    ⟨⟨hF, .refl⟩, fun _ hC => Anc.restrict .refl hC.2⟩, hfc,
    Anc.restrict .refl hfc.2, fun _ h => ⟨h.1, h.2.1⟩, fun _ h => Anc.restrict hfc.2 h.2.2.1⟩,
    ?_⟩
  unfold headHeightFloor
  split_ifs
  exacts [Or.inl rfl, Or.inr rfl]

end Consensus.Goldilocks.Store

end
