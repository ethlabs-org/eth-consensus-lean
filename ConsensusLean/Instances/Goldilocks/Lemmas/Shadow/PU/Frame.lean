module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Viability
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Cache
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order

public section

/-! # Shadow P-U frame snapshots -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}

/-- The shadow frame keeps the same rooted tree and roots fork choice at F. -/
theorem frameOK_toFrame' (hs : PUSnapshot st acp₀) : FrameOK st.toFrame' := by
  constructor
  all_goals simp only [Frame.Rooted, Frame.Anc, toFrame'_tree, toFrame'_F,
    toFrame'_fcRoot, toFrame'_viableHeads]
  · exact hs.finite.subset fun _ h => h.1
  · exact hs.coherent.mono fun _ h => h.1
  · exact ⟨⟨hs.F_mem, .refl⟩, fun _ h => Anc.restrict .refl h.2⟩
  · exact ⟨hs.F_mem, .refl⟩
  · exact .refl
  · exact fun _ h => ⟨h.1, h.2.1⟩
  · exact fun _ h => Anc.restrict .refl h.2.1

/-- Top frames contain J as a viable head, including the genesis justification. -/
theorem J_mem_viableHeads' (hs : PUSnapshot st acp₀) (htop : st.hmax = st.hj + 1) :
    st.J ∈ st.toFrame'.viableHeads := by
  rw [toFrame'_viableHeads]
  refine ⟨hs.J_mem, hs.F_J, ?_⟩
  rcases hs.J_entry with hg | ⟨hJh, _, _⟩
  · have hheight : (st.σ st.J.root).h = 1 := by rw [hg]; exact hs.genesis_height
    have hj := hs.J_height_le
    apply (st.isViable'_iff _).2
    by_cases hh : st.hmax ≤ (st.σ st.J.root).h
    · exact Or.inl hh
    · exact Or.inr ⟨by omega, Or.inr .refl⟩
  · exact (st.isViable'_iff _).2 (Or.inr ⟨by omega, Or.inr .refl⟩)

/-- Membership in the shadow viable tree is ancestor closure above F. -/
theorem mem_viableTree'_iff {X : NodeBlock P ACP} :
    X ∈ st.toFrame'.viableTree st.toFrame'.tree ↔
      X ∈ st.tree ∧ st.Anc st.F X ∧
        ∃ W ∈ st.tree, st.Anc st.F W ∧ st.IsViable' W ∧ st.Anc X W := by
  simp only [Frame.viableTree, Frame.Anc, Set.mem_ofPred_eq, toFrame'_tree,
    toFrame'_viableHeads, toFrame'_fcRoot]
  constructor
  · rintro ⟨⟨hX, hFX⟩, _, W, _, ⟨hW, hFW, hv⟩, hXW⟩
    exact ⟨hX, hFX, W, hW, hFW, hv, hXW.mono fun _ h => h.1⟩
  · rintro ⟨hX, hFX, W, hW, hFW, hv, hXW⟩
    exact ⟨⟨hX, hFX⟩, Anc.restrict .refl hFX, W, ⟨hW, hFW⟩,
      ⟨hW, hFW, hv⟩, Anc.restrict hFX hXW⟩

/-- Gap frames have exactly the stock viable tree. -/
theorem viableTree'_eq_of_gap (hs : PUSnapshot st acp₀)
    (hgap : st.hj + 1 < st.hmax) :
    st.toFrame'.viableTree st.toFrame'.tree = st.toFrame.viableTree st.toFrame.tree := by
  have htop : ¬ st.hmax = st.hj + 1 := by omega
  have hnc : ¬ st.Contest := fun h => htop h.1
  have hroot : st.fcRoot = st.F := by simp [fcRoot, htop]
  ext X
  rw [mem_viableTree'_iff]
  constructor
  · rintro ⟨hX, hFX, W, hW, hFW, hv, hXW⟩
    have hV := (isViable'_iff_of_not_contest hs hW hFW hnc).1 hv
    refine ⟨⟨hX, hFX⟩, ?_, W, ⟨hW, hFW⟩, ⟨hW, hFW, hV⟩,
      Anc.restrict hFX hXW⟩
    rw [show st.toFrame.fcRoot = st.F from hroot]
    exact Anc.restrict .refl hFX
  · rintro ⟨⟨hX, hFX⟩, _, W, _, ⟨hW, hFW, hrW, hv⟩, hXW⟩
    exact ⟨hX, hFX, W, hW, hFW, isViable_imp_isViable' hs hW hFW hrW hv,
      hXW.mono fun _ h => h.1⟩

/-- In a clean top frame only the F-to-J path is added to the viable tree. -/
theorem viableTree'_eq_union_of_top_clean (hs : PUSnapshot st acp₀)
    (htop : st.hmax = st.hj + 1) (hnc : ¬ st.Contest) :
    st.toFrame'.viableTree st.toFrame'.tree =
      st.toFrame.viableTree st.toFrame.tree ∪ {X | st.Anc st.F X ∧ st.Anc X st.J} := by
  have hroot : st.fcRoot = st.J := by simp [fcRoot, htop, hnc]
  ext X
  rw [mem_viableTree'_iff]
  constructor
  · rintro ⟨hX, hFX, W, hW, hFW, hv, hXW⟩
    obtain ⟨hJW, hv⟩ := (isViable'_iff_of_not_contest hs hW hFW hnc).1 hv
    rw [hroot] at hJW
    rcases Anc.total hs.coherent hXW hJW with hXJ | hJX
    · exact Or.inr ⟨hFX, hXJ⟩
    · left
      refine ⟨⟨hX, hFX⟩, ?_, W, ⟨hW, hFW⟩, ⟨hW, hFW, ?_, hv⟩,
        Anc.restrict hFX hXW⟩
      · rw [show st.toFrame.fcRoot = st.J from hroot]
        exact Anc.restrict hs.F_J hJX
      · rwa [hroot]
  · rintro (⟨⟨hX, hFX⟩, _, W, _, ⟨hW, hFW, hJW, hv⟩, hXW⟩ | ⟨hFX, hXJ⟩)
    · exact ⟨hX, hFX, W, hW, hFW, isViable_imp_isViable' hs hW hFW hJW hv,
        hXW.mono fun _ h => h.1⟩
    · have hX : X ∈ st.tree := by
        by_cases he : X = st.J
        · exact he ▸ hs.J_mem
        · exact (Anc.mem hXJ he).1
      have hJ := J_mem_viableHeads' hs htop
      rw [toFrame'_viableHeads] at hJ
      exact ⟨hX, hFX, st.J, hs.J_mem, hs.F_J, hJ.2.2, hXJ⟩

/-- In contests the new part is precisely the ancestor closure of the added J-side heads
outside the stock viable tree. -/
theorem viableTree'_eq_union_of_contest (hs : PUSnapshot st acp₀) (hc : st.Contest) :
    st.toFrame'.viableTree st.toFrame'.tree = st.toFrame.viableTree st.toFrame.tree ∪
      ({X | X ∈ st.tree ∧ st.Anc st.F X ∧ ∃ W ∈ st.tree,
        st.Anc st.F W ∧ st.Anc st.J W ∧ (st.σ W.root).h + 1 = st.hmax ∧ st.Anc X W} \
        st.toFrame.viableTree st.toFrame.tree) := by
  have hroot : st.fcRoot = st.F := by simp [fcRoot, hc]
  ext X
  rw [mem_viableTree'_iff]
  constructor
  · rintro ⟨hX, hFX, W, hW, hFW, hv, hXW⟩
    by_cases hold : X ∈ st.toFrame.viableTree st.toFrame.tree
    · exact Or.inl hold
    right
    refine ⟨?_, hold⟩
    rcases (st.isViable'_iff W).1 hv with hh | ⟨hh, hgap | hJW⟩
    · apply False.elim
      apply hold
      refine ⟨⟨hX, hFX⟩, ?_, W, ⟨hW, hFW⟩, ⟨hW, hFW, ?_, ?_⟩,
        Anc.restrict hFX hXW⟩
      · rw [show st.toFrame.fcRoot = st.F from hroot]
        exact Anc.restrict .refl hFX
      · rw [hroot]; exact hFW
      · simpa [IsViable, headHeightFloor, hc] using hh
    · have := hc.1
      omega
    · exact ⟨hX, hFX, W, hW, hFW, hJW, hh, hXW⟩
  · rintro (⟨⟨hX, hFX⟩, _, W, _, ⟨hW, hFW, hRW, hv⟩, hXW⟩ |
      ⟨⟨hX, hFX, W, hW, hFW, hJW, hh, hXW⟩, _⟩)
    · exact ⟨hX, hFX, W, hW, hFW, isViable_imp_isViable' hs hW hFW hRW hv,
        hXW.mono fun _ h => h.1⟩
    · exact ⟨hX, hFX, W, hW, hFW,
        (st.isViable'_iff W).2 (Or.inr ⟨hh, Or.inr hJW⟩), hXW⟩

/-- The frame of every shadow-reachable store is well formed. -/
theorem frame_realization' (acp₀ : ACP) (st : Store P ACP)
    (hr : st.Reachable' acp₀) : FrameOK st.toFrame' :=
  frameOK_toFrame' hr.puSnapshot

private theorem frame_ext {n : Nat} {FGP ACP : Type} {a b : Frame n FGP ACP}
    (ht : a.tree = b.tree) (hF : a.F = b.F) (hr : a.fcRoot = b.fcRoot)
    (hv : a.viableHeads = b.viableHeads) : a = b := by
  cases a
  cases b
  cases ht
  cases hF
  cases hr
  cases hv
  rfl

private theorem onBlock'_F {st st' : Store P ACP} {B : NodeBlock P ACP}
    (h : st.onBlock' B = some st') :
    st'.F = st.F ∨ (st'.blocks (st'.σ B.root).F = some st'.F ∧ st'.Anc st.F st'.F) := by
  rw [onBlock'_eq_onBlockWith] at h
  obtain ⟨pr, σ', -, -, -, -, -, rfl⟩ := onBlockWith_eq_some h
  set st₁ : Store P ACP :=
    { st with blocks := Function.update st.blocks B.root (some B),
              σ := Function.update st.σ B.root σ' }
  obtain ⟨atts, he⟩ := addAtts_eq (updateFinality' st₁ σ') B.fgPayload
  obtain ⟨hb, hσ, -, -, -, hF⟩ :=
    (finalitySpec_iff _).1 finalitySpec_updateFinality' st₁ σ'
  have ht : ({ updateFinality' st₁ σ' with atts := atts } : Store P ACP).tree = st₁.tree := by
    simp only [tree, hb]
  have h₁ : st₁.σ B.root = σ' := Function.update_self ..
  rw [he, Store.Anc, ht]
  simp only [hb, hσ, h₁]
  exact hF.imp id fun h => ⟨h.1, h.2.1⟩

private theorem shadow_frameStep_of {n : Nat} {FGP ACP : Type}
    {T T' : Set (Block n FGP ACP)} {B F F' : Block n FGP ACP}
    {v v' : Set (Block n FGP ACP)} (hT' : T' = insert B T)
    (hB : B ∉ T) (hX : ∀ V ∈ T, V.parent ≠ some B.root) (hBB : B.parent ≠ some B.root)
    (hF : F ∈ T) (hFB : Goldilocks.Anc T' F B) (hFF' : Goldilocks.Anc T' F F')
    (hF'B : Goldilocks.Anc T' F' B) :
    FrameStep ⟨{X | X ∈ T ∧ Goldilocks.Anc T F X}, F, F, v⟩ B
      ⟨{X | X ∈ T' ∧ Goldilocks.Anc T' F' X}, F', F', v'⟩ := by
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

/-- Accepting a block is a frame step even when shadow finalization advances F. -/
theorem accept_is_frame_step' (acp₀ : ACP) (st : Store P ACP)
    (hr : st.Reachable' acp₀) :
    (∀ B st', st.onBlock' B = some st' → FrameStep st.toFrame' B st'.toFrame') ∧
      ∀ a, (st.onAttestation a).toFrame' = st.toFrame' := by
  refine ⟨fun B st' h => ?_, fun a => ?_⟩
  · have hu := finalitySpec_updateFinality' (P := P) (ACP := ACP)
    have hw : st.onBlockWith updateFinality' B = some st' := by
      rwa [← onBlock'_eq_onBlockWith]
    obtain ⟨pr, -, hpr, hnew, hpr', hFB, -, -⟩ := onBlockWith_eq_some hw
    have hr' : st'.Reachable' acp₀ := by
      rw [reachable'_eq] at hr ⊢
      exact hr.tail ((step'_iff _ _).2 (Or.inl ⟨B, h⟩))
    have hT' : st'.tree = insert B st.tree := (tree_grows_with hu).1 B st' hw
    have hmove := onBlock'_F h
    have hFF' : st'.Anc st.F st'.F := by
      rcases hmove with he | ⟨_, hFF'⟩
      · rw [he]; exact .refl
      · exact hFF'
    have hF'B : st'.Anc st'.F B := by
      rcases hmove with he | ⟨hb, _⟩
      · rw [he, Store.Anc, hT']; exact hFB
      · obtain ⟨-, ⟨X, hXT, hXr, hXB⟩, -⟩ :=
          entry_state_of_source_with hu hr'.reachableWith B (hT' ▸ Set.mem_insert _ _)
        have hX : st'.blocks X.root = some X := hXT
        rw [hXr, hb] at hX
        obtain rfl := Option.some.inj hX
        exact hXB
    have hparent : ∀ V ∈ st.tree, V.parent ≠ some B.root := by
      intro V hV hp
      have hG := (accepted_tree_with hu hr.reachableWith).2.2.2 V hV
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hG with rfl | ⟨Z, _, hZ⟩
      · cases hp
      · have hZr : st.blocks Z.root = some Z := hZ.1
        rw [Option.some.inj (hZ.2.2.symm.trans hp), hnew] at hZr
        cases hZr
    have hBB : B.parent ≠ some B.root := by
      intro he
      rw [hpr, Option.some.injEq] at he
      rw [he, hnew] at hpr'
      cases hpr'
    have hf := shadow_frameStep_of (v := st.toFrame'.viableHeads)
      (v' := st'.toFrame'.viableHeads) hT' (fun hB => by cases hnew.symm.trans hB)
      hparent hBB hr.puSnapshot.F_mem (hT' ▸ hFB) hFF' hF'B
    convert hf using 1 <;> apply frame_ext <;>
      simp only [toFrame'_tree, toFrame'_F, toFrame'_fcRoot]
  · obtain ⟨atts, he⟩ := st.onAttestation_eq a
    rw [he]
    apply frame_ext <;>
      simp only [toFrame'_tree, toFrame'_F, toFrame'_fcRoot, toFrame'_viableHeads,
        isViable'_iff, Store.Anc, tree]

end Consensus.Goldilocks.Store

end
