module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.OwnBlockReady
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.AcceptedFinality

public section

/-! # Root-free preview acceptance and persistence -/

namespace Consensus.Goldilocks.Store

/-- Strict-height replay ancestry also covers a justification at equal height:
the retained self-entries identify the two checkpoint blocks. -/
theorem replay_finalized_below_justification_of_ancestry
    {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) {B F Y J : NodeBlock P ACP}
    (hB : B ∈ st.tree) (hF : F ∈ st.tree) (hFr : F.root = (st.σ B.root).F)
    (hY : Y ∈ st.tree) (hJ : J ∈ st.tree) (hJr : J.root = (st.σ Y.root).J)
    (hh : (st.σ B.root).hF ≤ (st.σ Y.root).hj)
    (hanc : ∀ W ∈ st.tree, (st.σ B.root).hF < (st.σ W.root).h → st.Anc F W) :
    st.Anc F J := by
  have hc := (accepted_tree P ACP acp₀ st hr).2.1
  rcases Healing.Store.fin_pair_self_entry hr hB with hg | ⟨F', hF', hF'r, hFh, hFT⟩
  · have he : F = P.genesisBlock acp₀ := hc.1 hF (Healing.Store.genesis_mem hr) (hFr.trans hg)
    rw [he]
    exact (accepted_tree P ACP acp₀ st hr).2.2.2 J hJ
  have heF : F' = F := hc.1 hF' hF (hF'r.trans hFr.symm)
  subst F'
  obtain ⟨J', hJ', hJ'r, hJY, hcase⟩ := Healing.Store.J_entry_of_reachable hr hY
  have heJ : J' = J := hc.1 hJ' hJ (hJ'r.trans hJr.symm)
  subst J'
  have hFY := hanc Y hY (hh.trans_lt (Healing.Store.hj_lt_h hr hY))
  have hJh := Healing.Store.J_height_le hr hY hJ hJr
  have hJT : (st.σ J.root).Th = J.root := by
    rcases hcase with rfl | hcase
    · rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Healing.Store.σ_genesis hr]
      rfl
    · exact hcase.2
  by_cases hlt : (st.σ B.root).hF < (st.σ J.root).h
  · exact hanc J hJ hlt
  · have he : F = J := Healing.self_entries_eq hr hF hJ hFY hJY
      (by rw [hFh]; omega) hFT hJT
    rw [he]
    exact .refl

/-- Successful import caches replay finality whenever its strict-height ancestry
comparisons hold in the post-store. This separates the guard calculation from
the source of crossing-set exclusion (fault bounds or chain conviction). -/
theorem onBlock_finality_cached_of_ancestry
    {P : Params} {ACP : Type} {acp₀ : ACP} {pre post : Store P ACP}
    (hr : pre.Reachable acp₀) {B F : NodeBlock P ACP}
    (ha : pre.onBlock B = some post) (hF : F ∈ post.tree)
    (hFr : F.root = (post.σ B.root).F)
    (hanc : ∀ W ∈ post.tree, (post.σ B.root).hF < (post.σ W.root).h → post.Anc F W) :
    post.Anc F post.F := by
  classical
  have hpost : post.Reachable acp₀ := hr.tail (Or.inl ⟨B, ha⟩)
  obtain ⟨pr, σ, _, _, _, _, _, hp⟩ := onBlock_eq_some ha
  let ins : Store P ACP :=
    { pre with blocks := Function.update pre.blocks B.root (some B),
               σ := Function.update pre.σ B.root σ }
  have hp' : post = (ins.updateFinality σ).addAtts B.fgPayload := hp
  obtain ⟨atts, hatts⟩ := addAtts_eq (ins.updateFinality σ) B.fgPayload
  have heq : post = { ins.updateFinality σ with atts := atts } := hp'.trans hatts
  have hb : post.blocks = ins.blocks := by
    rw [heq]; exact (updateFinality_spec ins σ).1
  have hs : post.σ = ins.σ := by
    rw [heq]; exact (updateFinality_spec ins σ).2.1
  have ht : post.tree = ins.tree := by unfold tree; rw [hb]
  have state_eq : ∀ W ∈ pre.tree, post.σ W.root = pre.σ W.root := by
    intro W hW
    have hnew := (onBlock_fields ha).choose_spec.choose_spec.1
    have hne : W.root ≠ B.root := by
      intro he
      change pre.blocks W.root = some W at hW
      rw [he, hnew] at hW
      cases hW
    rw [hs]
    exact Function.update_of_ne hne ..
  have hB : B ∈ post.tree := by
    change post.blocks B.root = some B
    rw [hb]; simp [ins]
  have sub : pre.tree ⊆ post.tree := (tree_grows P ACP acp₀ pre hr).1 B post ha ▸
    Set.subset_insert _ _
  obtain ⟨_, _, _, _, _, hOld, _, _⟩ := onBlock_eq_some ha
  obtain ⟨_, ⟨F', hF', hF'r, hF'B⟩, _⟩ := entry_state_of_source P ACP acp₀ post hpost B hB
  have heF : F' = F := (accepted_tree P ACP acp₀ post hpost).2.1.1 hF' hF
    (hF'r.trans hFr.symm)
  subst F'
  rcases Goldilocks.Anc.total (accepted_tree P ACP acp₀ post hpost).2.1
      ((tree_grows P ACP acp₀ pre hr).1 B post ha ▸ hOld) hF'B with hOldF | hFOld
  · by_cases he : pre.F = F
    · rw [← he]
      exact (finalized_monotone P ACP acp₀ pre hr).1 B post ha
    have hXF : ins.blocks (ins.σ B.root).F = some F := by
      rw [← hs, ← hb, ← hFr]; exact hF
    have hlimits := entry_input hpost B.root
    have hfin : (post.σ B.root).hF ≤ (post.σ B.root).hj := by
      obtain ⟨c, _, _, _, hc⟩ := chain_state_of_chain P ACP acp₀ post hpost B hB
      exact (FG.chain_invariants P.fg _ _ hc).2.1
    obtain ⟨J, hJ, hJr, _⟩ := (entry_state_of_source P ACP acp₀ post hpost B hB).2.2
    have hFJ := replay_finalized_below_justification_of_ancestry hpost
      hB hF hFr hB hJ hJr hfin hanc
    have hafter : (afterJustification P ACP ins (ins.σ B.root)).Anc F
        (afterJustification P ACP ins (ins.σ B.root)).J := by
      have hlookup : ins.blocks (ins.σ B.root).J = some J := by
        rw [← hs, ← hb, ← hJr]; exact hJ
      have holdJ : ins.Anc ins.F J := by
        change Goldilocks.Anc ins.tree pre.F J
        rw [← ht]; exact hOldF.trans hFJ
      unfold afterJustification
      simp only [hlookup]
      split_ifs with htake
      · change Goldilocks.Anc ins.tree F J
        rw [← ht]; exact hFJ
      · have hn : ¬ LexLt (pre.hj, pre.J.root) ((post.σ B.root).hj,
            (post.σ B.root).J) := by
          intro hn
          exact htake ⟨holdJ, by simpa only [hs] using hn⟩
        have hh : (post.σ B.root).hj ≤ pre.hj := by
          by_contra h
          exact hn (Or.inl (by omega))
        obtain ⟨_, hJpre, _, ⟨Y, hY, hYJ, hYh⟩, _⟩ :=
          cache_invariants P ACP acp₀ pre hr
        have hYs := state_eq Y hY
        have hxj := replay_finalized_below_justification_of_ancestry hpost hB hF hFr
          (sub hY) (sub hJpre) (by rw [hYs]; exact hYJ.symm)
          (by rw [hYs]; exact hfin.trans (hh.trans hYh.symm.le)) hanc
        change Goldilocks.Anc ins.tree F pre.J
        rw [← ht]; exact hxj
    have hv : HasViableDescendant
        ({ ins with hmax := max ins.hmax (ins.σ B.root).h } : Store P ACP) F := by
      obtain ⟨_, _, _, _, _, ⟨M, hM, hMh⟩, _⟩ := cache_invariants P ACP acp₀ pre hr
      have hMs := state_eq M hM
      have hmax : ∃ W ∈ post.tree, (post.σ W.root).h = max pre.hmax (post.σ B.root).h := by
        by_cases h : pre.hmax ≤ (post.σ B.root).h
        · exact ⟨B, hB, (max_eq_right h).symm⟩
        · exact ⟨M, sub hM, by rw [hMs, hMh, max_eq_left (le_of_not_ge h)]⟩
      obtain ⟨W, hW, hWh⟩ := hmax
      have hFW := hanc W hW
        ((hfin.trans_lt hlimits.2.1).trans_le (hWh ▸ le_max_right _ _))
      refine ⟨W, ?_, ?_, ?_⟩
      · change W ∈ ins.tree; rw [← ht]; exact hW
      · change Goldilocks.Anc ins.tree F W; rw [← ht]; exact hFW
      · change _ ≤ (ins.σ W.root).h
        rw [← hs]
        have hm : ins.hmax = pre.hmax := rfl
        unfold headHeightFloor
        split_ifs <;> change _ ≤ (post.σ W.root).h <;> simp only [hm] <;>
          (clear * - hWh; omega)
    have hc := cache_acceptance P ACP ins B F (ht ▸ hB)
      (by rw [← hs]; exact hlimits.2.1) hXF
      (by change Goldilocks.Anc ins.tree F B; rw [← ht]; exact hF'B)
      (by change Goldilocks.Anc ins.tree pre.F F; rw [← ht]; exact hOldF) he hafter hv
    rw [show ins.σ B.root = σ by simp [ins]] at hc
    have hpostF : post.F = (ins.updateFinality σ).F := by rw [heq]
    have htree : (ins.updateFinality σ).tree = post.tree := by
      unfold tree
      rw [(updateFinality_spec ins σ).1, ← hb]
    change Goldilocks.Anc (ins.updateFinality σ).tree F (ins.updateFinality σ).F at hc
    rwa [htree, ← hpostF] at hc
  · exact hFOld.trans ((finalized_monotone P ACP acp₀ pre hr).1 B post ha)

/-- Under the FG fault bound, an honest reader caches the root-free preview
on acceptance. It either already covered it or passes the advancing guard. -/
theorem accepted_preview_cached {P : Params} {ACP : Type} {acp₀ : ACP}
    {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}
    (hr : FGLocalRun acp₀ H U tr) (hf : Hᶜ.ncard < 2 * P.fg.q - P.n)
    {y : Fin P.n} (hy : y ∈ H) {k : Nat} {B : NodeBlock P ACP} {pr : Nat}
    (ha : tr.AcceptAt y k B) (hp : B.parent = some pr) :
    ∃ F ∈ (tr.store y (k + 1)).tree,
      F.root = P.fg.finalityPreview ((tr.store y k).σ pr) B.slot B.fgPayload ∧
      (tr.store y (k + 1)).Anc F (tr.store y (k + 1)).F := by
  have hb := accept_onBlock hr hy ha
  obtain ⟨F, hF, hfroot, _⟩ := onBlock_preview_resolves (store_reachable hr hy k) hb hp
  obtain ⟨pr', σ', _, _, hp', hσ, _, hs, _⟩ := onBlock_fields hb
  obtain rfl : pr' = pr := Option.some.inj (hp'.symm.trans hp)
  have hstate : (tr.store y (k + 1)).σ B.root = σ' := by
    rw [hs]; exact Function.update_self ..
  refine ⟨F, hF, hfroot, Healing.accepted_finality_cached hr hf hy ha hF ?_⟩
  rw [hstate, hfroot]
  exact (P.fg.stateTransition_finalityPreview hσ).symm

/-- Honest FG execution keeps a covered preview below its cache at every later
cut. This applies after `accepted_preview_cached` without further health. -/
theorem cached_preview_at_later_cut {P : Params} {ACP : Type} {acp₀ : ACP}
    {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}
    (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {k j : Nat}
    (hkj : k ≤ j) {F : NodeBlock P ACP}
    (hF : (tr.store y k).Anc F (tr.store y k).F) :
    (tr.store y j).Anc F (tr.store y j).F := by
  induction j, hkj using Nat.le_induction with
  | base => exact hF
  | succ j _ ih =>
    rcases store_step hr hy j with he | ⟨B, _, hb⟩ | ⟨a, _, he⟩
    · rwa [he]
    · exact preview_covered_persists (store_reachable hr hy j)
        (.single (Or.inl ⟨B, hb⟩)) ih
    · rw [he]
      exact preview_covered_persists (store_reachable hr hy j)
        (.single (Or.inr ⟨a, rfl⟩)) ih

/-- At any honest reader cut holding a non-genesis block, its parent-state
preview is already below the reader's cache under the FG fault bound. -/
theorem held_preview_cached {P : Params} {ACP : Type} {acp₀ : ACP}
    {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}
    (hr : FGLocalRun acp₀ H U tr) (hf : Hᶜ.ncard < 2 * P.fg.q - P.n)
    {y : Fin P.n} (hy : y ∈ H) {j : Nat} {B : NodeBlock P ACP} {pr : Nat}
    (hB : B ∈ (tr.store y j).tree) (hp : B.parent = some pr) :
    ∃ F ∈ (tr.store y j).tree,
      F.root = P.fg.finalityPreview ((tr.store y j).σ pr) B.slot B.fgPayload ∧
      (tr.store y j).Anc F (tr.store y j).F := by
  rcases tree_accepted hr hy hB with he | ⟨k, hkj, ha⟩
  · rw [he] at hp; cases hp
  obtain ⟨_, ⟨F, hF, hfroot, _⟩, _⟩ := entry_state_of_source P ACP acp₀ _
    (store_reachable hr hy (k + 1)) B (by
      rw [(tree_grows P ACP acp₀ _ (store_reachable hr hy k)).1 _ _
        (accept_onBlock hr hy ha)]
      exact Set.mem_insert _ _)
  have hcached := Healing.accepted_finality_cached hr hf hy ha hF hfroot
  have hFm := held_mono hr hy hkj hF
  have hBm : (tr.store y (k + 1)).blocks B.root = some B := by
    change B ∈ (tr.store y (k + 1)).tree
    rw [(tree_grows P ACP acp₀ _ (store_reachable hr hy k)).1 _ _
      (accept_onBlock hr hy ha)]
    exact Set.mem_insert _ _
  have hstate := (held_mono hr hy hkj hBm).2
  refine ⟨F, hFm.1, ?_, cached_preview_at_later_cut hr hy hkj hcached⟩
  rw [← hstate] at hfroot
  exact hfroot.trans (P.fg.stateTransition_finalityPreview (step_σ hr hy hB hp))

/-- Every target of the reader's post-acceptance frame extends the preview,
not just its viable heads. The quorum bound rules out a retained stale cache. -/
theorem held_preview_ancestor_frame {P : Params} {ACP : Type} {acp₀ : ACP}
    {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}
    (hr : FGLocalRun acp₀ H U tr) (hf : Hᶜ.ncard < 2 * P.fg.q - P.n)
    {y : Fin P.n} (hy : y ∈ H) {j : Nat} {B : NodeBlock P ACP} {pr : Nat}
    (hB : B ∈ (tr.store y j).tree) (hp : B.parent = some pr) :
    ∃ F ∈ (tr.store y j).tree,
      F.root = P.fg.finalityPreview ((tr.store y j).σ pr) B.slot B.fgPayload ∧
      ∀ X ∈ (tr.store y j).toFrame.tree, (tr.store y j).Anc F X := by
  obtain ⟨F, hF, hfroot, hcached⟩ := held_preview_cached hr hf hy hB hp
  exact ⟨F, hF, hfroot, fun X hX => hcached.trans hX.2⟩

end Consensus.Goldilocks.Store

end
