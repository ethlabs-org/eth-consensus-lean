module
public import ConsensusLean.Instances.Goldilocks.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.CoreStock
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Handlers
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Handlers
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Model
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.Handlers
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.View
public import ConsensusLean.Instances.Goldilocks.Spec.Node.Handlers
public import ConsensusLean.Instances.Goldilocks.Spec.Node.State
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Parametric
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Node
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Viability
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo

public section

/-! # Shadow P-U: the store invariants at the shadow finality update (lane C0)

The invariants generic in the finality update (`FinalitySpec`, `ReachableWith`, the `*_with`
lemmas) are in `Lemmas/FGStore/Parametric`, re-exported here. This file adds the shadow store's
instance: `updateFinality'` has the stock shape (`finalitySpec_updateFinality'`), so `Reachable'` is
`ReachableWith updateFinality'` (`Reachable'.reachableWith`), with the P-U snapshot bundle and the
justification-cache maximality (`Healing.JMax`) over it. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type}

/-! ## The shadow store

The shadow `onBlock'` is the stock body with `updateFinality'`; its finality update has the
stock shape (the guard is the only change), so `Reachable'` is `ReachableWith updateFinality'`
and every lemma above applies to it. -/

open Classical in
/-- The justification step of `update_finality`. -/
noncomputable def jUpd (st₁ : Store P ACP) (σ : FG.ChainState P.n) : Store P ACP :=
  match st₁.blocks σ.J with
  | some X =>
      if st₁.Anc st₁.F X ∧ LexLt (st₁.hj, st₁.J.root) (σ.hj, σ.J) then
        { st₁ with J := X, hj := σ.hj }
      else st₁
  | none => st₁

open Classical in
/-- The finalized-tip step of `update_finality`, with the guard `g`. -/
noncomputable def fUpd (g : Store P ACP → NodeBlock P ACP → Prop) (st₂ : Store P ACP)
    (σ : FG.ChainState P.n) : Store P ACP :=
  match st₂.blocks σ.F with
  | some X =>
      if st₂.Anc st₂.F X ∧ st₂.F ≠ X ∧ st₂.Anc X st₂.J ∧ g st₂ X then
        { st₂ with F := X }
      else st₂
  | none => st₂

/-- `update_finality` with the finalized-tip guard `g` (the stock body, `HasViableDescendant`
replaced by `g`). -/
noncomputable def updateFinalityG (g : Store P ACP → NodeBlock P ACP → Prop)
    (st : Store P ACP) (σ : FG.ChainState P.n) : Store P ACP :=
  fUpd g (jUpd { st with hmax := max st.hmax σ.h } σ) σ

private theorem jUpd_spec (st₁ : Store P ACP) (σ : FG.ChainState P.n) :
    (jUpd st₁ σ).blocks = st₁.blocks ∧ (jUpd st₁ σ).σ = st₁.σ ∧ (jUpd st₁ σ).atts = st₁.atts ∧
      (jUpd st₁ σ).hmax = st₁.hmax ∧ (jUpd st₁ σ).F = st₁.F ∧
      (((jUpd st₁ σ).J = st₁.J ∧ (jUpd st₁ σ).hj = st₁.hj) ∨
        (st₁.blocks σ.J = some (jUpd st₁ σ).J ∧ (jUpd st₁ σ).hj = σ.hj ∧
          st₁.Anc st₁.F (jUpd st₁ σ).J ∧ LexLt (st₁.hj, st₁.J.root) (σ.hj, σ.J))) := by
  unfold jUpd
  split
  · rename_i X hJ
    split_ifs with hJc
    · exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inr ⟨hJ, rfl, hJc.1, hJc.2⟩⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

private theorem fUpd_spec (g : Store P ACP → NodeBlock P ACP → Prop) (st₂ : Store P ACP)
    (σ : FG.ChainState P.n) :
    (fUpd g st₂ σ).blocks = st₂.blocks ∧ (fUpd g st₂ σ).σ = st₂.σ ∧
      (fUpd g st₂ σ).atts = st₂.atts ∧ (fUpd g st₂ σ).hmax = st₂.hmax ∧
      (fUpd g st₂ σ).J = st₂.J ∧ (fUpd g st₂ σ).hj = st₂.hj ∧
      ((fUpd g st₂ σ).F = st₂.F ∨
        (st₂.blocks σ.F = some (fUpd g st₂ σ).F ∧ st₂.Anc st₂.F (fUpd g st₂ σ).F ∧
          st₂.F ≠ (fUpd g st₂ σ).F ∧ st₂.Anc (fUpd g st₂ σ).F (fUpd g st₂ σ).J)) := by
  unfold fUpd
  split
  · rename_i X hF
    split_ifs with hFc
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, Or.inr ⟨hF, hFc.1, hFc.2.1, hFc.2.2.1⟩⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩

/-- Every guard gives the stock shape (`updateFinality_spec`, whose proof never reads the
guard). -/
theorem finalitySpec_updateFinalityG (g : Store P ACP → NodeBlock P ACP → Prop) :
    FinalitySpec (updateFinalityG g) := by
  rw [finalitySpec_iff]
  intro st σ
  unfold updateFinalityG
  obtain ⟨jb, jσ, ja, jm, jF, jJ⟩ := jUpd_spec { st with hmax := max st.hmax σ.h } σ
  obtain ⟨fb, fσ, fa, fm, fJ, fhj, fF⟩ := fUpd_spec g (jUpd { st with hmax := max st.hmax σ.h } σ) σ
  have hanc : ∀ {s s' : Store P ACP}, s.blocks = s'.blocks → ∀ X Y, s.Anc X Y ↔ s'.Anc X Y := by
    intro s s' h X Y
    unfold Store.Anc Store.tree
    rw [h]
  refine ⟨fb.trans jb, fσ.trans jσ, fa.trans ja, fm.trans jm, ?_, ?_⟩
  · rw [fJ, fhj]
    rcases jJ with h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h3, h4⟩
  · rcases fF with h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl (h.trans jF)
    · refine Or.inr ⟨by rw [jb] at h1; exact h1, ?_, by rw [jF] at h3; exact h3, ?_⟩
      · have := (hanc jb _ _).1 h2
        rwa [jF] at this
      · rw [fJ] at h4 ⊢
        exact (hanc jb _ _).1 h4

theorem updateFinality_eq_G :
    updateFinality (P := P) (ACP := ACP) =
      updateFinalityG (fun st X => st.HasViableDescendant X) := by
  funext st σ
  rw [updateFinality_eq]
  rfl

/-- **The shadow cache invariant**: every shadow-reachable store satisfies `CacheGood`; the
`_with` lemmas apply with `finalitySpec_updateFinality'` and `Reachable'.reachableWith`. -/
theorem Reachable.good {acp₀ : ACP} {st : Store P ACP} (h : st.Reachable acp₀) :
    CacheGood acp₀ st :=
  h.reachableWith.good finalitySpec_updateFinality

/-- `cache_invariants` over the shadow `Reachable'`. -/
theorem cache_invariants' {acp₀ : ACP} {st : Store P ACP} (h : st.Reachable acp₀) :
    st.F ∈ st.tree ∧ st.J ∈ st.tree ∧ st.Anc st.F st.J ∧
      (∃ B ∈ st.tree, (st.σ B.root).J = st.J.root ∧ (st.σ B.root).hj = st.hj) ∧
      (∀ B ∈ st.tree, (st.σ B.root).h ≤ st.hmax) ∧
      (∃ B ∈ st.tree, (st.σ B.root).h = st.hmax) ∧
      ∃ B ∈ st.tree, (st.σ B.root).F = st.F.root :=
  cache_invariants_with finalitySpec_updateFinality h.reachableWith

/-- Every store reached with a finality update of the stock shape is a `PUSnapshot`. -/
theorem ReachableWith.puSnapshot {u : Store P ACP → FG.ChainState P.n → Store P ACP}
    {acp₀ : ACP} {st : Store P ACP} (hu : FinalitySpec u) (hr : ReachableWith u acp₀ st) :
    st.PUSnapshot acp₀ := by
  obtain ⟨hfin, hcoh, -, hg⟩ := accepted_tree_with hu hr
  obtain ⟨hF, hJ, hFJ, -, hle, hmax, -⟩ := cache_invariants_with hu hr
  obtain ⟨hcase, W, hW, hJW, hjW⟩ := store_J_entry_with hu hr
  refine ⟨hfin, hcoh, hF, hJ, hFJ, hjW.trans_le (hle W hW), hle, hmax,
    fun h => h_le_of_store_anc_with hu hr h,
    fun hC _ h1 h2 => entry_at_height_with hu hr hC h1 h2,
    store_J_height_le_with hu hr, ?_, hg, ?_⟩
  · rcases hcase with ⟨he, -⟩ | ⟨h1, h2⟩
    · exact Or.inl he
    · exact Or.inr ⟨h1, h2, W, hW, hJW, hjW⟩
  · rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis_with hu hr]
    rfl

/-- Every shadow-reachable store is a `PUSnapshot`. -/
theorem Reachable.puSnapshot {acp₀ : ACP} {st : Store P ACP} (h : st.Reachable acp₀) :
    st.PUSnapshot acp₀ :=
  h.reachableWith.puSnapshot finalitySpec_updateFinality


/-! ## The justification cache is maximal (`Healing.JMax`) over `ReachableWith` (lane W)

`JMax` reads the justification step of `update_finality`, which `FinalitySpec` does not pin
down; `HjMaxSpec u` states it, and every `updateFinalityG g` (so the shadow `updateFinality'`)
has it: the guard only touches the finalized-tip step. -/

/-- The justification step does not lower `Σ.h_j`, and raises it to the justified height of a
state whose justification is a held block extending `Σ.F`. -/
def HjMaxSpec (u : Store P ACP → FG.ChainState P.n → Store P ACP) : Prop :=
  ∀ st σ, st.hj ≤ (u st σ).hj ∧
    ∀ X ∈ st.tree, X.root = σ.J → st.Anc st.F X → σ.hj ≤ (u st σ).hj

theorem hjMaxSpec_iff (u : Store P ACP → FG.ChainState P.n → Store P ACP) :
    HjMaxSpec u ↔ ∀ st σ, st.hj ≤ (u st σ).hj ∧
      ∀ X ∈ st.tree, X.root = σ.J → st.Anc st.F X → σ.hj ≤ (u st σ).hj := Iff.rfl

private theorem hj_jUpd (st₁ : Store P ACP) (σ : FG.ChainState P.n) :
    st₁.hj ≤ (jUpd st₁ σ).hj ∧
      ∀ X ∈ st₁.tree, X.root = σ.J → st₁.Anc st₁.F X → σ.hj ≤ (jUpd st₁ σ).hj := by
  unfold jUpd
  split
  · rename_i X₀ hJ
    have hXe : ∀ X ∈ st₁.tree, X.root = σ.J → X = X₀ := fun X hX hXr => by
      change st₁.blocks X.root = some X at hX
      rw [hXr, hJ] at hX
      exact (Option.some.inj hX).symm
    split_ifs with hJc
    · have hle : st₁.hj ≤ σ.hj := by
        rcases hJc.2 with h | h
        · exact h.le
        · exact h.1.le
      exact ⟨hle, fun _ _ _ _ => le_rfl⟩
    · refine ⟨le_rfl, fun X hX hXr ha => ?_⟩
      obtain rfl := hXe X hX hXr
      by_contra hlt
      exact hJc ⟨ha, Or.inl (not_le.1 hlt)⟩
  · rename_i hJ
    refine ⟨le_rfl, fun X hX hXr _ => ?_⟩
    change st₁.blocks X.root = some X at hX
    rw [hXr] at hX
    exact absurd (hX.symm.trans hJ) (by simp)

theorem hjMaxSpec_updateFinalityG (g : Store P ACP → NodeBlock P ACP → Prop) :
    HjMaxSpec (updateFinalityG g) := by
  intro st σ
  obtain ⟨-, -, -, -, -, hhj, -⟩ :=
    fUpd_spec g (jUpd { st with hmax := max st.hmax σ.h } σ) σ
  obtain ⟨h1, h2⟩ := hj_jUpd { st with hmax := max st.hmax σ.h } σ
  unfold updateFinalityG
  rw [hhj]
  exact ⟨h1, fun X hX hXr ha => h2 X hX hXr ha⟩

theorem hjMaxSpec_updateFinality : HjMaxSpec (P := P) (ACP := ACP) updateFinality :=
  updateFinality_eq_G ▸ hjMaxSpec_updateFinalityG _

section JMaxWith

variable {u : Store P ACP → FG.ChainState P.n → Store P ACP} {acp₀ : ACP}

/-- `Healing.JMax`, restated here so that its body is visible to the copied proofs. -/
def JMaxW (st : Store P ACP) : Prop :=
  ∀ B ∈ st.tree, ∀ X ∈ st.tree, X.root = (st.σ B.root).J → st.Anc st.F X →
    (st.σ B.root).hj ≤ st.hj

/-- Ancestry in a tree with a new block, ending in an old block, is ancestry in the old tree
(the old tree is closed under parents). -/
private theorem anc_of_anc_insert {st : Store P ACP} (hu : FinalitySpec u)
    (hr : ReachableWith u acp₀ st)
    {B : NodeBlock P ACP} (hn : st.blocks B.root = none) {A X : NodeBlock P ACP}
    (h : Goldilocks.Anc (insert B st.tree) A X) (hX : X ∈ st.tree) : st.Anc A X := by
  induction h with
  | refl => exact .refl
  | tail _ hYX ih =>
    obtain ⟨Z, hZ, hZr, -⟩ := step_σ_with hu hr hX hYX.2.2
    rcases hYX.1 with rfl | hY
    · change st.blocks Z.root = some Z at hZ
      rw [hZr, hn] at hZ
      cases hZ
    · exact (ih hY).tail ⟨hY, hX, hYX.2.2⟩

private theorem jMax_init : JMaxW (Store.init (P := P) acp₀) := by
  intro B _ _ _ _ _
  change (FG.ChainState.init P.fg).hj ≤ 0
  rfl

private theorem jMax_congr {st st' : Store P ACP} (hb : st'.blocks = st.blocks)
    (hσ : st'.σ = st.σ) (hF : st'.F = st.F) (hj : st'.hj = st.hj) (h : JMaxW st) :
    JMaxW st' := by
  have ht : st'.tree = st.tree := by
    ext Y
    change st'.blocks Y.root = some Y ↔ st.blocks Y.root = some Y
    rw [hb]
  intro B hB X hX hXr hFX
  simp only [Store.Anc, ht] at hB hX hFX
  rw [hσ] at hXr ⊢
  rw [hj]
  exact h B hB X hX hXr (hF ▸ hFX)

private theorem jMax_updateFinality {st : Store P ACP} (hu : FinalitySpec u) (hhjU : HjMaxSpec u)
    (hr : ReachableWith u acp₀ st) (hJ : JMaxW st)
    {B : NodeBlock P ACP} {σ' : FG.ChainState P.n} (hn : st.blocks B.root = none)
    (st₁ : Store P ACP) (hb₁ : st₁.blocks = Function.update st.blocks B.root (some B))
    (hσ₁ : st₁.σ = Function.update st.σ B.root σ') (hFe : st₁.F = st.F) (hj₁ : st₁.hj = st.hj) :
    JMaxW (u st₁ σ') := by
  obtain ⟨hb, hσ, -, -, -, hF⟩ := (finalitySpec_iff u).1 hu st₁ σ'
  obtain ⟨hhj, hhjσ⟩ := hhjU st₁ σ'
  have hmem : ∀ Y, Y ∈ st₁.tree ↔ Y = B ∨ Y ∈ st.tree := by
    intro Y
    change st₁.blocks Y.root = some Y ↔ Y = B ∨ st.blocks Y.root = some Y
    rw [hb₁, Function.update_apply]
    split_ifs with hY
    · refine ⟨fun e => Or.inl (Option.some.inj e).symm, ?_⟩
      rintro (rfl | e)
      · rfl
      · rw [hY, hn] at e
        cases e
    · refine ⟨Or.inr, ?_⟩
      rintro (rfl | e)
      · exact absurd rfl hY
      · exact e
  have htree : st₁.tree = insert B st.tree := Set.ext fun Y => hmem Y
  have ht : (u st₁ σ').tree = st₁.tree := by
    ext Y
    change (u st₁ σ').blocks Y.root = some Y ↔ st₁.blocks Y.root = some Y
    rw [hb]
  intro B₀ hB₀ X hX hXr hFX
  simp only [Store.Anc, ht] at hB₀ hX hFX
  rw [hσ] at hXr ⊢
  have hF₁ : st₁.Anc st.F X := by
    rcases hF with h | ⟨-, h, -, -⟩
    · rwa [h, hFe] at hFX
    · exact (hFe ▸ h).trans hFX
  rcases (hmem B₀).1 hB₀ with rfl | hB₀s
  · have : st₁.σ B₀.root = σ' := by rw [hσ₁]; exact Function.update_self _ _ _
    rw [this] at hXr ⊢
    exact hhjσ X hX hXr (hFe ▸ hF₁)
  · have hne : B₀.root ≠ B.root := fun e => by
      change st.blocks B₀.root = some B₀ at hB₀s
      rw [e, hn] at hB₀s
      cases hB₀s
    have hσ₀ : st₁.σ B₀.root = st.σ B₀.root := by rw [hσ₁]; exact Function.update_of_ne hne _ _
    rw [hσ₀] at hXr ⊢
    obtain ⟨-, -, ⟨X', hX', hX'r, -⟩⟩ :=
      entry_state_of_source_with hu hr B₀ hB₀s
    have hXs : X ∈ st.tree := by
      rcases (hmem X).1 hX with rfl | h
      · change st.blocks X'.root = some X' at hX'
        rw [hX'r, ← hXr, hn] at hX'
        cases hX'
      · exact h
    have hF₀ : st.Anc st.F X := anc_of_anc_insert hu hr hn (htree ▸ hF₁) hXs
    exact (hJ B₀ hB₀s X hXs hXr hF₀).trans (hj₁ ▸ hhj)

private theorem jMax_step {st st' : Store P ACP} (hu : FinalitySpec u) (hhjU : HjMaxSpec u)
    (hr : ReachableWith u acp₀ st) (hJ : JMaxW st)
    (hs : StepWith u st st') : JMaxW st' := by
  rcases (stepWith_iff _ _ _).1 hs with ⟨B, hB⟩ | ⟨a, rfl⟩
  · obtain ⟨pr, σ', -, hn, -, -, -, rfl⟩ := onBlockWith_eq_some hB
    obtain ⟨atts, he⟩ := addAtts_eq (u
      { st with blocks := Function.update st.blocks B.root (some B),
                σ := Function.update st.σ B.root σ' } σ') B.fgPayload
    rw [he]
    exact jMax_congr rfl rfl rfl rfl (jMax_updateFinality hu hhjU hr hJ hn _ rfl rfl rfl rfl)
  · obtain ⟨atts, he⟩ := Store.onAttestation_eq st a
    rw [he]
    exact jMax_congr rfl rfl rfl rfl hJ

/-- **`JMax` at every store reached with an update of the stock shapes** (`jMax_of_reachable`). -/
theorem jMax_of_reachable_with {st : Store P ACP} (hu : FinalitySpec u) (hhjU : HjMaxSpec u)
    (hr : ReachableWith u acp₀ st) : JMaxW st := by
  rw [reachableWith_eq] at hr
  induction hr with
  | refl => exact jMax_init
  | tail hr hs ih => exact jMax_step hu hhjU (by rw [reachableWith_eq]; exact hr) ih hs

/-- `Healing.JMax` at every shadow-reachable store. -/
theorem Reachable.jMax {acp₀ : ACP} {st : Store P ACP} (h : st.Reachable acp₀) :
    Healing.JMax st :=
  (Healing.jMax_iff st).2
    (jMax_of_reachable_with finalitySpec_updateFinality hjMaxSpec_updateFinality h.reachableWith)

end JMaxWith

end Consensus.Goldilocks.Store

end
