module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Node
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.HeldChains
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Entry
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.CutSteps

public section

/-! # Shadow P-U: the store invariants under any finality update (lane C0)

The shadow store (`Shadow/PU/Node`, `Store.onBlock'`) has the stock `fg_on_block` with only the
finality guard of `update_finality` changed. The stock reachable-state invariant
(`Lemmas/FGStore/Invariant`, `Good`, private there) reads `update_finality` only through
`updateFinality_spec`, which does not mention the guard. So the invariant is copied once here,
generic in the finality update `u` (`onBlockWith`, `StepWith`, `ReachableWith`), and holds
whenever `u` has the shape of `updateFinality_spec` (`FinalitySpec`). The shadow
`Reachable'` is its instance at `updateFinality'`.

Exported over `ReachableWith u` (given `FinalitySpec u`), with the stock statements:
`chain_state_of_chain_with`, `accepted_tree_with`, `tree_grows_with`, `cache_invariants_with`,
`entry_state_of_source_with`, and the store lemmas the frame and viability proofs read:
`genesis_mem_with`, `σ_genesis_with`, `step_σ_with`, `h_le_of_store_anc_with`,
`Th_eq_of_anc_with`, `hj_lt_h_with`, `J_entry_with` (stock form; `J_entry_hj_with` adds
`h_j = 0` on the genesis arm), `J_height_le_with`, `store_J_height_le_with`,
`entry_at_height_with` and `store_J_entry_with` (the store's `Σ.J`: genesis with `Σ.h_j = 0`,
or an entry at `Σ.h_j` below a held block of greater height). -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type}

/-- A finality update with the shape of `updateFinality_spec`: it writes only `h_max`, the
justification cache and the finalized tip, and each under the stock conditions, the
finalized-tip guard excepted. -/
def FinalitySpec (u : Store P ACP → FG.ChainState P.n → Store P ACP) : Prop :=
  ∀ st σ, (u st σ).blocks = st.blocks ∧ (u st σ).σ = st.σ ∧
    (u st σ).atts = st.atts ∧ (u st σ).hmax = max st.hmax σ.h ∧
    (((u st σ).J = st.J ∧ (u st σ).hj = st.hj) ∨
      (st.blocks σ.J = some (u st σ).J ∧ (u st σ).hj = σ.hj ∧
        st.Anc st.F (u st σ).J ∧ LexLt (st.hj, st.J.root) (σ.hj, σ.J))) ∧
    ((u st σ).F = st.F ∨
      (st.blocks σ.F = some (u st σ).F ∧ st.Anc st.F (u st σ).F ∧
        st.F ≠ (u st σ).F ∧ st.Anc (u st σ).F (u st σ).J))

theorem finalitySpec_updateFinality : FinalitySpec (P := P) (ACP := ACP) updateFinality :=
  updateFinality_spec

open Classical in
/-- `fg_on_block` with the finality update `u` (the stock body, `updateFinality` replaced). -/
noncomputable def onBlockWith (u : Store P ACP → FG.ChainState P.n → Store P ACP)
    (st : Store P ACP) (B : NodeBlock P ACP) : Option (Store P ACP) :=
  match B.parent with
  | none => none
  | some pr =>
      if (st.blocks B.root).isSome ∨ (st.blocks pr).isNone ∨
          ¬ Goldilocks.Anc (insert B st.tree) st.F B then
        none
      else
        match P.fg.stateTransition (st.σ pr) B.fgView with
        | none => none
        | some σ' =>
            let st₁ : Store P ACP :=
              { st with blocks := Function.update st.blocks B.root (some B),
                        σ := Function.update st.σ B.root σ' }
            some ((u st₁ σ').addAtts B.fgPayload)

/-- One FG store step with the finality update `u`. -/
def StepWith (u : Store P ACP → FG.ChainState P.n → Store P ACP) (st st' : Store P ACP) :
    Prop :=
  (∃ B, st.onBlockWith u B = some st') ∨ ∃ a, st' = onAttestation st a

/-- The FG states reached with the finality update `u`. -/
def ReachableWith (u : Store P ACP → FG.ChainState P.n → Store P ACP) (acp₀ : ACP) :
    Store P ACP → Prop :=
  Relation.ReflTransGen (StepWith u) (init acp₀)

theorem onBlockWith_eq_some {u : Store P ACP → FG.ChainState P.n → Store P ACP}
    {st st' : Store P ACP} {B : NodeBlock P ACP} (h : st.onBlockWith u B = some st') :
    ∃ pr, ∃ σ' : FG.ChainState P.n, B.parent = some pr ∧ st.blocks B.root = none ∧
      (st.blocks pr).isSome ∧
      Goldilocks.Anc (insert B st.tree) st.F B ∧
      P.fg.stateTransition (st.σ pr) B.fgView = some σ' ∧
      st' = (u { st with blocks := Function.update st.blocks B.root (some B),
                         σ := Function.update st.σ B.root σ' } σ').addAtts B.fgPayload := by
  unfold onBlockWith at h
  split at h
  · cases h
  rename_i pr hpr
  split_ifs at h with hc
  split at h
  · cases h
  rename_i σ' hσ'
  simp only [not_or, not_not, Bool.not_eq_true, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none] at hc
  exact ⟨pr, σ', hpr, hc.1, Option.isSome_iff_ne_none.2 hc.2.1, hc.2.2, hσ',
    (Option.some.inj h).symm⟩

/-! ## Chains linked from genesis -/

/-- A chain extended by one block is linked when the chain is and the block names the chain's
last root (genesis for the empty chain) as its parent. -/
private theorem linked_append {c : List (NodeBlock P ACP)} {B : NodeBlock P ACP} :
    LinkedFromGenesis P ACP (c ++ [B]) ↔
      LinkedFromGenesis P ACP c ∧ B.parent = (P.genesisRoot :: c.map Block.root).getLast? := by
  have key : ∀ l : List (NodeBlock P ACP), LinkedFromGenesis P ACP l ↔
      l.map Block.parent = ((P.genesisRoot :: l.map Block.root).dropLast).map some := by
    intro l
    simp [LinkedFromGenesis, List.dropLast_eq_take]
  have hne : P.genesisRoot :: c.map Block.root ≠ [] := List.cons_ne_nil _ _
  have hd : (P.genesisRoot :: (c ++ [B]).map Block.root).dropLast =
      P.genesisRoot :: c.map Block.root := by
    rw [List.map_append, ← List.cons_append, List.map_singleton, List.dropLast_concat]
  rw [key, key, hd, List.getLast?_eq_some_getLast hne]
  conv_lhs => rw [← List.dropLast_concat_getLast hne]
  simp only [List.map_append, List.map_cons, List.map_nil]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    exact ⟨h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

/-- The last root of a chain is the root of its last block, genesis for the empty chain. -/
private theorem lastRoot_eq (acp₀ : ACP) (c : List (NodeBlock P ACP)) :
    (P.genesisRoot :: c.map Block.root).getLast? =
      some ((c.getLast?).getD (P.genesisBlock acp₀)).root := by
  induction c using List.reverseRecOn with
  | nil => rfl
  | append_singleton c X _ =>
    simp only [List.map_append, List.map_cons, List.map_nil, ← List.cons_append,
      List.getLast?_append]
    simp

/-- A store whose blocks are those of `st` with `B` added under its new root has the tree of
`st` with `B` inserted. -/
private theorem tree_insert {st st' : Store P ACP} {B : NodeBlock P ACP}
    (hnew : st.blocks B.root = none)
    (hb : st'.blocks = Function.update st.blocks B.root (some B)) :
    st'.tree = insert B st.tree := by
  ext Y
  change st'.blocks Y.root = some Y ↔ Y = B ∨ st.blocks Y.root = some Y
  rw [hb, Function.update_apply]
  split_ifs with hY
  · refine ⟨fun e => Or.inl (Option.some.inj e).symm, ?_⟩
    rintro (rfl | e)
    · rfl
    · rw [hY, hnew] at e
      cases e
  · refine ⟨Or.inr, ?_⟩
    rintro (rfl | e)
    · exact absurd rfl hY
    · exact e

/-- A prefix of a linked chain is linked. -/
private theorem linked_of_prefix {c d : List (NodeBlock P ACP)} (hl : LinkedFromGenesis P ACP c)
    (hd : d <+: c) : LinkedFromGenesis P ACP d := by
  induction c using List.reverseRecOn with
  | nil => rwa [List.prefix_nil.1 hd]
  | append_singleton c B ih =>
    rcases List.prefix_concat_iff.1 hd with rfl | hd
    · exact hl
    · exact ih (linked_append.1 hl).1 hd

/-- The roots of a chain's FG view: genesis, then the chain's roots. -/
private theorem roots_fgView (c : List (NodeBlock P ACP)) :
    P.fg.roots (c.map Block.fgView) = P.genesisRoot :: c.map Block.root :=
  congrArg (P.genesisRoot :: ·) (List.map_map ..)

/-- The stock reachable-state invariant (`Lemmas/FGStore/Invariant`, private there), copied
public. It reads `update_finality` only through `FinalitySpec`, so it holds for every store
reached under any finality update with that shape. -/
structure CacheGood (acp₀ : ACP) (st : Store P ACP) : Prop where
  root : ∀ r X, st.blocks r = some X → X.root = r
  genesis : st.blocks P.genesisRoot = some (P.genesisBlock acp₀)
  σ_genesis : st.σ P.genesisRoot = FG.ChainState.init P.fg
  finite : {r | (st.blocks r).isSome}.Finite
  step : ∀ B ∈ st.tree, ∀ pr, B.parent = some pr →
    ∃ X ∈ st.tree, X.root = pr ∧ P.fg.stateTransition (st.σ pr) B.fgView = some (st.σ B.root)
  parent_none : ∀ B ∈ st.tree, B.parent = none → B = P.genesisBlock acp₀
  chain : ∀ B ∈ st.tree, ∃ c : List (NodeBlock P ACP), (∀ X ∈ c, X ∈ st.tree) ∧
    LinkedFromGenesis P ACP c ∧ (c.getLast?).getD (P.genesisBlock acp₀) = B
  F_mem : st.F ∈ st.tree
  J_mem : st.J ∈ st.tree
  F_J : st.Anc st.F st.J
  J_just : ∃ B ∈ st.tree, (st.σ B.root).J = st.J.root ∧ (st.σ B.root).hj = st.hj
  hmax_ge : ∀ B ∈ st.tree, (st.σ B.root).h ≤ st.hmax
  hmax_eq : ∃ B ∈ st.tree, (st.σ B.root).h = st.hmax
  F_fin : ∃ B ∈ st.tree, (st.σ B.root).F = st.F.root

private theorem mem_init_tree {acp₀ : ACP} {B : NodeBlock P ACP} :
    B ∈ (init (P := P) acp₀).tree ↔ B = P.genesisBlock acp₀ := by
  change (if B.root = P.genesisRoot then some (P.genesisBlock acp₀) else none) = some B ↔ _
  split_ifs with h
  · exact ⟨fun e => (Option.some.inj e).symm, fun e => e ▸ rfl⟩
  · exact ⟨fun e => (nomatch e), fun e => absurd (by rw [e]; rfl) h⟩

theorem cacheGood_init (acp₀ : ACP) : CacheGood acp₀ (init (P := P) acp₀) := by
  have hg : P.genesisBlock acp₀ ∈ (init (P := P) acp₀).tree := mem_init_tree.2 rfl
  refine ⟨fun r X h => ?_, by simp [init], rfl, ?_, fun B hB pr hp => ?_,
    fun B hB _ => mem_init_tree.1 hB, fun B hB => ⟨[], by simp, by simp [LinkedFromGenesis],
      (mem_init_tree.1 hB).symm⟩, hg, hg, Relation.ReflTransGen.refl,
    ⟨_, hg, rfl, rfl⟩, fun _ _ => le_rfl, ⟨_, hg, rfl⟩, ⟨_, hg, rfl⟩⟩
  · simp only [init] at h
    split_ifs at h with hr
    · cases h; exact hr.symm
  · exact (Set.finite_singleton P.genesisRoot).subset fun r hr => by
      change (if r = P.genesisRoot then some (P.genesisBlock acp₀) else none).isSome at hr
      split_ifs at hr with h
      · exact h
      · simp at hr
  · rw [mem_init_tree.1 hB] at hp
    cases hp

theorem cacheGood_onAttestation {acp₀ : ACP} {st : Store P ACP} (h : CacheGood acp₀ st)
    (a : FG.Att P.n) : CacheGood acp₀ (st.onAttestation a) := by
  obtain ⟨atts, he⟩ := st.onAttestation_eq a
  rw [he]
  exact ⟨h.root, h.genesis, h.σ_genesis, h.finite, h.step, h.parent_none, h.chain, h.F_mem,
    h.J_mem, h.F_J, h.J_just, h.hmax_ge, h.hmax_eq, h.F_fin⟩

theorem cacheGood_onBlockWith {u : Store P ACP → FG.ChainState P.n → Store P ACP}
    (hu : FinalitySpec u) {acp₀ : ACP} {st st' : Store P ACP} (h : CacheGood acp₀ st)
    {B : NodeBlock P ACP} (hB : st.onBlockWith u B = some st') : CacheGood acp₀ st' := by
  obtain ⟨pr, σ', hpar, hnew, hpr, -, hσ', rfl⟩ := onBlockWith_eq_some hB
  obtain ⟨hb, hσ, -, hm, hJ, hF⟩ := hu { st with
    blocks := Function.update st.blocks B.root (some B),
    σ := Function.update st.σ B.root σ' } σ'
  obtain ⟨atts, he⟩ := addAtts_eq (u { st with
    blocks := Function.update st.blocks B.root (some B),
    σ := Function.update st.σ B.root σ' } σ') B.fgPayload
  rw [he]
  generalize hs : ({ (u { st with
    blocks := Function.update st.blocks B.root (some B),
    σ := Function.update st.σ B.root σ' } σ') with atts := atts } : Store P ACP) = s
  have hsb : s.blocks = Function.update st.blocks B.root (some B) := hs ▸ hb
  have hsσ : s.σ = Function.update st.σ B.root σ' := hs ▸ hσ
  have hsm : s.hmax = max st.hmax σ'.h := hs ▸ hm
  have hst : s.tree = insert B st.tree := tree_insert hnew hsb
  have ht₁ : ({ st with blocks := Function.update st.blocks B.root (some B),
                        σ := Function.update st.σ B.root σ' } : Store P ACP).tree =
      insert B st.tree :=
    tree_insert hnew rfl
  have hJ' : (s.J = st.J ∧ s.hj = st.hj) ∨ (Function.update st.blocks B.root (some B) σ'.J =
      some s.J ∧ s.hj = σ'.hj ∧ s.Anc st.F s.J) := by
    rw [Store.Anc, hst]
    subst hs
    rcases hJ with hJ | ⟨h1, h2, h3, -⟩
    · exact Or.inl hJ
    · rw [Store.Anc, ht₁] at h3
      exact Or.inr ⟨h1, h2, h3⟩
  have hF' : s.F = st.F ∨ (Function.update st.blocks B.root (some B) σ'.F = some s.F ∧
      s.Anc st.F s.F ∧ s.Anc s.F s.J) := by
    rw [Store.Anc, hst]
    subst hs
    rcases hF with hF | ⟨h1, h2, -, h4⟩
    · exact Or.inl hF
    · rw [Store.Anc, ht₁] at h2 h4
      exact Or.inr ⟨h1, h2, h4⟩
  clear hs hb hσ hm hJ hF he hB
  -- facts about the old tree and the new block
  have hne : ∀ Y ∈ st.tree, Y.root ≠ B.root := fun Y hY e => by
    rw [← e, (hY : st.blocks Y.root = some Y)] at hnew
    cases hnew
  obtain ⟨X, hX⟩ := Option.isSome_iff_exists.1 hpr
  have hXr : X.root = pr := h.root pr X hX
  have hXt : X ∈ st.tree := by
    change st.blocks X.root = some X
    rwa [hXr]
  have hprB : pr ≠ B.root := hXr ▸ hne X hXt
  have hmem : ∀ {Y}, Y ∈ s.tree ↔ Y = B ∨ Y ∈ st.tree := by
    intro Y; rw [hst]; rfl
  have hold : ∀ {Y}, Y ∈ st.tree → Y ∈ s.tree := fun hY => hmem.2 (Or.inr hY)
  have hBt : B ∈ s.tree := hmem.2 (Or.inl rfl)
  have hσold : ∀ {Y}, Y ∈ st.tree → s.σ Y.root = st.σ Y.root := fun hY => by
    rw [hsσ, Function.update_of_ne (hne _ hY)]
  have hσB : s.σ B.root = σ' := by rw [hsσ, Function.update_self]
  have hroot : ∀ r Y, s.blocks r = some Y → Y.root = r := by
    intro r Y hY
    rw [hsb, Function.update_apply] at hY
    split_ifs at hY with hr
    · cases hY; exact hr.symm
    · exact h.root r Y hY
  have hmemr : ∀ {r Y}, Function.update st.blocks B.root (some B) r = some Y → Y ∈ s.tree :=
    fun {r Y} hY => by
      change s.blocks Y.root = some Y
      rw [hroot r Y (hsb ▸ hY), hsb]
      exact hY
  have hσg : s.σ P.genesisRoot = st.σ P.genesisRoot :=
    hσold (Y := P.genesisBlock acp₀) h.genesis
  refine ⟨hroot, ?_, hσg.trans h.σ_genesis, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hg : P.genesisRoot ≠ B.root := hne (P.genesisBlock acp₀) h.genesis
    rw [hsb, Function.update_of_ne hg]
    exact h.genesis
  · refine (h.finite.insert B.root).subset fun r hr => ?_
    change (s.blocks r).isSome at hr
    rw [hsb, Function.update_apply] at hr
    split_ifs at hr with hrB
    · exact Or.inl hrB
    · exact Or.inr hr
  · intro Y hY pr' hp
    rcases hmem.1 hY with rfl | hY
    · rw [hpar, Option.some.injEq] at hp
      subst hp
      refine ⟨X, hold hXt, hXr, ?_⟩
      rw [hσB, ← hXr, hσold hXt, hXr]
      exact hσ'
    · obtain ⟨Z, hZ, hZr, ht⟩ := h.step Y hY pr' hp
      refine ⟨Z, hold hZ, hZr, ?_⟩
      rw [hσold hY, ← hZr, hσold hZ, hZr]
      exact ht
  · intro Y hY hp
    rcases hmem.1 hY with rfl | hY
    · rw [hpar] at hp
      cases hp
    · exact h.parent_none Y hY hp
  · intro Y hY
    rcases hmem.1 hY with rfl | hY
    · obtain ⟨c, hc, hl, hcX⟩ := h.chain X hXt
      refine ⟨c ++ [Y], fun Z hZ => ?_, linked_append.2 ⟨hl, ?_⟩, by simp⟩
      · rcases List.mem_append.1 hZ with hZ | hZ
        · exact hold (hc Z hZ)
        · simp only [List.mem_singleton] at hZ
          exact hZ ▸ hBt
      · rw [lastRoot_eq acp₀, hcX, hXr, hpar]
    · obtain ⟨c, hc, hl, hcY⟩ := h.chain Y hY
      exact ⟨c, fun Z hZ => hold (hc Z hZ), hl, hcY⟩
  · rcases hF' with hF' | ⟨h1, -, -⟩
    · exact hF' ▸ hold h.F_mem
    · exact hmemr h1
  · rcases hJ' with ⟨hJ', -⟩ | ⟨h1, -, -⟩
    · exact hJ' ▸ hold h.J_mem
    · exact hmemr h1
  · have hmono : st.Anc st.F st.J → s.Anc st.F st.J := Anc.mono fun Y hY => hold hY
    rcases hF' with hF' | ⟨-, -, h3⟩
    · rw [hF']
      rcases hJ' with ⟨hJ', -⟩ | ⟨-, -, h3⟩
      · exact hJ' ▸ hmono h.F_J
      · exact h3
    · exact h3
  · rcases hJ' with ⟨hJ', hj'⟩ | ⟨h1, h2, -⟩
    · obtain ⟨W, hW, h1, h2⟩ := h.J_just
      exact ⟨W, hold hW, by rw [hσold hW, h1, hJ'], by rw [hσold hW, h2, hj']⟩
    · exact ⟨B, hBt, by rw [hσB, hroot _ _ (hsb ▸ h1)], by rw [hσB, h2]⟩
  · intro Y hY
    rw [hsm]
    rcases hmem.1 hY with rfl | hY
    · rw [hσB]; exact le_max_right _ _
    · rw [hσold hY]; exact (h.hmax_ge Y hY).trans (le_max_left _ _)
  · rw [hsm]
    rcases le_total st.hmax σ'.h with hle | hle
    · exact ⟨B, hBt, by rw [hσB, max_eq_right hle]⟩
    · obtain ⟨W, hW, hWe⟩ := h.hmax_eq
      exact ⟨W, hold hW, by rw [hσold hW, hWe, max_eq_left hle]⟩
  · rcases hF' with hF' | ⟨h1, -, -⟩
    · obtain ⟨W, hW, hWe⟩ := h.F_fin
      exact ⟨W, hold hW, by rw [hσold hW, hWe, hF']⟩
    · exact ⟨B, hBt, by rw [hσB, hroot _ _ (hsb ▸ h1)]⟩

/-- Every accepted block's state is at its slot. -/
private theorem CacheGood.slot {acp₀ : ACP} {st : Store P ACP} (h : CacheGood acp₀ st)
    {B : NodeBlock P ACP}
    (hB : B ∈ st.tree) : (st.σ B.root).s = B.slot := by
  rcases hp : B.parent with _ | pr
  · rw [h.parent_none B hB hp]
    change (st.σ P.genesisRoot).s = 0
    rw [h.σ_genesis]
    rfl
  · obtain ⟨X, -, -, ht⟩ := h.step B hB pr hp
    exact (P.fg.stateTransition_L_s ht).2.1

/-- The fold along a chain of the tree linked from genesis is the state of its last block. -/
private theorem CacheGood.fold {acp₀ : ACP} {st : Store P ACP} (h : CacheGood acp₀ st)
    {c : List (NodeBlock P ACP)} (hc : ∀ X ∈ c, X ∈ st.tree) (hl : LinkedFromGenesis P ACP c) :
    P.fg.chainState (c.map Block.fgView) =
      some (st.σ ((c.getLast?).getD (P.genesisBlock acp₀)).root) := by
  induction c using List.reverseRecOn with
  | nil => exact congrArg some h.σ_genesis.symm
  | append_singleton c B ih =>
    obtain ⟨hl', hp⟩ := linked_append.1 hl
    rw [lastRoot_eq acp₀] at hp
    have hc' : ∀ X ∈ c, X ∈ st.tree := fun X hX => hc X (List.mem_append_left _ hX)
    obtain ⟨X, -, -, ht⟩ := h.step B (hc B (by simp)) _ hp
    have hca := P.fg.chainState_append (c.map Block.fgView) B.fgView
    rw [ih hc' hl'] at hca
    refine (Eq.trans ?_ hca).trans ?_
    · exact congrArg P.fg.chainState (List.map_append ..)
    · simp only [List.getLast?_concat, Option.getD_some]
      exact ht

/-- Every block of a chain of the tree linked from genesis, and genesis, is an ancestor of its
last block. -/
private theorem CacheGood.anc {acp₀ : ACP} {st : Store P ACP} (h : CacheGood acp₀ st)
    {c : List (NodeBlock P ACP)} (hc : ∀ X ∈ c, X ∈ st.tree) (hl : LinkedFromGenesis P ACP c)
    {X : NodeBlock P ACP} (hX : X = P.genesisBlock acp₀ ∨ X ∈ c) :
    st.Anc X ((c.getLast?).getD (P.genesisBlock acp₀)) := by
  induction c using List.reverseRecOn with
  | nil =>
    rcases hX with rfl | hX
    · exact Relation.ReflTransGen.refl
    · cases hX
  | append_singleton c B ih =>
    obtain ⟨hl', hp⟩ := linked_append.1 hl
    rw [lastRoot_eq acp₀] at hp
    have hc' : ∀ X ∈ c, X ∈ st.tree := fun X hX => hc X (List.mem_append_left _ hX)
    simp only [List.getLast?_concat, Option.getD_some]
    rcases hX with rfl | hX
    · refine (ih hc' hl' (Or.inl rfl)).tail ⟨?_, hc B (by simp), hp⟩
      rcases hc'' : c.getLast? with _ | Y
      · exact h.genesis
      · exact hc' Y (List.mem_of_getLast? hc'')
    rcases List.mem_append.1 hX with hX | hX
    · refine (ih hc' hl' (Or.inr hX)).tail ⟨?_, hc B (by simp), hp⟩
      rcases hc'' : c.getLast? with _ | Y
      · exact h.genesis
      · exact hc' Y (List.mem_of_getLast? hc'')
    · simp only [List.mem_singleton] at hX
      subst hX
      exact Relation.ReflTransGen.refl


section With

variable {u : Store P ACP → FG.ChainState P.n → Store P ACP} {acp₀ : ACP} {st : Store P ACP}

/-- Every store reached with a finality update of the stock shape satisfies the invariant. -/
theorem ReachableWith.good (hu : FinalitySpec u) (h : ReachableWith u acp₀ st) :
    CacheGood acp₀ st := by
  induction h with
  | refl => exact cacheGood_init acp₀
  | tail _ hs ih =>
    rcases hs with ⟨B, hB⟩ | ⟨a, rfl⟩
    · exact cacheGood_onBlockWith hu ih hB
    · exact cacheGood_onAttestation ih a

variable (hu : FinalitySpec u) (hr : ReachableWith u acp₀ st)
include hu hr

/-- A held root names the block with that root. -/
theorem blocks_root_with {r : Nat} {X : NodeBlock P ACP} (hX : st.blocks r = some X) :
    X.root = r :=
  (hr.good hu).root r X hX

/-- **G0.1 (store)**, `chain_state_of_chain` over `ReachableWith`. -/
theorem chain_state_of_chain_with : ∀ B ∈ st.tree,
    ∃ c : List (NodeBlock P ACP), (∀ X ∈ c, X ∈ st.tree) ∧ LinkedFromGenesis P ACP c ∧
      ((c = [] ∧ B = P.genesisBlock acp₀) ∨ c.getLast? = some B) ∧
      P.fg.chainState (c.map Block.fgView) = some (st.σ B.root) := by
  intro B hB
  have h := hr.good hu
  obtain ⟨c, hc, hl, rfl⟩ := h.chain B hB
  refine ⟨c, hc, hl, ?_, h.fold hc hl⟩
  rcases hc' : c.getLast? with _ | X
  · exact Or.inl ⟨List.getLast?_eq_none_iff.1 hc', rfl⟩
  · exact Or.inr rfl

/-- **F.2 at the store**, `accepted_tree` over `ReachableWith`. -/
theorem accepted_tree_with :
    st.tree.Finite ∧ Coherent st.tree ∧ P.genesisBlock acp₀ ∈ st.tree ∧
      ∀ B ∈ st.tree, st.Anc (P.genesisBlock acp₀) B := by
  have h := hr.good hu
  refine ⟨?_, ⟨fun B hB C hC he => ?_, fun B hB C hC hp => ?_⟩, h.genesis, fun B hB => ?_⟩
  · refine Set.Finite.of_finite_image (h.finite.subset ?_) (f := Block.root)
      (fun B hB C hC he => ?_)
    · rintro _ ⟨B, hB, rfl⟩
      change (st.blocks B.root).isSome
      rw [(hB : st.blocks B.root = some B)]
      rfl
    · exact Option.some.inj ((hB : st.blocks B.root = some B).symm.trans
        (he ▸ (hC : st.blocks C.root = some C)))
  · exact Option.some.inj ((hB : st.blocks B.root = some B).symm.trans
      (he ▸ (hC : st.blocks C.root = some C)))
  · obtain ⟨X, -, -, ht⟩ := h.step C hC _ hp
    exact h.slot hB ▸ (P.fg.stateTransition_L_s ht).2.2
  · obtain ⟨c, hc, hl, rfl⟩ := h.chain B hB
    exact h.anc hc hl (Or.inl rfl)

omit hr in
/-- **F.2 at the store**, `tree_grows` with the finality update `u`. -/
theorem tree_grows_with :
    (∀ B st', st.onBlockWith u B = some st' → st'.tree = insert B st.tree) ∧
      ∀ a, (st.onAttestation a).tree = st.tree := by
  refine ⟨fun B st' hB => ?_, fun a => ?_⟩
  · obtain ⟨pr, σ', -, hnew, -, -, -, rfl⟩ := onBlockWith_eq_some hB
    obtain ⟨atts, he⟩ := addAtts_eq (u { st with
      blocks := Function.update st.blocks B.root (some B),
      σ := Function.update st.σ B.root σ' } σ') B.fgPayload
    rw [he]
    exact tree_insert hnew (hu _ _).1
  · obtain ⟨atts, he⟩ := st.onAttestation_eq a
    rw [he]
    rfl

/-- **G0.3**, `cache_invariants` over `ReachableWith`. -/
theorem cache_invariants_with :
    st.F ∈ st.tree ∧ st.J ∈ st.tree ∧ st.Anc st.F st.J ∧
      (∃ B ∈ st.tree, (st.σ B.root).J = st.J.root ∧ (st.σ B.root).hj = st.hj) ∧
      (∀ B ∈ st.tree, (st.σ B.root).h ≤ st.hmax) ∧
      (∃ B ∈ st.tree, (st.σ B.root).h = st.hmax) ∧
      ∃ B ∈ st.tree, (st.σ B.root).F = st.F.root := by
  have h := hr.good hu
  exact ⟨h.F_mem, h.J_mem, h.F_J, h.J_just, h.hmax_ge, h.hmax_eq, h.F_fin⟩

/-- **G0.2 (c), (h) at the store**, `entry_state_of_source` over `ReachableWith`. -/
theorem entry_state_of_source_with : ∀ B ∈ st.tree,
    (∃ E ∈ st.tree, E.root = (st.σ B.root).Th ∧ st.Anc E B ∧
      (st.σ E.root).h = (st.σ B.root).h ∧ (st.σ E.root).Th = (st.σ B.root).Th) ∧
    (∃ X ∈ st.tree, X.root = (st.σ B.root).F ∧ st.Anc X B) ∧
    (∃ X ∈ st.tree, X.root = (st.σ B.root).J ∧ st.Anc X B) := by
  intro B hB
  have h := hr.good hu
  obtain ⟨c, hc, hl, rfl⟩ := h.chain B hB
  have hf := h.fold hc hl
  have hroot : ∀ r ∈ P.fg.roots (c.map Block.fgView), ∃ X ∈ st.tree, X.root = r ∧
      st.Anc X ((c.getLast?).getD (P.genesisBlock acp₀)) := by
    intro r hr
    rw [roots_fgView, List.mem_cons, List.mem_map] at hr
    rcases hr with rfl | ⟨X, hX, rfl⟩
    · exact ⟨_, h.genesis, rfl, h.anc hc hl (Or.inl rfl)⟩
    · exact ⟨X, hc X hX, rfl, h.anc hc hl (Or.inr hX)⟩
  obtain ⟨-, hJ, hF⟩ := P.fg.mem_roots_of_chainState hf
  refine ⟨?_, hroot _ hF, hroot _ hJ⟩
  obtain ⟨c', hpre, σ'', h1, h2, h3, h4⟩ := P.fg.exists_entry_prefix hf
  have hc' : c' = (c.take c'.length).map Block.fgView :=
    (List.prefix_iff_eq_take.1 hpre).trans (List.map_take ..).symm
  rw [hc'] at h1 h4
  have hd : c.take c'.length <+: c := List.take_prefix _ _
  have hdc : ∀ X ∈ c.take c'.length, X ∈ c := fun X hX => hd.subset hX
  have hdl := linked_of_prefix hl hd
  have h1' := Option.some.inj (h1.symm.trans (h.fold (fun X hX => hc X (hdc X hX)) hdl))
  have h4' := Option.some.inj ((lastRoot_eq acp₀ _).symm.trans
    ((congrArg List.getLast? (roots_fgView _)).symm.trans h4))
  refine ⟨_, ?_, h4', h.anc hc hl ?_, h1' ▸ h2, h1' ▸ h3⟩
  · rcases he : (c.take c'.length).getLast? with _ | X
    · exact h.genesis
    · exact hc X (hdc X (List.mem_of_getLast? he))
  · rcases he : (c.take c'.length).getLast? with _ | X
    · exact Or.inl rfl
    · exact Or.inr (hdc X (List.mem_of_getLast? he))

/-- Genesis is held. -/
theorem genesis_mem_with : P.genesisBlock acp₀ ∈ st.tree :=
  (hr.good hu).genesis

/-- Genesis has the initial chain state. -/
theorem σ_genesis_with : st.σ P.genesisRoot = FG.ChainState.init P.fg :=
  (hr.good hu).σ_genesis

/-- An accepted block's state is the transition of its parent's, and the parent is held. -/
theorem step_σ_with {W : NodeBlock P ACP} (hW : W ∈ st.tree) {pr : Nat}
    (hp : W.parent = some pr) :
    ∃ X ∈ st.tree, X.root = pr ∧
      P.fg.stateTransition (st.σ pr) W.fgView = some (st.σ W.root) :=
  (hr.good hu).step W hW pr hp

/-- Along ancestry the state height does not decrease (`h_le_of_store_anc`). -/
theorem h_le_of_store_anc_with {A W : NodeBlock P ACP} (h : st.Anc A W) :
    (st.σ A.root).h ≤ (st.σ W.root).h := by
  induction h with
  | refl => exact le_rfl
  | tail _ hYW ih =>
    obtain ⟨-, -, -, ht⟩ := step_σ_with hu hr hYW.2.1 hYW.2.2
    rcases Healing.stateTransition_bits ht with ⟨hh, -⟩ | ⟨hh, -⟩ <;> omega

/-- **Entry constancy** (`Th_eq_of_anc`): while the height stays along ancestry, the entry
stays. -/
theorem Th_eq_of_anc_with {A W : NodeBlock P ACP} (h : st.Anc A W)
    (hh : (st.σ W.root).h = (st.σ A.root).h) : (st.σ W.root).Th = (st.σ A.root).Th := by
  induction h with
  | refl => rfl
  | tail hAY hYW ih =>
    obtain ⟨-, -, -, ht⟩ := step_σ_with hu hr hYW.2.1 hYW.2.2
    have h₁ := h_le_of_store_anc_with hu hr hAY
    rcases (Goldilocks.Store.step_fields ht).1 with ⟨he, hT⟩ | ⟨he, -⟩
    · rw [hT]; exact ih (by omega)
    · omega

/-- The state of a held block is above its justification (`hj_lt_h`). -/
theorem hj_lt_h_with {B : NodeBlock P ACP} (hB : B ∈ st.tree) :
    (st.σ B.root).hj < (st.σ B.root).h := by
  obtain ⟨c, -, -, -, hc⟩ := chain_state_of_chain_with hu hr B hB
  exact (FG.chain_invariants P.fg _ _ hc).2.2.1

/-- The justification of a held block's state names a held ancestor: genesis with justified
height `0`, or the entry of the justified height (`J_entry_of_reachable`, with the height of
the genesis arm). -/
theorem J_entry_hj_with {W : NodeBlock P ACP} (hW : W ∈ st.tree) :
    ∃ E ∈ st.tree, E.root = (st.σ W.root).J ∧ st.Anc E W ∧
      ((E = P.genesisBlock acp₀ ∧ (st.σ W.root).hj = 0) ∨
        ((st.σ E.root).h = (st.σ W.root).hj ∧ (st.σ E.root).Th = E.root)) := by
  have hg := genesis_mem_with hu hr
  have hA := (accepted_tree_with hu hr).2.2.2 W hW
  clear hW
  induction hA with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis_with hu hr]
    exact ⟨_, hg, rfl, .refl, Or.inl ⟨rfl, rfl⟩⟩
  | tail _ hYW ih =>
    obtain ⟨X, -, hXr, ht⟩ := step_σ_with hu hr hYW.2.1 hYW.2.2
    rcases (Goldilocks.Store.step_fields ht).2 with ⟨hJ, hj⟩ | ⟨hJ, hj⟩
    · obtain ⟨E, hE, h1, hEY, h2⟩ := ih
      refine ⟨E, hE, h1.trans hJ.symm, hEY.tail hYW, ?_⟩
      rw [hj]
      exact h2
    · obtain ⟨⟨E, hE, h1, hEY, h2, h3⟩, -⟩ := entry_state_of_source_with hu hr _ hYW.1
      exact ⟨E, hE, h1.trans hJ.symm, hEY.tail hYW, Or.inr ⟨h2.trans hj.symm, h3.trans h1.symm⟩⟩

/-- `J_entry_of_reachable` over `ReachableWith`, in the stock form. -/
theorem J_entry_with {W : NodeBlock P ACP} (hW : W ∈ st.tree) :
    ∃ E ∈ st.tree, E.root = (st.σ W.root).J ∧ st.Anc E W ∧ (E = P.genesisBlock acp₀ ∨
      ((st.σ E.root).h = (st.σ W.root).hj ∧ (st.σ E.root).Th = E.root)) :=
  let ⟨E, hE, h1, h2, h3⟩ := J_entry_hj_with hu hr hW
  ⟨E, hE, h1, h2, h3.imp_left And.left⟩

/-- The block named by a justification has at least its recorded height (`J_height_le`). -/
theorem J_height_le_with {W J : NodeBlock P ACP}
    (hW : W ∈ st.tree) (hJ : J ∈ st.tree) (hJr : J.root = (st.σ W.root).J) :
    (st.σ W.root).hj ≤ (st.σ J.root).h := by
  have hA := (accepted_tree_with hu hr).2.2.2 W hW
  clear hW
  induction hA generalizing J with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis_with hu hr]
    exact Nat.zero_le _
  | tail _ hYW ih =>
    obtain ⟨_, _, _, ht⟩ := step_σ_with hu hr hYW.2.1 hYW.2.2
    rcases (Goldilocks.Store.step_fields ht).2 with ⟨hroot, hh⟩ | ⟨hroot, hh⟩
    · rw [hh]
      exact ih hJ (hJr.trans hroot)
    · obtain ⟨⟨E, hE, hEr, _, hEh, _⟩, _⟩ := entry_state_of_source_with hu hr _ hYW.1
      have he : J = E := (accepted_tree_with hu hr).2.1.1
        hJ hE ((hJr.trans hroot).trans hEr.symm)
      rw [he, hEh, hh]

/-- The store's `Σ.h_j` is at most the height of `Σ.J`. -/
theorem store_J_height_le_with : st.hj ≤ (st.σ st.J.root).h := by
  obtain ⟨-, hJm, -, ⟨B, hB, hBJ, hBhj⟩, -⟩ := cache_invariants_with hu hr
  exact hBhj ▸ J_height_le_with hu hr hB hJm hBJ.symm

/-- **The store's `Σ.J`**: genesis with `Σ.h_j = 0`, or an entry of state height `Σ.h_j` that is
its own entry; in both cases below a held block whose state has `Σ.J` as justification and a
height above `Σ.h_j`. -/
theorem store_J_entry_with :
    ((st.J = P.genesisBlock acp₀ ∧ st.hj = 0) ∨
      ((st.σ st.J.root).h = st.hj ∧ (st.σ st.J.root).Th = st.J.root)) ∧
    ∃ W ∈ st.tree, st.Anc st.J W ∧ st.hj < (st.σ W.root).h := by
  obtain ⟨-, hJm, -, ⟨B, hB, hBJ, hBhj⟩, -⟩ := cache_invariants_with hu hr
  obtain ⟨E, hE, hEr, hEB, hcase⟩ := J_entry_hj_with hu hr hB
  obtain rfl : E = st.J :=
    (accepted_tree_with hu hr).2.1.1 hE hJm (hEr.trans hBJ)
  refine ⟨?_, B, hB, hEB, hBhj ▸ hj_lt_h_with hu hr hB⟩
  rcases hcase with ⟨he, h0⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨he, hBhj ▸ h0⟩
  · exact Or.inr ⟨h1.trans hBhj, h2⟩

/-- **The entry of every height of a chain** (`Healing.entry_at_height`). -/
theorem entry_at_height_with {C : NodeBlock P ACP} (hC : C ∈ st.tree) {h : Nat} (h1 : 1 ≤ h)
    (hle : h ≤ (st.σ C.root).h) :
    ∃ Z ∈ st.tree, st.Anc Z C ∧ (st.σ Z.root).h = h ∧ (st.σ Z.root).Th = Z.root := by
  have key : ∀ {W : NodeBlock P ACP} {h : Nat}, W ∈ st.tree → (st.σ W.root).h = h →
      ∃ Z ∈ st.tree, st.Anc Z W ∧ (st.σ Z.root).h = h ∧ (st.σ Z.root).Th = Z.root := by
    intro W h hW he
    obtain ⟨⟨E, hE, hEr, hEW, hEh, hET⟩, -⟩ := entry_state_of_source_with hu hr _ hW
    exact ⟨E, hE, hEW, hEh.trans he, hET.trans hEr.symm⟩
  have hA := (accepted_tree_with hu hr).2.2.2 C hC
  clear hC
  induction hA generalizing h with
  | refl =>
    have h₁ : ((st.σ (P.genesisBlock acp₀).root)).h = 1 := by
      rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis_with hu hr]; rfl
    exact key (genesis_mem_with hu hr) (by omega)
  | tail _ hYW ih =>
    rcases eq_or_lt_of_le hle with he | hlt
    · exact key hYW.2.1 he.symm
    · obtain ⟨-, -, -, ht⟩ := step_σ_with hu hr hYW.2.1 hYW.2.2
      obtain ⟨Z, hZ, hZY, hZh, hZT⟩ := ih h1 (by
        rcases Healing.stateTransition_bits ht with ⟨hh, -⟩ | ⟨hh, -⟩ <;> (clear * - hlt hh; omega))
      exact ⟨Z, hZ, hZY.tail hYW, hZh, hZT⟩

end With


/-- Some `q` validators each have an attestation on the chain naming `T`. -/
private def Quorum (gp : FG.FGParams) (c : List (FG.FGBlock gp.n)) (T : Nat) : Prop :=
  ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧ ∀ v ∈ Q, ∃ a ∈ gp.chainAtts c, a.val = v ∧ a.T = T

/-- The justified and finalized roots of a chain state and its pending pairs are genesis or named
by a quorum of attestations on the chain; its progress bits by attestations on its entry. -/
private structure Named (gp : FG.FGParams) (c : List (FG.FGBlock gp.n))
    (σ : FG.ChainState gp.n) : Prop where
  prog : ∀ v ∈ σ.prog, ∃ a ∈ gp.chainAtts c, a.val = v ∧ a.T = σ.Th
  pending : ∀ p ∈ σ.pending, Quorum gp c p.2
  J : σ.J = gp.genesis ∨ Quorum gp c σ.J
  F : σ.F = gp.genesis ∨ Quorum gp c σ.F

private theorem named_step (gp : FG.FGParams) {c : List (FG.FGBlock gp.n)}
    {σ σ' : FG.ChainState gp.n} {B : FG.FGBlock gp.n} (hc : gp.chainState c = some σ)
    (hN : Named gp c σ) (h : gp.stateTransition σ B = some σ') : Named gp (c ++ [B]) σ' := by
  have hatts : gp.chainAtts (c ++ [B]) = gp.chainAtts c ++ B.atts := by
    simp [FG.FGParams.chainAtts]
  have liftA : ∀ {a}, a ∈ gp.chainAtts c → a ∈ gp.chainAtts (c ++ [B]) := fun h => by
    rw [hatts]; exact List.mem_append_left _ h
  have liftQ : ∀ {T}, Quorum gp c T → Quorum gp (c ++ [B]) T := fun ⟨Q, hQ, hv⟩ =>
    ⟨Q, hQ, fun v hv' => let ⟨a, ha, h1⟩ := hv v hv'; ⟨a, liftA ha, h1⟩⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hts⟩ := FG.chain_invariants gp c σ hc
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  have hsub := FG.ChainState.foldl_processAtt_target_subset { σ with s := B.slot } B.atts hts
  have hP := fun v => @Goldilocks.Store.mem_foldl_prog _ { σ with s := B.slot } B.atts v
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he] at hsub hP ⊢
  dsimp only at hsub hP ⊢
  have hprog : ∀ v ∈ p, ∃ a ∈ gp.chainAtts (c ++ [B]), a.val = v ∧ a.T = σ.Th := by
    intro v hv
    rcases hP v hv with hv | ⟨a, ha, h1, h2⟩
    · obtain ⟨a, ha, h'⟩ := hN.prog v hv
      exact ⟨a, liftA ha, h'⟩
    · exact ⟨a, by rw [hatts]; exact List.mem_append_right _ ha, h1, h2⟩
  obtain ⟨F, hF, σ₁, rfl, hFc, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  have hpend : ∀ r ∈ σ.pending.filter (fun p => hF < p.1), Quorum gp (c ++ [B]) r.2 :=
    fun r hr => liftQ (hN.pending r (List.mem_of_mem_filter hr))
  have hF₁ : F = gp.genesis ∨ Quorum gp (c ++ [B]) F := by
    rcases hFc with ⟨rfl, -⟩ | ⟨hm, -⟩
    · exact hN.F.imp_right liftQ
    · exact Or.inr (liftQ (hN.pending _ hm))
  rcases hcase with ⟨hj, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he']
  · have hQ : Quorum gp (c ++ [B]) σ.Th := ⟨t, hj.1, fun v hv => hprog v (hsub hv)⟩
    refine ⟨by simp [FG.ChainState.advance], fun r hr => ?_, Or.inr hQ, hF₁⟩
    simp only [FG.ChainState.advance] at hr
    rcases List.mem_append.1 (List.mem_of_mem_drop hr) with hr | hr
    · exact hpend r hr
    · rw [List.mem_singleton] at hr
      subst hr
      exact hQ
  · exact ⟨by simp [FG.ChainState.advance], hpend, hN.J.imp_right liftQ, hF₁⟩
  · exact ⟨hprog, hpend, hN.J.imp_right liftQ, hF₁⟩

private theorem named (gp : FG.FGParams) {c : List (FG.FGBlock gp.n)} {σ : FG.ChainState gp.n}
    (h : gp.chainState c = some σ) : Named gp c σ :=
  gp.chainState_induction (P := fun c σ => Named gp c σ)
    ⟨by simp [FG.ChainState.init], by simp [FG.ChainState.init], Or.inl rfl, Or.inl rfl⟩
    (fun _ _ _ _ hc hN hB => named_step gp hc hN hB) h


/-! ## Further store lemmas over `ReachableWith` (lane Q) -/

section More

variable {u : Store P ACP → FG.ChainState P.n → Store P ACP} {acp₀ : ACP} {st : Store P ACP}

/-- An unheld root keeps the initial chain state (`σ_of_blocks_none`). -/
theorem σ_of_blocks_none_with (hu : FinalitySpec u) (hr : ReachableWith u acp₀ st) {r : Nat}
    (hn : st.blocks r = none) : st.σ r = FG.ChainState.init P.fg := by
  induction hr generalizing r with
  | refl => rfl
  | @tail s₀ s' _ hs ih =>
    rcases hs with ⟨B, hB⟩ | ⟨a, rfl⟩
    · obtain ⟨pr, σ', -, -, -, -, -, rfl⟩ := onBlockWith_eq_some hB
      obtain ⟨hb, hσ, -⟩ := hu { s₀ with
        blocks := Function.update s₀.blocks B.root (some B),
        σ := Function.update s₀.σ B.root σ' } σ'
      obtain ⟨atts, he⟩ := addAtts_eq (u { s₀ with
        blocks := Function.update s₀.blocks B.root (some B),
        σ := Function.update s₀.σ B.root σ' } σ') B.fgPayload
      rw [he] at hn ⊢
      have hn' := hn
      change (u _ σ').blocks r = none at hn'
      rw [hb] at hn'
      have hne : r ≠ B.root := fun e => by simp [e] at hn'
      change (u _ σ').σ r = _
      rw [hσ]
      change Function.update s₀.σ B.root σ' r = _
      change Function.update s₀.blocks B.root (some B) r = none at hn'
      rw [Function.update_of_ne hne] at hn' ⊢
      exact ih hn'
    · obtain ⟨atts, he⟩ := onAttestation_eq s₀ a
      rw [he] at hn ⊢
      exact ih hn

variable (hu : FinalitySpec u) (hr : ReachableWith u acp₀ st)
include hu hr

/-- A report from a held source preserves its entry ancestor (`entry_of_createAtt`). -/
theorem entry_of_createAtt_with {Λ Λ' : FG.Record} {v : Fin P.n}
    {src : NodeBlock P ACP} {a : FG.Att P.n} (hsrc : src ∈ st.tree)
    (h : Λ.createAtt v (st.σ (st.σ src.root).Th) = some (a, Λ')) :
    ∃ E ∈ st.tree, E.root = a.T ∧ st.Anc E src ∧
      (st.σ src.root).Th = E.root ∧ (st.σ E.root).Th = E.root ∧
      (st.σ E.root).h = (st.σ src.root).h ∧ (st.σ src.root).h = a.h := by
  obtain ⟨hh, hT⟩ := Healing.Store.createAtt_eq h
  obtain ⟨⟨E, hE, hEr, hEC, hEh, hET⟩, _⟩ := entry_state_of_source_with hu hr src hsrc
  refine ⟨E, hE, ?_, hEC, hEr.symm, hET.trans hEr.symm, hEh, ?_⟩
  · rw [hT, ← hEr, hET]
    exact hEr
  · rw [hh, ← hEr, hEh]

/-- The height pair that `fg_attest` signs names a held block (`exists_entry_of_createAtt`). -/
theorem exists_entry_of_createAtt_with {Λ Λ' : FG.Record} {v : Fin P.n}
    {src : NodeBlock P ACP} {a : FG.Att P.n}
    (h : Λ.createAtt v (st.σ (st.σ src.root).Th) = some (a, Λ')) :
    ∃ E ∈ st.tree, E.root = a.T ∧ (st.σ E.root).h = a.h := by
  obtain ⟨hh, hT⟩ := Healing.Store.createAtt_eq h
  rcases hs : st.blocks src.root with _ | X
  · have hg : (st.σ src.root).Th = P.genesisRoot := by
      rw [σ_of_blocks_none_with hu hr hs]; rfl
    rw [hg, σ_genesis_with hu hr] at hh hT
    refine ⟨_, genesis_mem_with hu hr, ?_, ?_⟩
    · rw [hT]; rfl
    · rw [hh]; exact congrArg FG.ChainState.h (σ_genesis_with hu hr)
  · have hXr : X.root = src.root := blocks_root_with hu hr hs
    have hX : X ∈ st.tree := by change st.blocks X.root = some X; rw [hXr]; exact hs
    obtain ⟨⟨E, hE, hEr, -, hEh, hET⟩, -⟩ := entry_state_of_source_with hu hr X hX
    rw [hXr] at hEr hEh hET
    refine ⟨E, hE, ?_, ?_⟩
    · rw [hT, ← hEr, hET]
      exact hEr
    · rw [hh, ← hEr]

/-- The height pair that `fg_attest` signs is at most `Σ.h_max` (`createAtt_h_le`). -/
theorem createAtt_h_le_with {Λ Λ' : FG.Record} {v : Fin P.n}
    {src : NodeBlock P ACP} {a : FG.Att P.n}
    (h : Λ.createAtt v (st.σ (st.σ src.root).Th) = some (a, Λ')) : a.h ≤ st.hmax := by
  obtain ⟨E, hE, -, hEh⟩ := exists_entry_of_createAtt_with hu hr h
  exact hEh ▸ (cache_invariants_with hu hr).2.2.2.2.1 E hE

/-- In a store, `Σ.J` and `Σ.F` are genesis or named by a quorum of attestations that blocks of
the tree carry (`Compose.cache_quorum`). -/
theorem cache_quorum_with :
    ∀ X ∈ ({st.J, st.F} : Set (NodeBlock P ACP)), X.root = P.genesisRoot ∨
      ∃ Q : Finset (Fin P.n), P.fg.q ≤ Q.card ∧ ∀ v ∈ Q,
        ∃ Z ∈ st.tree, ∃ a ∈ Z.fgPayload, a.val = v ∧ a.T = X.root := by
  obtain ⟨-, -, -, ⟨BJ, hBJ, hJ, -⟩, -, -, BF, hBF, hF⟩ := cache_invariants_with hu hr
  have key : ∀ B ∈ st.tree, ∀ T, ((st.σ B.root).J = T ∨ (st.σ B.root).F = T) →
      T = P.genesisRoot ∨ ∃ Q : Finset (Fin P.n), P.fg.q ≤ Q.card ∧ ∀ v ∈ Q,
        ∃ Z ∈ st.tree, ∃ a ∈ Z.fgPayload, a.val = v ∧ a.T = T := by
    intro B hB T hT
    obtain ⟨c, hc, -, -, hcs⟩ := chain_state_of_chain_with hu hr B hB
    have hN := named P.fg hcs
    have lift : Quorum P.fg (c.map Block.fgView) T → ∃ Q : Finset (Fin P.n), P.fg.q ≤ Q.card ∧
        ∀ v ∈ Q, ∃ Z ∈ st.tree, ∃ a ∈ Z.fgPayload, a.val = v ∧ a.T = T := by
      rintro ⟨Q, hQ, hv⟩
      refine ⟨Q, hQ, fun v hv' => ?_⟩
      obtain ⟨a, ha, h1, h2⟩ := hv v hv'
      simp only [FG.FGParams.chainAtts, List.mem_flatMap] at ha
      obtain ⟨Z', hZ', ha⟩ := ha
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hZ'
      exact ⟨Z, hc Z hZ, a, ha, h1, h2⟩
    rcases hT with rfl | rfl
    · exact hN.J.imp_right lift
    · exact hN.F.imp_right lift
  rintro X (rfl | rfl)
  · exact key BJ hBJ _ (Or.inl hJ)
  · exact key BF hBF _ (Or.inr hF)

/-- The tree half of G0.4 (frame realization) for the stock frame `toFrame`. -/
theorem frame_realization_with :
    FrameOK st.toFrame ∧ (st.headHeightFloor = st.hmax ∨ st.headHeightFloor = st.hmax - 1) := by
  obtain ⟨hfin, hcoh, -, -⟩ := accepted_tree_with hu hr
  obtain ⟨hF, hJ, hFJ, -⟩ := cache_invariants_with hu hr
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

omit hu in
/-- One state per block across two stores reached with `u` (`σ_eq_of_mem`). -/
theorem σ_eq_of_mem_with (hu : FinalitySpec u) {st₂ : Store P ACP}
    (hr₂ : ReachableWith u acp₀ st₂)
    {U : Set (NodeBlock P ACP)} (hU : Set.InjOn Block.root U) (h₁ : st.tree ⊆ U)
    (h₂ : st₂.tree ⊆ U) {B : NodeBlock P ACP} (hB₁ : B ∈ st.tree) (hB₂ : B ∈ st₂.tree) :
    st.σ B.root = st₂.σ B.root := by
  have hg := (accepted_tree_with hu hr).2.2.2 B hB₁
  clear hB₁
  induction hg with
  | refl =>
    change st.σ P.genesisRoot = st₂.σ P.genesisRoot
    rw [σ_genesis_with hu hr, σ_genesis_with hu hr₂]
  | @tail W' W _ hpar ih =>
    obtain ⟨hW'₁, hW₁, hp⟩ := hpar
    obtain ⟨X, hX, hXr, ht₂⟩ := step_σ_with hu hr₂ hB₂ hp
    obtain rfl : X = W' := hU (h₂ hX) (h₁ hW'₁) hXr
    obtain ⟨-, -, -, ht₁⟩ := step_σ_with hu hr hW₁ hp
    rw [ih hX] at ht₁
    exact Option.some.inj (ht₁.symm.trans ht₂)

end More


/-! ## Held chains and held safety over `ReachableWith` (lane W) -/

section Held

variable {u : Store P ACP → FG.ChainState P.n → Store P ACP} {acp₀ : ACP} {st : Store P ACP}

/-- A target bit after counting is old or set by a counted non-timeout attestation on the
entry. -/
private theorem mem_foldl_target {n : Nat} {σ : FG.ChainState n} {atts : List (FG.Att n)}
    {v : Fin n} (h : v ∈ (atts.foldl FG.ChainState.processAtt σ).target) :
    v ∈ σ.target ∨ ∃ a ∈ atts, a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false := by
  induction atts generalizing σ with
  | nil => exact Or.inl h
  | cons a as ih =>
    obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq σ [a]
    have hh : (σ.processAtt a).h = σ.h := by simpa using congrArg FG.ChainState.h he
    have hT : (σ.processAtt a).Th = σ.Th := by simpa using congrArg FG.ChainState.Th he
    rcases ih h with h | ⟨b, hb, hb'⟩
    · have : v ∈ σ.target ∨ (a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false) := by
        clear ih he hh hT
        unfold FG.ChainState.processAtt at h
        dsimp only at h
        repeat' split at h
        all_goals aesop
      exact this.imp_right fun h => ⟨a, List.mem_cons_self, h⟩
    · rw [hh, hT] at hb'
      exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hb'⟩

/-- A justification `(h_j, J)` with `h_j ≥ 1` has a quorum of non-timeout attestations on the
chain with height pair `(h_j, J)` (with each target bit's attestation, for the induction). -/
private theorem justification_quorum (gp : FG.FGParams) {c : List (FG.FGBlock gp.n)}
    {σ : FG.ChainState gp.n} (h : gp.chainState c = some σ) :
    (∀ v ∈ σ.target, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false) ∧
    (1 ≤ σ.hj → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧ ∀ v ∈ Q, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.hj ∧ a.T = σ.J ∧ a.timeout = false) := by
  refine gp.chainState_induction (P := fun c σ =>
    (∀ v ∈ σ.target, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false) ∧
    (1 ≤ σ.hj → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧ ∀ v ∈ Q, ∃ a ∈ gp.chainAtts c,
      a.val = v ∧ a.h = σ.hj ∧ a.T = σ.J ∧ a.timeout = false))
    ⟨by simp [FG.ChainState.init], by simp [FG.ChainState.init]⟩ ?_ h
  intro c σ B σ' _ ⟨ht, hq⟩ hB
  have liftA : ∀ {a}, a ∈ gp.chainAtts c → a ∈ gp.chainAtts (c ++ [B]) := fun h => by
    simp only [FG.FGParams.chainAtts, List.flatMap_append, List.mem_append] at h ⊢
    exact Or.inl h
  have liftB : ∀ {a}, a ∈ B.atts → a ∈ gp.chainAtts (c ++ [B]) := fun h => by
    simp only [FG.FGParams.chainAtts, List.flatMap_append, List.mem_append]
    exact Or.inr (by simpa using h)
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 hB
  have hT := fun v => @mem_foldl_target _ { σ with s := B.slot } B.atts v
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he] at hT ⊢
  dsimp only at hT
  have ht₀ : ∀ v ∈ t, ∃ a ∈ gp.chainAtts (c ++ [B]),
      a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th ∧ a.timeout = false := by
    intro v hv
    rcases hT v hv with hv | ⟨a, ha, h'⟩
    · obtain ⟨a, ha, h'⟩ := ht v hv
      exact ⟨a, liftA ha, h'⟩
    · exact ⟨a, liftB ha, h'⟩
  have hq₀ : 1 ≤ σ.hj → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧
      ∀ v ∈ Q, ∃ a ∈ gp.chainAtts (c ++ [B]),
        a.val = v ∧ a.h = σ.hj ∧ a.T = σ.J ∧ a.timeout = false := fun h1 =>
    let ⟨Q, hQ, hv⟩ := hq h1
    ⟨Q, hQ, fun v h => let ⟨a, ha, h'⟩ := hv v h; ⟨a, liftA ha, h'⟩⟩
  obtain ⟨F, hF', σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  rcases hcase with ⟨⟨hq', -⟩, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he']
  · exact ⟨by simp [FG.ChainState.advance], fun _ => ⟨t, hq', ht₀⟩⟩
  · exact ⟨by simp [FG.ChainState.advance], hq₀⟩
  · exact ⟨ht₀, hq₀⟩


/-- **The chain of a held block.** A block `B` of a reachable store has a chain from genesis
whose state is `B`'s, every block of which (and genesis) is at or below `B` in the store, and
whose attestations are on blocks at or below `B`. -/
theorem held_chain_with {st : Store P ACP}
    (hu : FinalitySpec u) (hR : ReachableWith u acp₀ st) {B : NodeBlock P ACP}
    (hB : B ∈ st.tree) :
    ∃ c : List (NodeBlock P ACP), P.fg.chainState (c.map Block.fgView) = some (st.σ B.root) ∧
      (∀ X ∈ P.genesisBlock acp₀ :: c, X ∈ st.tree ∧ st.Anc X B) ∧
      ∀ a ∈ P.fg.chainAtts (c.map Block.fgView), ∃ Y ∈ st.tree, st.Anc Y B ∧ a ∈ Y.fgPayload := by
  obtain ⟨c, hc, hl, hlast, hσ⟩ := chain_state_of_chain_with hu hR B hB
  obtain ⟨-, -, hg, -⟩ := accepted_tree_with hu hR
  have hanc := anc_of_linked c _ hg hc hl B (by
    rcases hlast with ⟨rfl, rfl⟩ | h
    · rfl
    · simp [List.getLast?_cons, h])
  refine ⟨c, hσ, fun X hX => ⟨?_, hanc X hX⟩, fun a ha => ?_⟩
  · rcases List.mem_cons.1 hX with rfl | h
    exacts [hg, hc _ h]
  · obtain ⟨_, hX, haX⟩ := List.mem_flatMap.1 ha
    obtain ⟨X, hXc, rfl⟩ := List.mem_map.1 hX
    exact ⟨X, hc X hXc, hanc X (List.mem_cons_of_mem _ hXc), haX⟩

/-- **Two justifications at one height cross.** Held blocks of two reachable stores with the
same `h_j` and different `J` give at least `2q − n` validators, each with an E2 pair among the
attestations on blocks at or below the two held blocks. -/
theorem justified_crossing_with {st₁ st₂ : Store P ACP}
    (hu : FinalitySpec u) (hR₁ : ReachableWith u acp₀ st₁)
    (hR₂ : ReachableWith u acp₀ st₂) {B B' : NodeBlock P ACP} (hB : B ∈ st₁.tree)
    (hB' : B' ∈ st₂.tree)
    (he : (st₁.σ B.root).hj = (st₂.σ B'.root).hj) (hne : (st₁.σ B.root).J ≠ (st₂.σ B'.root).J) :
    ∃ W : Finset (Fin P.n), 2 * P.fg.q - P.n ≤ W.card ∧ ∀ v ∈ W,
      ∃ a, (∃ Y ∈ st₁.tree, st₁.Anc Y B ∧ a ∈ Y.fgPayload) ∧
        ∃ b, (∃ Y ∈ st₂.tree, st₂.Anc Y B' ∧ b ∈ Y.fgPayload) ∧ a.val = v ∧ FG.slashable a b := by
  obtain ⟨c₁, h₁, -, ha₁⟩ := held_chain_with hu hR₁ hB
  obtain ⟨c₂, h₂, -, ha₂⟩ := held_chain_with hu hR₂ hB'
  have h0 : 1 ≤ (st₁.σ B.root).hj := by
    by_contra h0
    exact hne ((FG.chain_invariants P.fg _ _ h₁).2.2.2.1 (by omega) |>.trans
      ((FG.chain_invariants P.fg _ _ h₂).2.2.2.1 (by omega)).symm)
  obtain ⟨Q₁, hQ₁, hv₁⟩ := (justification_quorum P.fg h₁).2 h0
  obtain ⟨Q₂, hQ₂, hv₂⟩ := (justification_quorum P.fg h₂).2 (he ▸ h0)
  refine ⟨Q₁ ∩ Q₂, (FG.quorum_intersection P.fg Q₁ Q₂ hQ₁ hQ₂).1, fun v hv => ?_⟩
  obtain ⟨a, ha, rfl, hah, haT, hat⟩ := hv₁ v (Finset.mem_inter.1 hv).1
  obtain ⟨b, hb, hvb, hbh, hbT, hbt⟩ := hv₂ a.val (Finset.mem_inter.1 hv).2
  exact ⟨a, ha₁ a ha, b, ha₂ b hb, rfl,
    ⟨hvb.symm, Or.inr (Or.inr ⟨by rw [hah, hbh, he], hat, hbt, by rw [haT, hbT]; exact hne⟩)⟩⟩

/-- **A finalization off a higher chain crosses it** (G1.2 at chain level). A block `F`
finalized by the state of a held `X` of one reachable store, whose root is not the root of any
block at or below a held `W` of another reachable store with a state height above the finalized
height, gives at least `2q − n` validators, each with a slashable pair among the attestations on
blocks at or below `X` and at or below `W`. -/
theorem finalized_crossing_with {st₁ st₂ : Store P ACP}
    (hu : FinalitySpec u) (hR₁ : ReachableWith u acp₀ st₁)
    (hR₂ : ReachableWith u acp₀ st₂) {X F W : NodeBlock P ACP} (hX : X ∈ st₁.tree)
    (hFr : F.root = (st₁.σ X.root).F) (hW : W ∈ st₂.tree)
    (hlt : (st₁.σ X.root).hF < (st₂.σ W.root).h)
    (hoff : ∀ Y ∈ st₂.tree, st₂.Anc Y W → Y.root ≠ F.root) :
    ∃ S : Finset (Fin P.n), 2 * P.fg.q - P.n ≤ S.card ∧ ∀ v ∈ S,
      ∃ a, (∃ Y ∈ st₁.tree, st₁.Anc Y X ∧ a ∈ Y.fgPayload) ∧
        ∃ b, (∃ Y ∈ st₂.tree, st₂.Anc Y W ∧ b ∈ Y.fgPayload) ∧ a.val = v ∧ FG.slashable a b := by
  obtain ⟨c₁, hσ₁, -, ha₁⟩ := held_chain_with hu hR₁ hX
  obtain ⟨c₂, hσ₂, hc₂, ha₂⟩ := held_chain_with hu hR₂ hW
  have hnot : (st₁.σ X.root).F ∉ P.fg.roots (c₂.map Block.fgView) := by
    intro hmem
    rw [← hFr] at hmem
    obtain ⟨Y, hY, hYF⟩ : ∃ Y ∈ P.genesisBlock acp₀ :: c₂, Y.root = F.root := by
      simpa [FG.FGParams.roots, Block.fgView, Params.fg, Params.genesisBlock, eq_comm] using hmem
    exact hoff Y (hc₂ Y hY).1 (hc₂ Y hY).2 hYF
  have hF1 : 1 ≤ (st₁.σ X.root).hF := by
    by_contra h0
    apply hnot
    rw [(FG.chain_invariants P.fg _ _ hσ₁).2.2.2.2.1 (by omega)]
    exact List.mem_cons_self
  obtain ⟨S, hS, hSv⟩ := P.fg.finalization_meets_crossing hσ₁ hσ₂ hF1 hlt hnot
  refine ⟨S, hS, fun v hv => ?_⟩
  obtain ⟨a, ha, b, hb, hav, hab⟩ := hSv v hv
  exact ⟨a, ha₁ a ha, b, ha₂ b hb, hav, hab⟩


/-- A set of at least `k` validators meets every set whose complement has fewer than `k`
members. -/
private theorem exists_mem_of_ncard_compl_lt {n k : Nat} {S : Finset (Fin n)} {V : Set (Fin n)}
    (hS : k ≤ S.card) (hV : Vᶜ.ncard < k) : ∃ v ∈ S, v ∈ V := by
  by_contra! h
  have := Set.ncard_le_ncard (s := (S : Set (Fin n))) (t := Vᶜ) h
  rw [Set.ncard_coe_finset] at this
  omega


/-- **Equal justified heights agree** (G1.1, G0.5 at the stores). Two justification quorums at
one height with different `J` meet in `2q − n` validators with E2 pairs, one of them in `V`. -/
theorem J_eq_of_hj_eq_of_safe_with {st₁ st₂ : Store P ACP}
    (hu : FinalitySpec u) (hR₁ : ReachableWith u acp₀ st₁)
    (hR₂ : ReachableWith u acp₀ st₂) {V : Set (Fin P.n)} (hV : Vᶜ.ncard < 2 * P.fg.q - P.n)
    -- Safety: attestations on held blocks of `st₁` and `st₂` with a signer in `V` are not
    -- slashable.
    (hsafe : ∀ a b, (∃ Y ∈ st₁.tree, a ∈ Y.fgPayload) → (∃ Y ∈ st₂.tree, b ∈ Y.fgPayload) →
      a.val ∈ V → ¬ FG.slashable a b)
    {B B' : NodeBlock P ACP} (hB : B ∈ st₁.tree) (hB' : B' ∈ st₂.tree)
    (he : (st₁.σ B.root).hj = (st₂.σ B'.root).hj) :
    (st₁.σ B.root).J = (st₂.σ B'.root).J := by
  by_contra hne
  obtain ⟨W, hW, hw⟩ := justified_crossing_with hu hR₁ hR₂ hB hB' he hne
  obtain ⟨v, hvW, hv⟩ := exists_mem_of_ncard_compl_lt hW hV
  obtain ⟨a, ⟨Y, hY, -, ha⟩, b, ⟨Y', hY', -, hb⟩, rfl, hab⟩ := hw v hvW
  exact hsafe a b ⟨Y, hY, ha⟩ ⟨Y', hY', hb⟩ hv hab

/-- **G1.2 at the stores.** A block `F` finalized by the state of a held `X` of `st₁` is a store
ancestor of every held `W` of `st₂` whose state height exceeds the finalized height: otherwise
`F` is not on `W`'s chain (roots are injective on the coherent `U`), and the finality and
crossing quorums meet in `2q − n` validators with slashable pairs, one of them in `V`. -/
theorem finalized_anc_of_safe_with {st₁ st₂ : Store P ACP}
    (hu : FinalitySpec u) (hR₁ : ReachableWith u acp₀ st₁)
    (hR₂ : ReachableWith u acp₀ st₂) {U : Set (NodeBlock P ACP)} (hU : Coherent U)
    (hsub₁ : st₁.tree ⊆ U) (hsub₂ : st₂.tree ⊆ U) {V : Set (Fin P.n)}
    (hV : Vᶜ.ncard < 2 * P.fg.q - P.n)
    -- Safety: attestations on held blocks of `st₁` and `st₂` with a signer in `V` are not
    -- slashable.
    (hsafe : ∀ a b, (∃ Y ∈ st₁.tree, a ∈ Y.fgPayload) → (∃ Y ∈ st₂.tree, b ∈ Y.fgPayload) →
      a.val ∈ V → ¬ FG.slashable a b)
    {X F W : NodeBlock P ACP} (hX : X ∈ st₁.tree) (hF : F ∈ st₁.tree)
    (hFr : F.root = (st₁.σ X.root).F) (hW : W ∈ st₂.tree)
    (hlt : (st₁.σ X.root).hF < (st₂.σ W.root).h) : st₂.Anc F W := by
  by_contra hn
  obtain ⟨S, hS, hw⟩ := finalized_crossing_with hu hR₁ hR₂ hX hFr hW hlt fun Y hY hYW hYr =>
    hn (hU.1 (hsub₂ hY) (hsub₁ hF) hYr ▸ hYW)
  obtain ⟨v, hvS, hv⟩ := exists_mem_of_ncard_compl_lt hS hV
  obtain ⟨a, ⟨Y, hY, -, ha⟩, b, ⟨Y', hY', -, hb⟩, rfl, hab⟩ := hw v hvS
  exact hsafe a b ⟨Y, hY, ha⟩ ⟨Y', hY', hb⟩ hv hab

/-- **`Σ.F` below every block of state height `≥ h_max`** (G1.2 with `h_F ≤ h_j < h ≤ h_max`
on the chain of the block whose state finalizes `Σ.F`). -/
theorem F_anc_of_hmax_le_of_safe_with {st₁ st₂ : Store P ACP}
    (hu : FinalitySpec u) (hR₁ : ReachableWith u acp₀ st₁)
    (hR₂ : ReachableWith u acp₀ st₂) {U : Set (NodeBlock P ACP)} (hU : Coherent U)
    (hsub₁ : st₁.tree ⊆ U) (hsub₂ : st₂.tree ⊆ U) {V : Set (Fin P.n)}
    (hV : Vᶜ.ncard < 2 * P.fg.q - P.n)
    -- Safety: attestations on held blocks of `st₁` and `st₂` with a signer in `V` are not
    -- slashable.
    (hsafe : ∀ a b, (∃ Y ∈ st₁.tree, a ∈ Y.fgPayload) → (∃ Y ∈ st₂.tree, b ∈ Y.fgPayload) →
      a.val ∈ V → ¬ FG.slashable a b)
    {B : NodeBlock P ACP} (hB : B ∈ st₂.tree) (hle : st₁.hmax ≤ (st₂.σ B.root).h) :
    st₂.Anc st₁.F B := by
  obtain ⟨hF, -, -, -, hge, -, X, hX, hXF⟩ := cache_invariants_with hu hR₁
  obtain ⟨c, -, -, -, hc⟩ := chain_state_of_chain_with hu hR₁ X hX
  have hinv := FG.chain_invariants _ _ _ hc
  have hXh := hge X hX
  have h1 := hinv.2.1
  have h2 := hinv.2.2.1
  exact finalized_anc_of_safe_with hu hR₁ hR₂ hU hsub₁ hsub₂ hV hsafe hX hF hXF.symm hB (by omega)


/-- Along one block, the finalized pair and the pending pairs of the new state are old ones
(pending, or the old finalized pair) or the old height's entry pair. -/
private theorem step_pairs {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n} {B : FG.FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') (Q : Nat × Nat → Prop)
    (hp : ∀ p ∈ σ.pending, Q p) (hF : Q (σ.hF, σ.F)) (hE : Q (σ.h, σ.Th)) :
    (∀ p ∈ σ'.pending, Q p) ∧ Q (σ'.hF, σ'.F) := by
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he]
  dsimp only
  obtain ⟨F, hF', σ₁, rfl, hFc, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  have hpend : ∀ r ∈ σ.pending.filter (fun p => hF' < p.1), Q r :=
    fun r hr => hp r (List.mem_of_mem_filter hr)
  have hF₁ : Q (hF', F) := by
    rcases hFc with ⟨rfl, rfl⟩ | ⟨hm, -⟩
    · exact hF
    · exact hp _ hm
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he']
  · refine ⟨fun r hr => ?_, hF₁⟩
    simp only [FG.ChainState.advance] at hr
    rcases List.mem_append.1 (List.mem_of_mem_drop hr) with hr | hr
    · exact hpend r hr
    · rw [List.mem_singleton] at hr
      subst hr
      exact hE
  · exact ⟨hpend, hF₁⟩
  · exact ⟨hpend, hF₁⟩

/-- **The finalized pair of a held block's state names the entry of its height** (or genesis):
the finalized pair is the old one or a pending pair, and every pending pair was appended at a
justification of the entry of the parent's height (G0.2 (d), (g) at the store). -/
theorem fin_pair_entry_with
    (hu : FinalitySpec u) (hr : ReachableWith u acp₀ st) {X : NodeBlock P ACP} (hX : X ∈ st.tree) :
    (st.σ X.root).F = P.genesisRoot ∨
      ∃ W ∈ st.tree, W.root = (st.σ X.root).F ∧ (st.σ W.root).h = (st.σ X.root).hF := by
  let Q : Nat × Nat → Prop := fun p =>
    p.2 = P.genesisRoot ∨ ∃ W ∈ st.tree, W.root = p.2 ∧ (st.σ W.root).h = p.1
  suffices key : (∀ p ∈ (st.σ X.root).pending, Q p) ∧ Q ((st.σ X.root).hF, (st.σ X.root).F) from
    key.2
  have hA := (accepted_tree_with hu hr).2.2.2 X hX
  clear hX
  induction hA with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis_with hu hr]
    exact ⟨fun p hp => by simp [FG.ChainState.init] at hp, Or.inl rfl⟩
  | tail _ hYW ih =>
    obtain ⟨-, -, -, ht⟩ := step_σ_with hu hr hYW.2.1 hYW.2.2
    obtain ⟨⟨E, hE, hEr, -, hEh, -⟩, -⟩ :=
      entry_state_of_source_with hu hr _ hYW.1
    exact step_pairs ht Q ih.1 ih.2 (Or.inr ⟨E, hE, hEr, hEh⟩)


/-- `h_j < h_max` in a reachable store. -/
theorem hj_lt_hmax_of_reachable_with {st : Store P ACP}
    (hu : FinalitySpec u) (hR : ReachableWith u acp₀ st) :
    st.hj < st.hmax := by
  obtain ⟨-, -, -, ⟨Bj, hBj, -, hBjhj⟩, hge, -, -⟩ := cache_invariants_with hu hR
  exact hBjhj ▸ (hj_lt_h_with hu hR hBj).trans_le (hge Bj hBj)

/-- **Equal cached `h_j` give equal `Σ.J`.** -/
theorem J_eq_of_cache_hj_eq_of_safe_with {st₁ st₂ : Store P ACP}
    (hu : FinalitySpec u) (hR₁ : ReachableWith u acp₀ st₁)
    (hR₂ : ReachableWith u acp₀ st₂) {U : Set (NodeBlock P ACP)} (hU : Coherent U)
    (hsub₁ : st₁.tree ⊆ U) (hsub₂ : st₂.tree ⊆ U) {V : Set (Fin P.n)}
    (hV : Vᶜ.ncard < 2 * P.fg.q - P.n)
    -- Safety: attestations on held blocks of `st₁` and `st₂` with a signer in `V` are not
    -- slashable.
    (hsafe : ∀ a b, (∃ Y ∈ st₁.tree, a ∈ Y.fgPayload) → (∃ Y ∈ st₂.tree, b ∈ Y.fgPayload) →
      a.val ∈ V → ¬ FG.slashable a b)
    (he : st₁.hj = st₂.hj) : st₁.J = st₂.J := by
  obtain ⟨-, hJ₁, -, ⟨B₁, hB₁, hB₁J, hB₁hj⟩, -⟩ := cache_invariants_with hu hR₁
  obtain ⟨-, hJ₂, -, ⟨B₂, hB₂, hB₂J, hB₂hj⟩, -⟩ := cache_invariants_with hu hR₂
  have h := J_eq_of_hj_eq_of_safe_with hu hR₁ hR₂ hV hsafe hB₁ hB₂ (by omega)
  exact hU.1 (hsub₁ hJ₁) (hsub₂ hJ₂) (hB₁J.symm.trans (h.trans hB₂J))

/-- **`Σ.F` below every block of state height `> h_j`** (store-level G1.2). -/
theorem F_anc_of_hj_lt_of_safe_with {st₁ st₂ : Store P ACP}
    (hu : FinalitySpec u) (hR₁ : ReachableWith u acp₀ st₁)
    (hR₂ : ReachableWith u acp₀ st₂) {U : Set (NodeBlock P ACP)} (hU : Coherent U)
    (hsub₁ : st₁.tree ⊆ U) (hsub₂ : st₂.tree ⊆ U) {V : Set (Fin P.n)}
    (hV : Vᶜ.ncard < 2 * P.fg.q - P.n)
    -- Safety: attestations on held blocks of `st₁` and `st₂` with a signer in `V` are not
    -- slashable.
    (hsafe : ∀ a b, (∃ Y ∈ st₁.tree, a ∈ Y.fgPayload) → (∃ Y ∈ st₂.tree, b ∈ Y.fgPayload) →
      a.val ∈ V → ¬ FG.slashable a b)
    {B : NodeBlock P ACP} (hB : B ∈ st₂.tree) (hlt : st₁.hj < (st₂.σ B.root).h) :
    st₂.Anc st₁.F B := by
  have hcoh : Coherent st₁.tree := hU.mono hsub₁
  have hg := genesis_mem_with hu hR₁
  obtain ⟨hFm, hJm, hFJ, ⟨Bj, hBj, hBjJ, hBjhj⟩, -, -, ⟨Bf, hBf, hBfF⟩⟩ :=
    cache_invariants_with hu hR₁
  have hgF : st₁.Anc (P.genesisBlock acp₀) st₁.F :=
    (accepted_tree_with hu hR₁).2.2.2 _ hFm
  have hgen : st₁.F.root = P.genesisRoot → st₂.Anc st₁.F B := fun he => by
    rw [hcoh.1 hFm hg he]
    exact (accepted_tree_with hu hR₂).2.2.2 B hB
  rcases fin_pair_entry_with hu hR₁ hBf with he | ⟨W, hW, hWr, hWh⟩
  · exact hgen (hBfF.symm.trans he)
  obtain rfl : W = st₁.F := hcoh.1 hW hFm (hWr.trans hBfF)
  obtain ⟨E, hE, hEr, -, hcase⟩ := J_entry_with hu hR₁ hBj
  obtain rfl : E = st₁.J := hcoh.1 hE hJm (hEr.trans hBjJ)
  rcases hcase with hEg | ⟨hEh, -⟩
  · rw [hEg] at hFJ
    exact hgen (congrArg Block.root (Anc.antisymm hcoh hFJ hgF))
  have h₁ := h_le_of_store_anc_with hu hR₁ hFJ
  exact finalized_anc_of_safe_with hu hR₁ hR₂ hU hsub₁ hsub₂ hV hsafe hBf hFm
    hBfF.symm hB (by omega)


end Held

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

theorem updateFinality'_eq_G :
    updateFinality' (P := P) (ACP := ACP) =
      updateFinalityG (fun st X => st.HasViableDescendant' X) := by
  funext st σ
  rw [updateFinality'_eq]
  rfl

/-- The shadow finality update has the stock shape. -/
theorem finalitySpec_updateFinality' : FinalitySpec (P := P) (ACP := ACP) updateFinality' :=
  updateFinality'_eq_G ▸ finalitySpec_updateFinalityG _

theorem onBlock'_eq_onBlockWith (st : Store P ACP) (B : NodeBlock P ACP) :
    st.onBlock' B = st.onBlockWith updateFinality' B := by
  rw [onBlock'_eq]
  rfl

/-- A shadow-reachable store is reached with the finality update `updateFinality'`. -/
theorem Reachable'.reachableWith {acp₀ : ACP} {st : Store P ACP} (h : st.Reachable' acp₀) :
    ReachableWith updateFinality' acp₀ st := by
  have h' : Relation.ReflTransGen Step' (init acp₀) st := by rw [← reachable'_eq]; exact h
  clear h
  induction h' with
  | refl => exact .refl
  | tail _ hs ih =>
    refine ih.tail ?_
    rcases (step'_iff _ _).1 hs with ⟨B, hB⟩ | ⟨a, ha⟩
    · exact Or.inl ⟨B, (onBlock'_eq_onBlockWith _ B) ▸ hB⟩
    · exact Or.inr ⟨a, ha⟩

/-- **The shadow cache invariant**: every shadow-reachable store satisfies `CacheGood`; the
`_with` lemmas apply with `finalitySpec_updateFinality'` and `Reachable'.reachableWith`. -/
theorem Reachable'.good {acp₀ : ACP} {st : Store P ACP} (h : st.Reachable' acp₀) :
    CacheGood acp₀ st :=
  h.reachableWith.good finalitySpec_updateFinality'

/-- `cache_invariants` over the shadow `Reachable'`. -/
theorem cache_invariants' {acp₀ : ACP} {st : Store P ACP} (h : st.Reachable' acp₀) :
    st.F ∈ st.tree ∧ st.J ∈ st.tree ∧ st.Anc st.F st.J ∧
      (∃ B ∈ st.tree, (st.σ B.root).J = st.J.root ∧ (st.σ B.root).hj = st.hj) ∧
      (∀ B ∈ st.tree, (st.σ B.root).h ≤ st.hmax) ∧
      (∃ B ∈ st.tree, (st.σ B.root).h = st.hmax) ∧
      ∃ B ∈ st.tree, (st.σ B.root).F = st.F.root :=
  cache_invariants_with finalitySpec_updateFinality' h.reachableWith

end Consensus.Goldilocks.Store

end
