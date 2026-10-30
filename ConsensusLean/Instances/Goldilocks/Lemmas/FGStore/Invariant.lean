module
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Tree
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Entry
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Handlers

public section

/-! # Goldilocks FG store: the reachable-state invariant (G0.1, F.2, G0.3, entry states)

One invariant of the FG states that the handlers reach, by induction over the steps: the tree
is kept by root, finite, contains genesis and is closed under parents with increasing slots;
every accepted block has a chain in the tree whose fold is its state (G0.1), which places the
entry, justification and finalization of its state on its chain; and the caches name accepted
blocks of accepted states (G0.3). The statements of part 1 about one reachable state follow. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type}

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

/-! ## The invariant -/

/-- The invariant of a reachable FG state. -/
private structure Good (acp₀ : ACP) (st : Store P ACP) : Prop where
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

private theorem good_init (acp₀ : ACP) : Good acp₀ (init (P := P) acp₀) := by
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

private theorem good_onAttestation {acp₀ : ACP} {st : Store P ACP} (h : Good acp₀ st)
    (a : FG.Att P.n) : Good acp₀ (st.onAttestation a) := by
  obtain ⟨atts, he⟩ := st.onAttestation_eq a
  rw [he]
  exact ⟨h.root, h.genesis, h.σ_genesis, h.finite, h.step, h.parent_none, h.chain, h.F_mem,
    h.J_mem, h.F_J, h.J_just, h.hmax_ge, h.hmax_eq, h.F_fin⟩

private theorem good_onBlock {acp₀ : ACP} {st st' : Store P ACP} (h : Good acp₀ st)
    {B : NodeBlock P ACP} (hB : st.onBlock B = some st') : Good acp₀ st' := by
  obtain ⟨pr, σ', hpar, hnew, hpr, -, hσ', rfl⟩ := onBlock_eq_some hB
  obtain ⟨hb, hσ, -, hm, hJ, hF⟩ := updateFinality_spec { st with
    blocks := Function.update st.blocks B.root (some B),
    σ := Function.update st.σ B.root σ' } σ'
  obtain ⟨atts, he⟩ := addAtts_eq (updateFinality { st with
    blocks := Function.update st.blocks B.root (some B),
    σ := Function.update st.σ B.root σ' } σ') B.fgPayload
  rw [he]
  generalize hs : ({ (updateFinality { st with
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

private theorem good {acp₀ : ACP} {st : Store P ACP} (h : st.Reachable acp₀) : Good acp₀ st := by
  induction h with
  | refl => exact good_init acp₀
  | tail _ hs ih =>
    rcases hs with ⟨B, hB⟩ | ⟨a, rfl⟩
    · exact good_onBlock ih hB
    · exact good_onAttestation ih a

/-! ## Consequences on one reachable state -/

/-- Every accepted block's state is at its slot. -/
private theorem Good.slot {acp₀ : ACP} {st : Store P ACP} (h : Good acp₀ st) {B : NodeBlock P ACP}
    (hB : B ∈ st.tree) : (st.σ B.root).s = B.slot := by
  rcases hp : B.parent with _ | pr
  · rw [h.parent_none B hB hp]
    change (st.σ P.genesisRoot).s = 0
    rw [h.σ_genesis]
    rfl
  · obtain ⟨X, -, -, ht⟩ := h.step B hB pr hp
    exact (P.fg.stateTransition_L_s ht).2.1

/-- The fold along a chain of the tree linked from genesis is the state of its last block. -/
private theorem Good.fold {acp₀ : ACP} {st : Store P ACP} (h : Good acp₀ st)
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
private theorem Good.anc {acp₀ : ACP} {st : Store P ACP} (h : Good acp₀ st)
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

variable (P ACP)

/-- A held root names the block with that root. -/
theorem Reachable.blocks_root {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (h : st.Reachable acp₀) {r : Nat} {X : NodeBlock P ACP} (hX : st.blocks r = some X) :
    X.root = r :=
  (good h).root r X hX

/-- **G0.1 (store).** -/
theorem chain_state_of_chain : ChainStateOfChain P ACP := by
  intro acp₀ st hr B hB
  have h := good hr
  obtain ⟨c, hc, hl, rfl⟩ := h.chain B hB
  refine ⟨c, hc, hl, ?_, h.fold hc hl⟩
  rcases hc' : c.getLast? with _ | X
  · exact Or.inl ⟨List.getLast?_eq_none_iff.1 hc', rfl⟩
  · exact Or.inr rfl

/-- **F.2 at the store, the accepted tree.** -/
theorem accepted_tree : AcceptedTree P ACP := by
  intro acp₀ st hr
  have h := good hr
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

/-- **F.2 at the store, the tree only grows.** -/
theorem tree_grows : TreeGrows P ACP := by
  intro acp₀ st _
  refine ⟨fun B st' hB => ?_, fun a => ?_⟩
  · obtain ⟨pr, σ', -, hnew, -, -, -, rfl⟩ := onBlock_eq_some hB
    obtain ⟨atts, he⟩ := addAtts_eq (updateFinality { st with
      blocks := Function.update st.blocks B.root (some B),
      σ := Function.update st.σ B.root σ' } σ') B.fgPayload
    rw [he]
    exact tree_insert hnew (updateFinality_spec _ _).1
  · obtain ⟨atts, he⟩ := st.onAttestation_eq a
    rw [he]
    rfl

/-- **G0.3.** -/
theorem cache_invariants : CacheInvariants P ACP := by
  intro acp₀ st hr
  have h := good hr
  exact ⟨h.F_mem, h.J_mem, h.F_J, h.J_just, h.hmax_ge, h.hmax_eq, h.F_fin⟩

/-- **G0.2 (c), (h) at the store.** -/
theorem entry_state_of_source : EntryStateOfSource P ACP := by
  intro acp₀ st hr B hB
  have h := good hr
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

end Consensus.Goldilocks.Store

end
