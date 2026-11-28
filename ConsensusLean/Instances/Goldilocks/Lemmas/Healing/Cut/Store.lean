module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Entries
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Transition
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.StepBits
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Live
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.CutSteps

public section

/-! # Goldilocks Healing, HR.1: facts of one reachable FG store

The store facts that HR.1 reads at the honest nodes of a run:

* an unheld root has the initial chain state, and so does genesis (`σ_of_blocks_none`,
  `σ_genesis`); an accepted block's state is the transition of its parent's (`step_σ`);
* the height pair `(h, T)` that `fg_attest` signs names a held block `E` with root `T` whose state
  has height `h` (`exists_entry_of_createAtt`), so `h ≤ Σ.h_max`;
* two reachable stores whose trees lie in a set with injective roots give a common block the same
  state (`σ_eq_of_mem`);
* **G0.2 (f)**: a chain leaves a height only with a progress quorum of attestations of that height
  on it, so with fewer than `q` faulty validators every height below a block's state height has an
  honest attestation on the block's chain (`exists_honest_att_of_lt`);
* along the store's ancestry the state height does not decrease (`h_le_of_store_anc`), and while
  it stays the entry stays (`Th_eq_of_anc`, G0.2 (i)) and so does its slot (`ThSlot_eq_of_anc`);
  a held block's entry slot is at most its slot (`ThSlot_le_slot`). -/

namespace Consensus.Goldilocks.Healing

open FG


/-! ## A reachable store -/

namespace Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}

private theorem mem_tree_update {st' : Store P ACP} {B Y : NodeBlock P ACP}
    (hb : st'.blocks = Function.update st.blocks B.root (some B)) :
    Y ∈ st'.tree ↔ Y = B ∨ (Y.root ≠ B.root ∧ Y ∈ st.tree) := by
  change st'.blocks Y.root = some Y ↔ _
  rw [hb, Function.update_apply]
  split_ifs with h
  · exact ⟨fun e => Or.inl (Option.some.inj e).symm, fun e => by
      rcases e with rfl | ⟨h', -⟩
      · rfl
      · exact absurd h h'⟩
  · exact ⟨fun e => Or.inr ⟨h, e⟩, fun e => by
      rcases e with rfl | ⟨-, e⟩
      · exact absurd rfl h
      · exact e⟩

/-- An unheld root has the initial chain state. -/
theorem σ_of_blocks_none (hr : st.Reachable acp₀) {r : Nat} (hn : st.blocks r = none) :
    st.σ r = ChainState.init P.fg := by
  induction hr generalizing r with
  | refl => rfl
  | tail _ hs ih =>
    rcases hs with ⟨B, hB⟩ | ⟨a, rfl⟩
    · obtain ⟨-, σ', -, -, -, -, hb, hσ, -⟩ := Goldilocks.Store.onBlock_fields hB
      have hne : r ≠ B.root := fun e => by simp [hb, e] at hn
      rw [hb, Function.update_of_ne hne] at hn
      rw [hσ, Function.update_of_ne hne]
      exact ih hn
    · obtain ⟨h1, h2, -⟩ := Goldilocks.Store.onAttestation_fields _ a
      rw [h1] at hn
      rw [h2]
      exact ih hn

/-- Genesis is held. -/
theorem genesis_mem (hr : st.Reachable acp₀) : P.genesisBlock acp₀ ∈ st.tree :=
  (Goldilocks.Store.accepted_tree P ACP acp₀ st hr).2.2.1

/-- Genesis has the initial chain state. -/
theorem σ_genesis (hr : st.Reachable acp₀) : st.σ P.genesisRoot = ChainState.init P.fg := by
  induction hr with
  | refl => rfl
  | tail hr hs ih =>
    rcases hs with ⟨B, hB⟩ | ⟨a, rfl⟩
    · obtain ⟨-, σ', hn, -, -, -, -, hσ, -⟩ := Goldilocks.Store.onBlock_fields hB
      have hg : _ = some _ := genesis_mem hr
      have hne : P.genesisRoot ≠ B.root := fun e => by
        rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, e, hn] at hg
        cases hg
      rw [hσ, Function.update_of_ne hne]
      exact ih
    · rw [(Goldilocks.Store.onAttestation_fields _ a).2.1]
      exact ih

/-- An accepted block's state is the transition of its parent's, and the parent is held. -/
theorem step_σ (hr : st.Reachable acp₀) {W : NodeBlock P ACP} (hW : W ∈ st.tree) {pr : Nat}
    (hp : W.parent = some pr) :
    ∃ X ∈ st.tree, X.root = pr ∧
      P.fg.stateTransition (st.σ pr) W.fgView = some (st.σ W.root) := by
  induction hr with
  | refl =>
    change (if W.root = P.genesisRoot then some (P.genesisBlock acp₀) else none) = some W at hW
    split_ifs at hW
    cases hW
    cases hp
  | @tail st st' hr hs ih =>
    rcases hs with ⟨B, hB⟩ | ⟨a, rfl⟩
    · obtain ⟨pr', σ', hn, hpr, hp', ht, hb, hσ, -⟩ := Goldilocks.Store.onBlock_fields hB
      obtain ⟨X, hX⟩ := Option.isSome_iff_exists.1 hpr
      have hXr : X.root = pr' := Goldilocks.Store.Reachable.blocks_root hr hX
      have hXs : X ∈ st.tree := by change st.blocks X.root = some X; rw [hXr]; exact hX
      have hXB : X.root ≠ B.root := fun e => by
        have : st.blocks X.root = some X := hXs
        rw [e, hn] at this
        cases this
      have hXt : X ∈ st'.tree := (mem_tree_update hb).2 (Or.inr ⟨hXB, hXs⟩)
      rcases (mem_tree_update hb).1 hW with rfl | ⟨hWB, hW⟩
      · rw [hp] at hp'
        cases hp'
        refine ⟨X, hXt, hXr, ?_⟩
        rw [hσ, Function.update_self, Function.update_of_ne (hXr ▸ hXB)]
        exact ht
      · obtain ⟨Y, hY, hYr, hYt⟩ := ih hW
        have hYB : Y.root ≠ B.root := fun e => by
          have : st.blocks Y.root = some Y := hY
          rw [e, hn] at this
          cases this
        refine ⟨Y, (mem_tree_update hb).2 (Or.inr ⟨hYB, hY⟩), hYr, ?_⟩
        rw [hσ, Function.update_of_ne hWB, Function.update_of_ne (hYr ▸ hYB)]
        exact hYt
    · obtain ⟨h1, h2, -⟩ := Goldilocks.Store.onAttestation_fields st a
      have hW' : W ∈ st.tree := by
        change st.blocks W.root = some W
        rw [← h1]
        exact hW
      obtain ⟨X, hX, hXr, hXt⟩ := ih hW'
      refine ⟨X, ?_, hXr, by rw [h2]; exact hXt⟩
      change (st.onAttestation a).blocks X.root = some X
      rw [h1]
      exact hX

/-- A report from a held source preserves its entry ancestor, self-entry and
source-height witnesses, not only the height pair that is signed. -/
theorem entry_of_createAtt (hr : st.Reachable acp₀) {Λ Λ' : FG.Record} {v : Fin P.n}
    {src : NodeBlock P ACP} {a : Att P.n} (hsrc : src ∈ st.tree)
    (h : Λ.createAtt v (st.σ (st.σ src.root).Th) = some (a, Λ')) :
    ∃ E ∈ st.tree, E.root = a.T ∧ st.Anc E src ∧
      (st.σ src.root).Th = E.root ∧ (st.σ E.root).Th = E.root ∧
      (st.σ E.root).h = (st.σ src.root).h ∧ (st.σ src.root).h = a.h := by
  obtain ⟨hh, hT⟩ := createAtt_eq h
  obtain ⟨⟨E, hE, hEr, hEC, hEh, hET⟩, _⟩ :=
    Goldilocks.Store.entry_state_of_source P ACP acp₀ st hr src hsrc
  refine ⟨E, hE, ?_, hEC, hEr.symm, hET.trans hEr.symm, hEh, ?_⟩
  · rw [hT, ← hEr, hET]
    exact hEr
  · rw [hh, ← hEr, hEh]

/-- **The height pair that `fg_attest` signs names a held block**: its root is the pair's
`T` and its state has the pair's height. -/
theorem exists_entry_of_createAtt (hr : st.Reachable acp₀) {Λ Λ' : FG.Record} {v : Fin P.n}
    {src : NodeBlock P ACP} {a : Att P.n}
    (h : Λ.createAtt v (st.σ (st.σ src.root).Th) = some (a, Λ')) :
    ∃ E ∈ st.tree, E.root = a.T ∧ (st.σ E.root).h = a.h := by
  obtain ⟨hh, hT⟩ := createAtt_eq h
  rcases hs : st.blocks src.root with _ | X
  · have hg : (st.σ src.root).Th = P.genesisRoot := by rw [σ_of_blocks_none hr hs]; rfl
    rw [hg, σ_genesis hr] at hh hT
    refine ⟨_, genesis_mem hr, ?_, ?_⟩
    · rw [hT]; rfl
    · rw [hh]; exact congrArg ChainState.h (σ_genesis hr)
  · have hXr : X.root = src.root := Goldilocks.Store.Reachable.blocks_root hr hs
    have hX : X ∈ st.tree := by change st.blocks X.root = some X; rw [hXr]; exact hs
    obtain ⟨⟨E, hE, hEr, -, hEh, hET⟩, -⟩ :=
      Goldilocks.Store.entry_state_of_source P ACP acp₀ st hr X hX
    rw [hXr] at hEr hEh hET
    refine ⟨E, hE, ?_, ?_⟩
    · rw [hT, ← hEr, hET]
      exact hEr
    · rw [hh, ← hEr]

/-- The height pair that `fg_attest` signs is at most `Σ.h_max`. -/
theorem createAtt_h_le (hr : st.Reachable acp₀) {Λ Λ' : FG.Record} {v : Fin P.n}
    {src : NodeBlock P ACP} {a : Att P.n}
    (h : Λ.createAtt v (st.σ (st.σ src.root).Th) = some (a, Λ')) : a.h ≤ st.hmax := by
  obtain ⟨E, hE, -, hEh⟩ := exists_entry_of_createAtt hr h
  exact hEh ▸ (Goldilocks.Store.cache_invariants P ACP acp₀ st hr).2.2.2.2.1 E hE

/-- **One state per block across stores**: two reachable stores whose trees lie in a set with
injective roots give a block they both hold the same state. -/
theorem σ_eq_of_mem {st₁ st₂ : Store P ACP} (hr₁ : st₁.Reachable acp₀) (hr₂ : st₂.Reachable acp₀)
    {U : Set (NodeBlock P ACP)} (hU : Set.InjOn Block.root U) (h₁ : st₁.tree ⊆ U)
    (h₂ : st₂.tree ⊆ U) {B : NodeBlock P ACP} (hB₁ : B ∈ st₁.tree) (hB₂ : B ∈ st₂.tree) :
    st₁.σ B.root = st₂.σ B.root := by
  have hg := (Goldilocks.Store.accepted_tree P ACP acp₀ _ hr₁).2.2.2 B hB₁
  clear hB₁
  induction hg with
  | refl =>
    change st₁.σ P.genesisRoot = st₂.σ P.genesisRoot
    rw [σ_genesis hr₁, σ_genesis hr₂]
  | @tail W' W _ hpar ih =>
    obtain ⟨hW'₁, hW₁, hp⟩ := hpar
    obtain ⟨X, hX, hXr, ht₂⟩ := step_σ hr₂ hB₂ hp
    obtain rfl : X = W' := hU (h₂ hX) (h₁ hW'₁) hXr
    obtain ⟨-, -, -, ht₁⟩ := step_σ hr₁ hW₁ hp
    rw [ih hX] at ht₁
    exact Option.some.inj (ht₁.symm.trans ht₂)

/-- **G0.2 (f) at a store.** With fewer than `q` faulty validators, every height `h ≥ 1` below
the state height of a held block `X` has an honest attestation of height `h` on `X`'s chain
(a chain leaves a height only with a progress quorum of attestations of that height). -/
theorem exists_honest_att_of_lt (hr : st.Reachable acp₀) {H : Set (Fin P.n)}
    (hq : Hᶜ.ncard < P.fg.q) {X : NodeBlock P ACP} (hX : X ∈ st.tree) :
    ∀ h, 1 ≤ h → h < (st.σ X.root).h →
      ∃ Y, st.Anc Y X ∧ ∃ a ∈ Y.fgPayload, a.val ∈ H ∧ a.h = h := by
  suffices key : (∀ v ∈ (st.σ X.root).prog ∪ (st.σ X.root).target,
      ∃ Y, st.Anc Y X ∧ ∃ a ∈ Y.fgPayload, a.val = v ∧ a.h = (st.σ X.root).h) ∧
      ∀ h, 1 ≤ h → h < (st.σ X.root).h →
        ∃ Y, st.Anc Y X ∧ ∃ a ∈ Y.fgPayload, a.val ∈ H ∧ a.h = h from key.2
  have hg := (Goldilocks.Store.accepted_tree P ACP acp₀ _ hr).2.2.2 X hX
  clear hX
  induction hg with
  | refl =>
    change (∀ v ∈ (st.σ P.genesisRoot).prog ∪ (st.σ P.genesisRoot).target, _) ∧
      ∀ h, 1 ≤ h → h < (st.σ P.genesisRoot).h → _
    rw [σ_genesis hr]
    refine ⟨fun v hv => ?_, fun h h1 h2 => ?_⟩
    · rcases Finset.mem_union.1 hv with hv | hv <;> exact absurd hv (Finset.notMem_empty _)
    simp only [ChainState.init] at h2
    omega
  | @tail W' W _ hpar ih =>
    obtain ⟨hW'₁, hW₁, hp⟩ := hpar
    obtain ⟨-, -, -, ht⟩ := step_σ hr hW₁ hp
    have hanc : st.Anc W' W := Relation.ReflTransGen.single ⟨hW'₁, hW₁, hp⟩
    -- an old bit or a signer of `W`'s attestations at the old height
    have old : ∀ v, v ∈ (st.σ W'.root).prog ∪ (st.σ W'.root).target ∨
        (∃ a ∈ W.fgView.atts, a.val = v ∧ a.h = (st.σ W'.root).h) →
        ∃ Y, st.Anc Y W ∧ ∃ a ∈ Y.fgPayload, a.val = v ∧ a.h = (st.σ W'.root).h := by
      rintro v (hv | ⟨a, ha, hav, hah⟩)
      · obtain ⟨Y, hY, hYa⟩ := ih.1 v hv
        exact ⟨Y, hY.trans hanc, hYa⟩
      · exact ⟨W, .refl, a, ha, hav, hah⟩
    rcases stateTransition_bits ht with ⟨he, hbits⟩ | ⟨he, hnil, S, hS, hSv⟩
    · refine ⟨fun v hv => he ▸ old v (hbits v hv), fun h h1 h2 => ?_⟩
      obtain ⟨Y, hY, hYa⟩ := ih.2 h h1 (he ▸ h2)
      exact ⟨Y, hY.trans hanc, hYa⟩
    · obtain ⟨S, hS, hSv⟩ : ∃ S : Finset (Fin P.n), P.fg.q ≤ S.card ∧ ∀ v ∈ S,
          v ∈ (st.σ W'.root).prog ∪ (st.σ W'.root).target ∨
            ∃ a ∈ W.fgView.atts, a.val = v ∧ a.h = (st.σ W'.root).h := ⟨S, hS, hSv⟩
      refine ⟨fun v hv => ?_, fun h h1 h2 => ?_⟩
      · exact absurd hv (Finset.eq_empty_iff_forall_notMem.1 hnil v)
      rcases Nat.lt_succ_iff_lt_or_eq.1 (he ▸ h2) with h2 | rfl
      · obtain ⟨Y, hY, hYa⟩ := ih.2 h h1 h2
        exact ⟨Y, hY.trans hanc, hYa⟩
      · obtain ⟨v, hvS, hvH⟩ : ∃ v ∈ S, v ∈ H := by
          by_contra hc
          have : (↑S : Set (Fin P.n)) ⊆ Hᶜ := fun v hv h => hc ⟨v, hv, h⟩
          have := Set.ncard_le_ncard this (Set.toFinite _)
          rw [Set.ncard_coe_finset] at this
          omega
        obtain ⟨Y, hY, a, ha, rfl, hah⟩ := old v (hSv v hvS)
        exact ⟨Y, hY, a, ha, hvH, hah⟩

end Store

/-! ## Along the store's ancestry -/

section Anc

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}

/-- Along ancestry in a reachable store the state height does not decrease. -/
theorem h_le_of_store_anc (hr : st.Reachable acp₀) {A W : NodeBlock P ACP} (h : st.Anc A W) :
    (st.σ A.root).h ≤ (st.σ W.root).h := by
  induction h with
  | refl => exact le_rfl
  | tail _ hYW ih =>
    obtain ⟨-, -, -, ht⟩ := Store.step_σ hr hYW.2.1 hYW.2.2
    rcases stateTransition_bits ht with ⟨hh, -⟩ | ⟨hh, -⟩ <;> omega

/-- **Entry constancy** (G0.2 (i)): while the height stays along ancestry, the entry stays. -/
theorem Th_eq_of_anc (hr : st.Reachable acp₀) {A W : NodeBlock P ACP} (h : st.Anc A W)
    (hh : (st.σ W.root).h = (st.σ A.root).h) : (st.σ W.root).Th = (st.σ A.root).Th := by
  induction h with
  | refl => rfl
  | tail hAY hYW ih =>
    obtain ⟨-, -, -, ht⟩ := Store.step_σ hr hYW.2.1 hYW.2.2
    have h₁ := h_le_of_store_anc hr hAY
    rcases (Goldilocks.Store.step_fields ht).1 with ⟨he, hT⟩ | ⟨he, -⟩
    · rw [hT]; exact ih (by omega)
    · omega

/-- **Entry-slot constancy:** while the height stays along ancestry, the entry slot stays. -/
theorem ThSlot_eq_of_anc (hr : st.Reachable acp₀) {A W : NodeBlock P ACP} (h : st.Anc A W)
    (hh : (st.σ W.root).h = (st.σ A.root).h) :
    (st.σ W.root).ThSlot = (st.σ A.root).ThSlot := by
  induction h with
  | refl => rfl
  | @tail Y Y' hAY hYY' ih =>
    obtain ⟨-, hY', hp⟩ := hYY'
    obtain ⟨-, -, -, ht⟩ := Store.step_σ hr hY' hp
    have h₁ := h_le_of_store_anc hr hAY
    rcases P.fg.stateTransition_ThSlot ht with ⟨e, e', -⟩ | ⟨e, -, -⟩
    · rw [e']; exact ih (by rw [← e]; exact hh)
    · omega

/-- **The entry slot is at most the slot.** In a reachable store, a held `Z` has
`σ[Z].ThSlot ≤ Z.slot`. -/
theorem ThSlot_le_slot (hr : st.Reachable acp₀) {Z : NodeBlock P ACP} (hZ : Z ∈ st.tree) :
    (st.σ Z.root).ThSlot ≤ Z.slot := by
  obtain ⟨hcoh, -, hg⟩ := (Goldilocks.Store.accepted_tree P ACP acp₀ st hr).2
  induction hg Z hZ with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Store.σ_genesis hr]
    exact Nat.zero_le _
  | @tail Y Y' hGY hYY' ih =>
    obtain ⟨hY, hY', hp⟩ := hYY'
    obtain ⟨-, -, -, ht⟩ := Store.step_σ hr hY' hp
    have hsl : Y.slot < Y'.slot := hcoh.2 Y hY Y' hY' hp
    have := ih hY
    rcases P.fg.stateTransition_ThSlot ht with ⟨-, e, -⟩ | ⟨-, e, -⟩
    · rw [e]; omega
    · rw [e]; rfl

end Anc

end Consensus.Goldilocks.Healing

end
