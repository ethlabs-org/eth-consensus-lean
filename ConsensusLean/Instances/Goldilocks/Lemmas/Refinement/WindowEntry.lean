module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowUnanimous
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Live
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High

public section

/-! # Goldilocks Refinement: the entry is justified on the parent's chain (L5.4, WI-19)

Workbench `fg-liveness/r14-end-to-end`, s5 L5.4: the entry `(h, T)` is justified on the
canonical chain, and the predecessor is finalized if the height has its previous height justified.

* `Store.chain_states_of_anc`: the store bridge. For a held `X ⪯ W`, a chain `c` reaches
  `σ[X]` and `c ++ d` reaches `σ[W]`; every block of `d` is held, between `X` and `W`, has a
  slot at most `W.slot`, and the prefix of `c ++ d` that ends at it reaches its state.
* `Store.entry_justified_of_anc`: `FGParams.early_cross_chain_justifies` at the store: if `σ[X].h <
  σ[W].h` and `W.slot < σ[X].ThSlot + δt`, a held `D` with `X ⪯ D ⪯ W` justified the entry of
  `σ[X]`, and finalized the predecessor block if `σ[X]` has its previous height justified.
* `Store.chain_states_of_anc'`: the bridge with parent links: every earlier block of `d` is an
  ancestor of `B`, and the parent `Z` of `B` is held, `X ⪯ Z`, and the prefix before `B`
  reaches `σ[Z]`.
* `Store.theorem_F_of_anc`: `FGParams.theorem_F_chain` at the store: if `σ[X].h + 1 < σ[W].h`
  and every held `D ⪯ W` with parent `Z ⪰ X` at height `σ[X].h` or `σ[X].h + 1` has
  `D.slot < σ[Z].ThSlot + δt`, held `X ⪯ D₁ ⪯ D₂ ⪯ W` justify the two entries and `D₂`
  finalized the held block of root `σ[X].Th` at height `σ[X].h`.
* `Store.ThSlot_le_slot`, `Store.ThSlot_mono`: `σ[Z].ThSlot ≤ Z.slot`, and the entry slot grows
  along an ancestry. `Store.theorem_F_of_anc_slot`: `theorem_F_of_anc` with the timing premise
  `W.slot < σ[X].ThSlot + δt`.
* `Store.finalized_covers_of_window`: with held `X ⪯ W ⪯ B₃` as in the slot form, and `B₀`
  below the entry block of `σ[X]`, the block of root `σ[B₃].F` is held and `B₀ ⪯` it (the
  `CacheCoverage` premise shape); `finalized_covers_of_window'`: per-height timing;
  `theorem_F_of_anc''`, `finalized_covers_of_window''`: each crossing early or justifying.
  Helpers: `hF_mono`, `Th_eq_of_h_eq`,
  `fin_pair_self_entry_or_zero`, `self_entry_anc_finalized`.
* `window_justifies_or_parents_above_after'`: `window_justifies_or_parents_above_after` with
  `X ⪯ C` for every held `X` of root `T` in case (A).
* `window_justifies_or_parents_above_unanimous_entry`:
  `window_justifies_or_parents_above_unanimous''` with the same addition.
* `window_entry_justified_or_window` (L5.4): in case (A), every honest proposal of a slot `s` with
  `v + Δ ≤ t_s` and `s ≤ σ[X].ThSlot + δt` has an honest parent `Pr ⪰ X` on whose chain a block
  justified `(h, T)` (and finalized the predecessor if its previous height is justified), at every
  honest holder. The bound `s ≤ σ[X].ThSlot + δt` stays a premise: the window gives only `v + Δ ≤
  t_s`. -/

namespace Consensus.Goldilocks

namespace FG.FGParams

variable (gp : FGParams)

/-- `chainState_append` through a map. -/
theorem chainState_map_append_singleton {α : Type} (f : α → FGBlock gp.n) (c : List α)
    (B : α) : gp.chainState ((c ++ [B]).map f) =
      (gp.chainState (c.map f)).bind (gp.stateTransition · (f B)) := by
  rw [List.map_append, List.map_singleton, gp.chainState_append]


/-- `theorem_F_chain'` through a map: the two justifying blocks are images of blocks of `d`. -/
theorem theorem_F_map_chain' {α : Type} (f : α → FGBlock gp.n) {c d : List α}
    {σ τ : ChainState gp.n} (hc : gp.chainState (c.map f) = some σ)
    (hd : gp.chainState ((c ++ d).map f) = some τ) (hh : σ.h + 1 < τ.h)
    (hs : ∀ d₁ B d₂ ρ ρ', d = d₁ ++ B :: d₂ → gp.chainState ((c ++ d₁).map f) = some ρ →
      gp.chainState ((c ++ d₁ ++ [B]).map f) = some ρ' → (ρ.h = σ.h ∨ ρ.h = σ.h + 1) →
      ρ'.h = ρ.h + 1 → (f B).slot < ρ.ThSlot + gp.δt ∨ ρ'.hj = ρ.h) :
    ∃ d₁ B₁ d₂ B₂ d₃ σ₁ σ₂, d = d₁ ++ B₁ :: (d₂ ++ B₂ :: d₃) ∧
      gp.chainState ((c ++ d₁ ++ [B₁]).map f) = some σ₁ ∧
      σ₁.h = σ.h + 1 ∧ σ₁.hj = σ.h ∧ σ₁.J = σ.Th ∧
      gp.chainState ((c ++ (d₁ ++ B₁ :: d₂) ++ [B₂]).map f) = some σ₂ ∧
      σ₂.h = σ.h + 2 ∧ σ₂.hj = σ.h + 1 ∧ σ₂.J = σ₁.Th ∧
      σ₂.F = σ.Th ∧ σ₂.hF = σ.h := by
  rw [List.map_append] at hd
  obtain ⟨e₁, B₁, e₂, B₂, e₃, σ₁, σ₂, he, h1, h1h, h1j, h1J, h2, h2h, h2j, h2J, h2F, h2hF⟩ :=
    gp.theorem_F_chain' hc hd hh (by
      intro e₁ B e₂ ρ ρ' he hρ hρ' hρh
      obtain ⟨d₁, r, rfl, rfl, hr'⟩ := List.map_eq_append_iff.1 he
      obtain ⟨D, d₂, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.1 hr'
      exact hs d₁ D d₂ ρ ρ' rfl (by simpa [List.map_append] using hρ)
        (by simpa [List.map_append] using hρ') hρh)
  obtain ⟨d₁, r, rfl, rfl, hr₁⟩ := List.map_eq_append_iff.1 he
  obtain ⟨D₁, r', rfl, rfl, hr₂⟩ := List.map_eq_cons_iff.1 hr₁
  obtain ⟨d₂, r'', rfl, rfl, hr₃⟩ := List.map_eq_append_iff.1 hr₂
  obtain ⟨D₂, d₃, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.1 hr₃
  exact ⟨d₁, D₁, d₂, D₂, d₃, σ₁, σ₂, rfl, by simpa [List.map_append] using h1, h1h, h1j, h1J,
    by simpa [List.map_append] using h2, h2h, h2j, h2J, h2F, h2hF⟩

end FG.FGParams

namespace Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}


/-- **The store bridge with parent links.** `chain_states_of_anc`, and for every block `B` of
`d` (with `d = d₁ ++ B :: d₂`), every block of `d₁` is an ancestor of `B`, and the parent `Z` of
`B` (the last block of `d₁`, or `X`) is held, has `B.parent = some Z.root` and `X ⪯ Z`, and
`c ++ d₁` reaches `σ[Z]`. -/
theorem chain_states_of_anc' (hr : st.Reachable acp₀) {X W : NodeBlock P ACP}
    (hX : X ∈ st.tree) (hXW : st.Anc X W) :
    ∃ c d : List (NodeBlock P ACP),
      P.fg.chainState (c.map Block.fgView) = some (st.σ X.root) ∧
      P.fg.chainState ((c ++ d).map Block.fgView) = some (st.σ W.root) ∧
      ∀ d₁ B d₂, d = d₁ ++ B :: d₂ → B ∈ st.tree ∧ st.Anc X B ∧ st.Anc B W ∧
        B.slot ≤ W.slot ∧
        P.fg.chainState ((c ++ d₁ ++ [B]).map Block.fgView) = some (st.σ B.root) ∧
        (∀ Y ∈ d₁, st.Anc Y B) ∧
        ∃ Z ∈ st.tree, B.parent = some Z.root ∧ st.Anc X Z ∧
          P.fg.chainState ((c ++ d₁).map Block.fgView) = some (st.σ Z.root) := by
  obtain ⟨c, -, -, -, hc⟩ := chain_state_of_chain P ACP acp₀ st hr X hX
  refine ⟨c, ?_⟩
  induction hXW with
  | refl => exact ⟨[], hc, by rw [List.append_nil]; exact hc, fun d₁ B d₂ h => by simp at h⟩
  | @tail W W' hXW' hWW' ih =>
    obtain ⟨d, -, hd, hpre⟩ := ih
    obtain ⟨hW, hW', hp⟩ := hWW'
    obtain ⟨-, -, -, ht⟩ := Healing.Store.step_σ hr hW' hp
    have hsl : W.slot < W'.slot := (accepted_tree P ACP acp₀ st hr).2.1.2 W hW W' hW' hp
    have hd' : P.fg.chainState ((c ++ (d ++ [W'])).map Block.fgView) = some (st.σ W'.root) := by
      have e := P.fg.chainState_map_append_singleton Block.fgView (c ++ d) W'
      rw [hd] at e
      rw [← List.append_assoc]
      exact e.trans ht
    refine ⟨d ++ [W'], hc, hd', fun d₁ B d₂ he => ?_⟩
    rcases List.eq_nil_or_concat d₂ with rfl | ⟨d₂', z, rfl⟩
    · obtain ⟨rfl, hB⟩ := List.append_inj' he rfl
      obtain rfl : W' = B := List.singleton_inj.1 hB
      refine ⟨hW', hXW'.tail ⟨hW, hW', hp⟩, Relation.ReflTransGen.refl, le_rfl, ?_, ?_,
        W, hW, hp, hXW', hd⟩
      · rw [← List.append_assoc] at hd'; exact hd'
      · intro Y hY
        obtain ⟨e₁, e₂, rfl⟩ := List.append_of_mem hY
        exact (hpre e₁ Y e₂ rfl).2.2.1.tail ⟨hW, hW', hp⟩
    · have he' : d ++ [W'] = (d₁ ++ B :: d₂') ++ [z] := by simpa using he
      obtain ⟨rfl, -⟩ := List.append_inj' he' rfl
      obtain ⟨hB, hXB, hBW, hBs, hσ, hY, hZ⟩ := hpre d₁ B d₂' rfl
      exact ⟨hB, hXB, hBW.tail ⟨hW, hW', hp⟩, by omega, hσ, hY, hZ⟩


/-- **The entry slot is at most the slot.** In a reachable store, a held `Z` has
`σ[Z].ThSlot ≤ Z.slot`. -/
theorem ThSlot_le_slot (hr : st.Reachable acp₀) {Z : NodeBlock P ACP} (hZ : Z ∈ st.tree) :
    (st.σ Z.root).ThSlot ≤ Z.slot := by
  obtain ⟨hcoh, -, hg⟩ := (accepted_tree P ACP acp₀ st hr).2
  induction hg Z hZ with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Healing.Store.σ_genesis hr]
    exact Nat.zero_le _
  | @tail Y Y' hGY hYY' ih =>
    obtain ⟨hY, hY', hp⟩ := hYY'
    obtain ⟨-, -, -, ht⟩ := Healing.Store.step_σ hr hY' hp
    have hsl : Y.slot < Y'.slot := hcoh.2 Y hY Y' hY' hp
    have := ih hY
    rcases P.fg.stateTransition_ThSlot ht with ⟨-, e, -⟩ | ⟨-, e, -⟩
    · rw [e]; omega
    · rw [e]; rfl

/-- Along one block, the finalized pair and the pending pairs of the new state are old ones
(pending, or the old finalized pair) or the old height's entry pair (a copy of the private
`Healing.Store.step_pairs`). -/
private theorem fin_step_pairs {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n}
    {B : FG.FGBlock gp.n} (h : gp.stateTransition σ B = some σ') (Q : Nat × Nat → Prop)
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

/-- **The finalized pair is the initial one or a self-entry.** In a reachable store, a held `X`
has `σ[X].hF = 0`, or a held `W` has root `σ[X].F`, `σ[W].h = σ[X].hF` and `σ[W].Th = W.root`.
-/
theorem fin_pair_self_entry_or_zero (hr : st.Reachable acp₀) {X : NodeBlock P ACP}
    (hX : X ∈ st.tree) :
    (st.σ X.root).hF = 0 ∨ ∃ W ∈ st.tree, W.root = (st.σ X.root).F ∧
      (st.σ W.root).h = (st.σ X.root).hF ∧ (st.σ W.root).Th = W.root := by
  let Q : Nat × Nat → Prop := fun p => p.1 = 0 ∨ ∃ W ∈ st.tree,
    W.root = p.2 ∧ (st.σ W.root).h = p.1 ∧ (st.σ W.root).Th = W.root
  suffices key : (∀ p ∈ (st.σ X.root).pending, Q p) ∧ Q ((st.σ X.root).hF, (st.σ X.root).F) from
    key.2
  have hA := (accepted_tree P ACP acp₀ _ hr).2.2.2 X hX
  clear hX
  induction hA with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Healing.Store.σ_genesis hr]
    exact ⟨fun p hp => by simp [FG.ChainState.init] at hp, Or.inl rfl⟩
  | tail _ hYW ih =>
    obtain ⟨_, _, _, ht⟩ := Healing.Store.step_σ hr hYW.2.1 hYW.2.2
    obtain ⟨⟨E, hE, hEr, _, hEh, hET⟩, _⟩ := entry_state_of_source P ACP acp₀ _ hr _ hYW.1
    exact fin_step_pairs ht Q ih.1 ih.2 (Or.inr ⟨E, hE, hEr, hEh, hET.trans hEr.symm⟩)

/-- **The finalized height grows along an ancestry.** In a reachable store, for a held
`X ⪯ Z`, `σ[X].hF ≤ σ[Z].hF`. -/
theorem hF_mono (hr : st.Reachable acp₀) {X Z : NodeBlock P ACP} (hXZ : st.Anc X Z) :
    (st.σ X.root).hF ≤ (st.σ Z.root).hF := by
  induction hXZ with
  | refl => exact le_rfl
  | @tail Y Y' _ hYY' ih =>
    obtain ⟨hY, hY', hp⟩ := hYY'
    obtain ⟨-, -, -, ht⟩ := Healing.Store.step_σ hr hY' hp
    obtain ⟨c, -, -, -, hc⟩ := chain_state_of_chain P ACP acp₀ st hr Y hY
    exact ih.trans (FG.height_step P.fg _ _ _ _ hc ht).2.2.1

private theorem h_le_anc (hr : st.Reachable acp₀) {X Z : NodeBlock P ACP} (hXZ : st.Anc X Z) :
    (st.σ X.root).h ≤ (st.σ Z.root).h := by
  induction hXZ with
  | refl => exact le_rfl
  | @tail Y Y' _ hYY' ih =>
    obtain ⟨-, hY', hp⟩ := hYY'
    obtain ⟨-, -, -, ht⟩ := Healing.Store.step_σ hr hY' hp
    rcases P.fg.stateTransition_ThSlot ht with ⟨e, -⟩ | ⟨e, -⟩ <;> omega

/-- **The entry is constant at one height.** In a reachable store, for a held `X ⪯ Z` with
`σ[Z].h = σ[X].h`, `σ[Z].Th = σ[X].Th`. -/
theorem Th_eq_of_h_eq (hr : st.Reachable acp₀) {X Z : NodeBlock P ACP} (hXZ : st.Anc X Z)
    (hh : (st.σ Z.root).h = (st.σ X.root).h) : (st.σ Z.root).Th = (st.σ X.root).Th := by
  induction hXZ with
  | refl => rfl
  | @tail Y Y' hXY hYY' ih =>
    obtain ⟨-, hY', hp⟩ := hYY'
    obtain ⟨-, -, -, ht⟩ := Healing.Store.step_σ hr hY' hp
    have h1 := h_le_anc hr hXY
    rcases P.fg.stateTransition_ThSlot ht with ⟨e, -, e'⟩ | ⟨e, -, -⟩
    · rw [e']
      exact ih (e.symm.trans hh)
    · omega

/-- **A self-entry at most the finalized height is below the finalized block.** In a reachable
store, let `T ⪯ Z` be held with `σ[T].Th = T.root` and `σ[T].h ≤ σ[Z].hF`. Then the block of
root `σ[Z].F` is held and `T ⪯` it. -/
theorem self_entry_anc_finalized (hr : st.Reachable acp₀) {T Z : NodeBlock P ACP}
    (hT : T ∈ st.tree) (hZ : Z ∈ st.tree) (hTZ : st.Anc T Z)
    (hTs : (st.σ T.root).Th = T.root) (hh : (st.σ T.root).h ≤ (st.σ Z.root).hF) :
    ∃ F, st.blocks (st.σ Z.root).F = some F ∧ st.Anc T F := by
  have hcoh := (accepted_tree P ACP acp₀ st hr).2.1
  obtain ⟨c, -, -, -, hc⟩ := chain_state_of_chain P ACP acp₀ st hr T hT
  have h1 := (FG.chain_invariants P.fg _ _ hc).1
  obtain ⟨-, ⟨F, hF, hFr, hFZ⟩, -⟩ := entry_state_of_source P ACP acp₀ st hr Z hZ
  change st.blocks F.root = some F at hF
  refine ⟨F, by rw [← hFr]; exact hF, ?_⟩
  rcases fin_pair_self_entry_or_zero hr hZ with h0 | ⟨W, hW, hWr, hWh, hWT⟩
  · omega
  change st.blocks W.root = some W at hW
  rw [hWr, ← hFr] at hW
  obtain rfl : W = F := Option.some.inj (hW.symm.trans hF)
  rcases Anc.total hcoh hTZ hFZ with hTF | hFT
  · exact hTF
  · have h2 := h_le_anc hr hFT
    have hEq := Th_eq_of_h_eq hr hFT (by omega)
    rw [hTs, hWT] at hEq
    have hb : st.blocks T.root = some T := hT
    rw [hEq] at hb
    obtain rfl : T = W := Option.some.inj (hb.symm.trans hF)
    exact Relation.ReflTransGen.refl

/-- **Theorem F along an ancestry, crossings early or justifying (store form).**
`theorem_F_of_anc` with the timing premise weakened: every held `D ⪯ W` with held parent
`Z ⪰ X` at height `σ[X].h` or `σ[X].h + 1` that enters the next height
(`σ[D].h = σ[Z].h + 1`) has `D.slot < σ[Z].ThSlot + δt` or justifies (`σ[D].hj = σ[Z].h`).
A crossing at age `≥ δt` with a target quorum (justify precedes timeout) meets the second
disjunct. -/
theorem theorem_F_of_anc'' (hr : st.Reachable acp₀) {X W : NodeBlock P ACP}
    (hX : X ∈ st.tree) (hXW : st.Anc X W) (hh : (st.σ X.root).h + 1 < (st.σ W.root).h)
    (hs : ∀ D ∈ st.tree, ∀ Z ∈ st.tree, D.parent = some Z.root → st.Anc X Z → st.Anc D W →
      ((st.σ Z.root).h = (st.σ X.root).h ∨ (st.σ Z.root).h = (st.σ X.root).h + 1) →
      (st.σ D.root).h = (st.σ Z.root).h + 1 →
      D.slot < (st.σ Z.root).ThSlot + P.fg.δt ∨ (st.σ D.root).hj = (st.σ Z.root).h) :
    ∃ D₁ ∈ st.tree, ∃ D₂ ∈ st.tree, st.Anc X D₁ ∧ st.Anc D₁ D₂ ∧ st.Anc D₂ W ∧
      (st.σ D₁.root).h = (st.σ X.root).h + 1 ∧ (st.σ D₁.root).hj = (st.σ X.root).h ∧
      (st.σ D₁.root).J = (st.σ X.root).Th ∧
      (st.σ D₂.root).h = (st.σ X.root).h + 2 ∧ (st.σ D₂.root).hj = (st.σ X.root).h + 1 ∧
      (st.σ D₂.root).J = (st.σ D₁.root).Th ∧
      (st.σ D₂.root).F = (st.σ X.root).Th ∧ (st.σ D₂.root).hF = (st.σ X.root).h ∧
      ∃ T ∈ st.tree, T.root = (st.σ X.root).Th ∧ st.Anc T X := by
  obtain ⟨c, d, hc, hd, hpre⟩ := chain_states_of_anc' hr hX hXW
  obtain ⟨d₁, D₁, d₂, D₂, d₃, σ₁, σ₂, rfl, h1, h1h, h1j, h1J, h2, h2h, h2j, h2J, h2F, h2hF⟩ :=
    P.fg.theorem_F_map_chain' Block.fgView hc hd hh (by
      intro d₁ D d₂ ρ ρ' he hρ hρ' hρh
      obtain ⟨hD, -, hDW, -, hσD, -, Z, hZ, hpar, hXZ, hσZ⟩ := hpre d₁ D d₂ he
      obtain rfl : ρ = st.σ Z.root := Option.some.inj (hρ.symm.trans hσZ)
      obtain rfl : ρ' = st.σ D.root := Option.some.inj (hρ'.symm.trans hσD)
      exact hs D hD Z hZ hpar hXZ hDW hρh)
  obtain ⟨hD₁, hXD₁, -, -, hσ₁, -⟩ := hpre d₁ D₁ (d₂ ++ D₂ :: d₃) rfl
  obtain ⟨hD₂, -, hD₂W, -, hσ₂, hY, -⟩ := hpre (d₁ ++ D₁ :: d₂) D₂ d₃
    (List.append_assoc d₁ (D₁ :: d₂) (D₂ :: d₃)).symm
  obtain rfl : σ₁ = st.σ D₁.root := Option.some.inj (h1.symm.trans hσ₁)
  obtain rfl : σ₂ = st.σ D₂.root := Option.some.inj (h2.symm.trans hσ₂)
  obtain ⟨⟨T, hT, hTr, hTX, -⟩, -⟩ := entry_state_of_source P ACP acp₀ st hr X hX
  exact ⟨D₁, hD₁, D₂, hD₂, hXD₁, hY D₁ (List.mem_append_right d₁ List.mem_cons_self), hD₂W,
    h1h, h1j, h1J, h2h, h2j, h2J, h2F, h2hF, T, hT, hTr, hTX⟩

/-- **Window coverage, crossings early or justifying.** `finalized_covers_of_window'` with the
premise of `theorem_F_of_anc''`: only the held `D ⪯ W` that enter the next height from a held
parent `Z ⪰ X` at height `σ[X].h` or `σ[X].h + 1` are constrained, and each is early
(`D.slot < σ[Z].ThSlot + δt`) or justifies (`σ[D].hj = σ[Z].h`). -/
theorem finalized_covers_of_window'' (hr : st.Reachable acp₀) {B₀ B₃ X W : NodeBlock P ACP}
    (hX : X ∈ st.tree) (hB₃ : B₃ ∈ st.tree) (hXW : st.Anc X W) (hWB : st.Anc W B₃)
    (hh : (st.σ X.root).h + 1 < (st.σ W.root).h)
    (hs : ∀ D ∈ st.tree, ∀ Z ∈ st.tree, D.parent = some Z.root → st.Anc X Z → st.Anc D W →
      ((st.σ Z.root).h = (st.σ X.root).h ∨ (st.σ Z.root).h = (st.σ X.root).h + 1) →
      (st.σ D.root).h = (st.σ Z.root).h + 1 →
      D.slot < (st.σ Z.root).ThSlot + P.fg.δt ∨ (st.σ D.root).hj = (st.σ Z.root).h)
    (hB₀ : ∀ T ∈ st.tree, T.root = (st.σ X.root).Th → st.Anc B₀ T) :
    ∃ F, st.blocks (st.σ B₃.root).F = some F ∧ st.Anc B₀ F := by
  obtain ⟨-, -, D₂, -, -, -, hD₂W, -, -, -, -, -, -, -, hhF, -⟩ :=
    theorem_F_of_anc'' hr hX hXW hh hs
  obtain ⟨⟨E, hE, hEr, hEX, hEh, hET⟩, -⟩ := entry_state_of_source P ACP acp₀ st hr X hX
  obtain ⟨F, hF, hEF⟩ := self_entry_anc_finalized hr hE hB₃
    (hEX.trans (hXW.trans hWB)) (hET.trans hEr.symm)
    (by rw [hEh, ← hhF]; exact hF_mono hr (hD₂W.trans hWB))
  exact ⟨F, hF, (hB₀ E hE hEr).trans hEF⟩

end Store

namespace Refinement

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

end Refinement

end Consensus.Goldilocks

end
