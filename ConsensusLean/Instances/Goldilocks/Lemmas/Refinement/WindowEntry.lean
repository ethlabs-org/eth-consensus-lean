module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowUnanimous
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Live
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High

public section

/-! # Goldilocks Refinement: the entry is justified on the parent's chain (L5.4, WI-19)

Workbench `fg-liveness/r14-end-to-end`, s5 L5.4: the entry `(h, T)` is justified on the
canonical chain, and the predecessor is finalized if the height is bound.

* `Store.chain_states_of_anc`: the store bridge. For a held `X ⪯ W`, a chain `c` reaches
  `σ[X]` and `c ++ d` reaches `σ[W]`; every block of `d` is held, between `X` and `W`, has a
  slot at most `W.slot`, and the prefix of `c ++ d` that ends at it reaches its state.
* `Store.entry_justified_of_anc`: `FGParams.early_cross_chain_justifies` at the store: if
  `σ[X].h < σ[W].h` and `W.slot < σ[X].ThSlot + δt`, a held `D` with `X ⪯ D ⪯ W` justified
  the entry of `σ[X]`, and finalized the predecessor block if `σ[X]` is bound.
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
* `window_entry_justified_or_window` (L5.4): in case (A), every honest proposal of a slot `s`
  with `v + Δ ≤ t_s` and `s ≤ σ[X].ThSlot + δt` has an honest parent `Pr ⪰ X` on whose chain
  a block justified `(h, T)` (and finalized the predecessor if bound), at every honest holder.
  The bound `s ≤ σ[X].ThSlot + δt` stays a premise: the window gives only `v + Δ ≤ t_s`. -/

namespace Consensus.Goldilocks

namespace FG.FGParams

variable (gp : FGParams)

/-- `chainState_append` through a map. -/
theorem chainState_map_append_singleton {α : Type} (f : α → FGBlock gp.n) (c : List α)
    (B : α) : gp.chainState ((c ++ [B]).map f) =
      (gp.chainState (c.map f)).bind (gp.stateTransition · (f B)) := by
  rw [List.map_append, List.map_singleton, gp.chainState_append]

/-- `early_cross_chain_justifies` through a map: the justifying block is the image of a block of
`d`. -/
theorem early_cross_map_justifies {α : Type} (f : α → FGBlock gp.n) {c d : List α}
    {σ τ : ChainState gp.n} (hc : gp.chainState (c.map f) = some σ)
    (hd : gp.chainState ((c ++ d).map f) = some τ) (hh : σ.h < τ.h)
    (hs : ∀ B ∈ d, (f B).slot < σ.ThSlot + gp.δt) :
    ∃ d₁ B d₂ σ₂, d = d₁ ++ B :: d₂ ∧ gp.chainState ((c ++ d₁ ++ [B]).map f) = some σ₂ ∧
      σ₂.h = σ.h + 1 ∧ σ₂.hj = σ.h ∧ σ₂.J = σ.Th ∧
      (σ.bound → σ₂.F = σ.J ∧ σ₂.hF = σ.hj) := by
  rw [List.map_append] at hd
  obtain ⟨e₁, B, e₂, σ₂, he, hσ₂, h⟩ := gp.early_cross_chain_justifies hc hd hh (by
    intro B hB
    obtain ⟨B', hB', rfl⟩ := List.mem_map.1 hB
    exact hs B' hB')
  obtain ⟨d₁, r, rfl, rfl, hr'⟩ := List.map_eq_append_iff.1 he
  obtain ⟨D, d₂, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.1 hr'
  refine ⟨d₁, D, d₂, σ₂, rfl, ?_, h⟩
  simpa [List.map_append] using hσ₂


/-- `theorem_F_chain` through a map: the two justifying blocks are images of blocks of `d`. -/
theorem theorem_F_map_chain {α : Type} (f : α → FGBlock gp.n) {c d : List α}
    {σ τ : ChainState gp.n} (hc : gp.chainState (c.map f) = some σ)
    (hd : gp.chainState ((c ++ d).map f) = some τ) (hh : σ.h + 1 < τ.h)
    (hs : ∀ d₁ B d₂ ρ, d = d₁ ++ B :: d₂ → gp.chainState ((c ++ d₁).map f) = some ρ →
      (ρ.h = σ.h ∨ ρ.h = σ.h + 1) → (f B).slot < ρ.ThSlot + gp.δt) :
    ∃ d₁ B₁ d₂ B₂ d₃ σ₁ σ₂, d = d₁ ++ B₁ :: (d₂ ++ B₂ :: d₃) ∧
      gp.chainState ((c ++ d₁ ++ [B₁]).map f) = some σ₁ ∧
      σ₁.h = σ.h + 1 ∧ σ₁.hj = σ.h ∧ σ₁.J = σ.Th ∧
      gp.chainState ((c ++ (d₁ ++ B₁ :: d₂) ++ [B₂]).map f) = some σ₂ ∧
      σ₂.h = σ.h + 2 ∧ σ₂.hj = σ.h + 1 ∧ σ₂.J = σ₁.Th ∧
      σ₂.F = σ.Th ∧ σ₂.hF = σ.h := by
  rw [List.map_append] at hd
  obtain ⟨e₁, B₁, e₂, B₂, e₃, σ₁, σ₂, he, h1, h1h, h1j, h1J, h2, h2h, h2j, h2J, h2F, h2hF⟩ :=
    gp.theorem_F_chain hc hd hh (by
      intro e₁ B e₂ ρ he hρ hρh
      obtain ⟨d₁, r, rfl, rfl, hr'⟩ := List.map_eq_append_iff.1 he
      obtain ⟨D, d₂, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.1 hr'
      exact hs d₁ D d₂ ρ rfl (by simpa [List.map_append] using hρ) hρh)
  obtain ⟨d₁, r, rfl, rfl, hr₁⟩ := List.map_eq_append_iff.1 he
  obtain ⟨D₁, r', rfl, rfl, hr₂⟩ := List.map_eq_cons_iff.1 hr₁
  obtain ⟨d₂, r'', rfl, rfl, hr₃⟩ := List.map_eq_append_iff.1 hr₂
  obtain ⟨D₂, d₃, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.1 hr₃
  exact ⟨d₁, D₁, d₂, D₂, d₃, σ₁, σ₂, rfl, by simpa [List.map_append] using h1, h1h, h1j, h1J,
    by simpa [List.map_append] using h2, h2h, h2j, h2J, h2F, h2hF⟩

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

/-- **The store bridge (G0.1 along an ancestry).** For a held `X ⪯ W` in a reachable store, a
chain `c` reaches `σ[X]` and `c ++ d` reaches `σ[W]`, and every block `B` of `d` (with
`d = d₁ ++ B :: d₂`) is held, has `X ⪯ B ⪯ W` and `B.slot ≤ W.slot`, and `c ++ d₁ ++ [B]`
reaches `σ[B]`. -/
theorem chain_states_of_anc (hr : st.Reachable acp₀) {X W : NodeBlock P ACP}
    (hX : X ∈ st.tree) (hXW : st.Anc X W) :
    ∃ c d : List (NodeBlock P ACP),
      P.fg.chainState (c.map Block.fgView) = some (st.σ X.root) ∧
      P.fg.chainState ((c ++ d).map Block.fgView) = some (st.σ W.root) ∧
      ∀ d₁ B d₂, d = d₁ ++ B :: d₂ → B ∈ st.tree ∧ st.Anc X B ∧ st.Anc B W ∧
        B.slot ≤ W.slot ∧
        P.fg.chainState ((c ++ d₁ ++ [B]).map Block.fgView) = some (st.σ B.root) := by
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
      refine ⟨hW', ?_, Relation.ReflTransGen.refl, le_rfl, ?_⟩
      · exact hXW'.tail ⟨hW, hW', hp⟩
      · rw [← List.append_assoc] at hd'; exact hd'
    · have he' : d ++ [W'] = (d₁ ++ B :: d₂') ++ [z] := by simpa using he
      obtain ⟨rfl, -⟩ := List.append_inj' he' rfl
      obtain ⟨hB, hXB, hBW, hBs, hσ⟩ := hpre d₁ B d₂' rfl
      exact ⟨hB, hXB, hBW.tail ⟨hW, hW', hp⟩, by omega, hσ⟩

/-- **The entry is justified below an early higher block (L5.4 step 4, store form).** In a
reachable store, for a held `X ⪯ W` with `σ[X].h < σ[W].h` and `W.slot < σ[X].ThSlot + δt`,
some held `D` with `X ⪯ D ⪯ W` has entered `σ[X].h + 1` by justifying the entry of `σ[X]`
(`h_j = σ[X].h`, `J = σ[X].Th`), and if `σ[X]` is bound, `D` finalized its predecessor block
(`F = σ[X].J`, `h_F = σ[X].h_j`). -/
theorem entry_justified_of_anc (hr : st.Reachable acp₀) {X W : NodeBlock P ACP}
    (hX : X ∈ st.tree) (hXW : st.Anc X W) (hh : (st.σ X.root).h < (st.σ W.root).h)
    (hs : W.slot < (st.σ X.root).ThSlot + P.fg.δt) :
    ∃ D ∈ st.tree, st.Anc X D ∧ st.Anc D W ∧ (st.σ D.root).h = (st.σ X.root).h + 1 ∧
      (st.σ D.root).hj = (st.σ X.root).h ∧ (st.σ D.root).J = (st.σ X.root).Th ∧
      ((st.σ X.root).bound → (st.σ D.root).F = (st.σ X.root).J ∧
        (st.σ D.root).hF = (st.σ X.root).hj) := by
  obtain ⟨c, d, hc, hd, hpre⟩ := chain_states_of_anc hr hX hXW
  obtain ⟨d₁, D, d₂, σ₂, rfl, hσ₂, h1, h2, h3, h4⟩ :=
    P.fg.early_cross_map_justifies Block.fgView hc hd hh (by
      intro B hB
      obtain ⟨d₁, d₂, rfl⟩ := List.append_of_mem hB
      exact lt_of_le_of_lt (hpre d₁ B d₂ rfl).2.2.2.1 hs)
  obtain ⟨hD, hXD, hDW, -, hσ⟩ := hpre d₁ D d₂ rfl
  obtain rfl : σ₂ = st.σ D.root := Option.some.inj (hσ₂.symm.trans hσ)
  exact ⟨D, hD, hXD, hDW, h1, h2, h3, h4⟩


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

/-- **Theorem F along an ancestry (store form).** In a reachable store, let `X ⪯ W` be held with
`σ[X].h + 1 < σ[W].h`, and let every held `D` with a held parent `Z`, `X ⪯ Z`, `D ⪯ W` and
`σ[Z].h ∈ {σ[X].h, σ[X].h + 1}` have `D.slot < σ[Z].ThSlot + δt`. Then there are held
`X ⪯ D₁ ⪯ D₂ ⪯ W`: `D₁` justified `(σ[X].h, σ[X].Th)`, `D₂` justified `(σ[X].h + 1, σ[D₁].Th)`
and finalized `F = σ[X].Th` with `h_F = σ[X].h`; the block `T` of root `σ[X].Th` is held with
`T ⪯ X`. -/
theorem theorem_F_of_anc (hr : st.Reachable acp₀) {X W : NodeBlock P ACP}
    (hX : X ∈ st.tree) (hXW : st.Anc X W) (hh : (st.σ X.root).h + 1 < (st.σ W.root).h)
    (hs : ∀ D ∈ st.tree, ∀ Z ∈ st.tree, D.parent = some Z.root → st.Anc X Z → st.Anc D W →
      ((st.σ Z.root).h = (st.σ X.root).h ∨ (st.σ Z.root).h = (st.σ X.root).h + 1) →
      D.slot < (st.σ Z.root).ThSlot + P.fg.δt) :
    ∃ D₁ ∈ st.tree, ∃ D₂ ∈ st.tree, st.Anc X D₁ ∧ st.Anc D₁ D₂ ∧ st.Anc D₂ W ∧
      (st.σ D₁.root).h = (st.σ X.root).h + 1 ∧ (st.σ D₁.root).hj = (st.σ X.root).h ∧
      (st.σ D₁.root).J = (st.σ X.root).Th ∧
      (st.σ D₂.root).h = (st.σ X.root).h + 2 ∧ (st.σ D₂.root).hj = (st.σ X.root).h + 1 ∧
      (st.σ D₂.root).J = (st.σ D₁.root).Th ∧
      (st.σ D₂.root).F = (st.σ X.root).Th ∧ (st.σ D₂.root).hF = (st.σ X.root).h ∧
      ∃ T ∈ st.tree, T.root = (st.σ X.root).Th ∧ st.Anc T X := by
  obtain ⟨c, d, hc, hd, hpre⟩ := chain_states_of_anc' hr hX hXW
  obtain ⟨d₁, D₁, d₂, D₂, d₃, σ₁, σ₂, rfl, h1, h1h, h1j, h1J, h2, h2h, h2j, h2J, h2F, h2hF⟩ :=
    P.fg.theorem_F_map_chain Block.fgView hc hd hh (by
      intro d₁ D d₂ ρ he hρ hρh
      obtain ⟨hD, -, hDW, -, -, -, Z, hZ, hpar, hXZ, hσZ⟩ := hpre d₁ D d₂ he
      obtain rfl : ρ = st.σ Z.root := Option.some.inj (hρ.symm.trans hσZ)
      exact hs D hD Z hZ hpar hXZ hDW hρh)
  obtain ⟨hD₁, hXD₁, -, -, hσ₁, -⟩ := hpre d₁ D₁ (d₂ ++ D₂ :: d₃) rfl
  obtain ⟨hD₂, -, hD₂W, -, hσ₂, hY, -⟩ := hpre (d₁ ++ D₁ :: d₂) D₂ d₃
    (List.append_assoc d₁ (D₁ :: d₂) (D₂ :: d₃)).symm
  obtain rfl : σ₁ = st.σ D₁.root := Option.some.inj (h1.symm.trans hσ₁)
  obtain rfl : σ₂ = st.σ D₂.root := Option.some.inj (h2.symm.trans hσ₂)
  obtain ⟨⟨T, hT, hTr, hTX, -⟩, -⟩ := entry_state_of_source P ACP acp₀ st hr X hX
  exact ⟨D₁, hD₁, D₂, hD₂, hXD₁, hY D₁ (List.mem_append_right d₁ List.mem_cons_self), hD₂W,
    h1h, h1j, h1J, h2h, h2j, h2J, h2F, h2hF, T, hT, hTr, hTX⟩


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

/-- **The entry slot grows along an ancestry.** In a reachable store, for a held `X ⪯ Z`,
`σ[X].ThSlot ≤ σ[Z].ThSlot`. -/
theorem ThSlot_mono (hr : st.Reachable acp₀) {X Z : NodeBlock P ACP} (hXZ : st.Anc X Z) :
    (st.σ X.root).ThSlot ≤ (st.σ Z.root).ThSlot := by
  induction hXZ with
  | refl => exact le_rfl
  | @tail Y Y' _ hYY' ih =>
    obtain ⟨hY, hY', hp⟩ := hYY'
    obtain ⟨-, -, -, ht⟩ := Healing.Store.step_σ hr hY' hp
    have hsl : Y.slot < Y'.slot := (accepted_tree P ACP acp₀ st hr).2.1.2 Y hY Y' hY' hp
    have := ThSlot_le_slot hr hY
    rcases P.fg.stateTransition_ThSlot ht with ⟨-, e, -⟩ | ⟨-, e, -⟩
    · rw [e]; exact ih
    · rw [e]; change _ ≤ Y'.slot; omega

/-- **Theorem F along an ancestry, slot form.** `theorem_F_of_anc` with the timing premise
replaced by `W.slot < σ[X].ThSlot + δt`: slots grow along an ancestry, and so does the entry
slot. -/
theorem theorem_F_of_anc_slot (hr : st.Reachable acp₀) {X W : NodeBlock P ACP}
    (hX : X ∈ st.tree) (hXW : st.Anc X W) (hh : (st.σ X.root).h + 1 < (st.σ W.root).h)
    (hs : W.slot < (st.σ X.root).ThSlot + P.fg.δt) :
    ∃ D₁ ∈ st.tree, ∃ D₂ ∈ st.tree, st.Anc X D₁ ∧ st.Anc D₁ D₂ ∧ st.Anc D₂ W ∧
      (st.σ D₁.root).h = (st.σ X.root).h + 1 ∧ (st.σ D₁.root).hj = (st.σ X.root).h ∧
      (st.σ D₁.root).J = (st.σ X.root).Th ∧
      (st.σ D₂.root).h = (st.σ X.root).h + 2 ∧ (st.σ D₂.root).hj = (st.σ X.root).h + 1 ∧
      (st.σ D₂.root).J = (st.σ D₁.root).Th ∧
      (st.σ D₂.root).F = (st.σ X.root).Th ∧ (st.σ D₂.root).hF = (st.σ X.root).h ∧
      ∃ T ∈ st.tree, T.root = (st.σ X.root).Th ∧ st.Anc T X := by
  have hcoh := (accepted_tree P ACP acp₀ st hr).2.1
  refine theorem_F_of_anc hr hX hXW hh fun D _ Z _ _ hXZ hDW _ => ?_
  have h1 := (hDW.slot_le hcoh).1
  have h2 := ThSlot_mono hr hXZ
  omega

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

/-- **Window coverage at the store (WI-19/20, the `CacheCoverage` premise shape).** In a
reachable store, let `X ⪯ W ⪯ B₃` be held with `σ[X].h + 1 < σ[W].h` and
`W.slot < σ[X].ThSlot + δt`, and let `B₀ ⪯ T` for every held `T` of root `σ[X].Th` (the entry
block of `σ[X]`). Then the block `F` of root `σ[B₃].F` is held and `B₀ ⪯ F`
(`theorem_F_of_anc_slot` finalizes the entry at `D₂ ⪯ W`; the finalized height grows
along the chain, and the finalized block of `B₃` is then at or above that entry). -/
theorem finalized_covers_of_window (hr : st.Reachable acp₀) {B₀ B₃ X W : NodeBlock P ACP}
    (hX : X ∈ st.tree) (hB₃ : B₃ ∈ st.tree) (hXW : st.Anc X W) (hWB : st.Anc W B₃)
    (hh : (st.σ X.root).h + 1 < (st.σ W.root).h)
    (hs : W.slot < (st.σ X.root).ThSlot + P.fg.δt)
    (hB₀ : ∀ T ∈ st.tree, T.root = (st.σ X.root).Th → st.Anc B₀ T) :
    ∃ F, st.blocks (st.σ B₃.root).F = some F ∧ st.Anc B₀ F := by
  obtain ⟨-, -, D₂, -, -, -, hD₂W, -, -, -, -, -, -, -, hhF, -⟩ :=
    theorem_F_of_anc_slot hr hX hXW hh hs
  obtain ⟨⟨E, hE, hEr, hEX, hEh, hET⟩, -⟩ := entry_state_of_source P ACP acp₀ st hr X hX
  obtain ⟨F, hF, hEF⟩ := self_entry_anc_finalized hr hE hB₃
    (hEX.trans (hXW.trans hWB)) (hET.trans hEr.symm)
    (by rw [hEh, ← hhF]; exact hF_mono hr (hD₂W.trans hWB))
  exact ⟨F, hF, (hB₀ E hE hEr).trans hEF⟩

/-- **Window coverage, per-height timing.** `finalized_covers_of_window` with the timing premise
of `theorem_F_of_anc`: every held `D ⪯ W` whose held parent `Z ⪰ X` is at height `σ[X].h` or
`σ[X].h + 1` has `D.slot < σ[Z].ThSlot + δt`. Each crossing is timed from its own entry. -/
theorem finalized_covers_of_window' (hr : st.Reachable acp₀) {B₀ B₃ X W : NodeBlock P ACP}
    (hX : X ∈ st.tree) (hB₃ : B₃ ∈ st.tree) (hXW : st.Anc X W) (hWB : st.Anc W B₃)
    (hh : (st.σ X.root).h + 1 < (st.σ W.root).h)
    (hs : ∀ D ∈ st.tree, ∀ Z ∈ st.tree, D.parent = some Z.root → st.Anc X Z → st.Anc D W →
      ((st.σ Z.root).h = (st.σ X.root).h ∨ (st.σ Z.root).h = (st.σ X.root).h + 1) →
      D.slot < (st.σ Z.root).ThSlot + P.fg.δt)
    (hB₀ : ∀ T ∈ st.tree, T.root = (st.σ X.root).Th → st.Anc B₀ T) :
    ∃ F, st.blocks (st.σ B₃.root).F = some F ∧ st.Anc B₀ F := by
  obtain ⟨-, -, D₂, -, -, -, hD₂W, -, -, -, -, -, -, -, hhF, -⟩ :=
    theorem_F_of_anc hr hX hXW hh hs
  obtain ⟨⟨E, hE, hEr, hEX, hEh, hET⟩, -⟩ := entry_state_of_source P ACP acp₀ st hr X hX
  obtain ⟨F, hF, hEF⟩ := self_entry_anc_finalized hr hE hB₃
    (hEX.trans (hXW.trans hWB)) (hET.trans hEr.symm)
    (by rw [hEh, ← hhF]; exact hF_mono hr (hD₂W.trans hWB))
  exact ⟨F, hF, (hB₀ E hE hEr).trans hEF⟩

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

/-- Two held blocks of one honest store with the same root are equal. -/
private theorem eq_of_root_eq (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {X X' : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state y k).fg.tree) (hX' : X' ∈ (tr.state y k).fg.tree)
    (he : X.root = X'.root) : X = X' :=
  (Store.accepted_tree _ _ _ _ (Compose.fg_reachable hrun.toLocalRun hy k)).2.1.1 hX hX' he

/-- **The window with the entry below the report.** `window_justifies_or_parents_above_after`
with one more fact in case (A): every held `X` with root `T` has `X ⪯ C` (the report of
`hreports'` is above the held block of root `T`, which is unique). -/
theorem window_justifies_or_parents_above_after' (hrun : GoldilocksRun proposer dg H tr)
    (hq : Hᶜ.ncard < sp.toParams.fg.q)
    {g ΔF v gR tH : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : Healed tr H proposer gR tH h₀ E)
    (hs : Healing.HSShared tr H dg g ΔF) (hv : gbar g ≤ v) {s₀ gM s₁ : Nat}
    (hM4 : ∀ s, s₀ ≤ s → ∃ s', s ≤ s' ∧ s' < s + gM ∧
      ∃ P, Healing.HonestProposalRun tr H proposer s' P)
    (hs₁ : s₀ ≤ s₁) (hvs : v + ΔF ≤ sp.ts s₁)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ℓ) (htH : tH ≤ tr.time k) {l}
    (hl : l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k))
    (hf : l.fast = true) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree)
    (hBl : B.root = l.block) (hks : tr.time k + sp.Δ ≤ sp.ts s₁) {h T : Nat}
    (hh : ((tr.state y k).fg.σ B.root).h = h) (hT : ((tr.state y k).fg.σ B.root).Th = T)
    (hh₀ : h₀ + 1 ≤ h) {ΔR a b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg gR ΔR a b) (hvb : v ≤ b)
    (hreports' : ∀ X ∈ (tr.state y k).fg.tree, X.root = T →
      ∀ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ tH ≤ tr.time r ∧
        tr.time r ≤ v ∧ Anc (tr.HonestBlocks H) X C) :
    (∃ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧
      Healing.cutZ sp.toParams gR < tr.time r ∧ tH ≤ tr.time r ∧ tr.time r ≤ v ∧
      h < ((tr.state z r).fg.σ C.root).h ∧
      (∀ X ∈ (tr.state y k).fg.tree, X.root = T → Anc (tr.HonestBlocks H) X C) ∧
      ∀ s P, Healing.HonestProposalRun tr H proposer s P → v + sp.Δ ≤ sp.ts s →
        ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) C Pr ∧
          ∀ y ∈ H, ∀ k, Pr ∈ (tr.state y k).fg.tree →
            h < ((tr.state y k).fg.σ Pr.root).h) ∨
    ∃ s', s₁ ≤ s' ∧ s' < s₁ + gM ∧ proposer s' ∈ H ∧ ∃ k X Pr,
      tr.ProposesAt (proposer s') k X ∧ X.slot = s' ∧ X.parent = some Pr.root ∧
      Pr ∈ (tr.state (proposer s') k).fg.tree ∧
      (h < ((tr.state (proposer s') k).fg.σ Pr.root).h ∨
        (((tr.post k).fg.σ X.root).hj = h ∧ ((tr.post k).fg.σ X.root).J = T ∧
          (((tr.state (proposer s') k).fg.σ Pr.root).bound →
            ((tr.post k).fg.σ X.root).hF =
              ((tr.state (proposer s') k).fg.σ Pr.root).hj))) := by
  rcases window_justifies_or_crossed_after hrun hq hH hs hv hM4 hs₁ hvs hy hc htH hl hf hB hBl
      hks hh hT hh₀ hp hvb hreports' with
    ⟨X₀, hX₀, hX₀r, -, z, hz, r, ell, C, hto, htr, hrv, hXC, hC, hlt⟩ | hW
  · refine Or.inl ⟨z, hz, r, ell, C, hto, ?_, htr, hrv, hlt, fun X hX hXr => ?_,
      fun s P hP hsv => ?_⟩
    · have hrh := hH.toHealedRecords.rh
      exact hp.cutZ_lt_of_high hz hC (by omega)
    · rw [eq_of_root_eq hrun hy hX hX₀ (hXr.trans hX₀r.symm)]
      exact hXC
    · exact crossed_parents_above hrun hp.noColl hH hz hto htr hlt hP (by linarith)
  · exact Or.inr hW

/-- **The two-way window theorem with the entry below the report.**
`window_justifies_or_parents_above_unanimous''` with one more fact in case (A): every held `X`
with root `T` has `X ⪯ C`; in the escape case, `X ⪯ P ⪯ C` by `hXP`. -/
theorem window_justifies_or_parents_above_unanimous_entry (hrun : GoldilocksRun proposer dg H tr)
    (hq : Hᶜ.ncard < sp.toParams.fg.q)
    {g ΔF v gR tH : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : Healed tr H proposer gR tH h₀ E)
    (hs : Healing.HSShared tr H dg g ΔF) (hv : gbar g ≤ v) {s₀ gM s₁ : Nat}
    (hM4 : ∀ s, s₀ ≤ s → ∃ s', s ≤ s' ∧ s' < s + gM ∧
      ∃ P, Healing.HonestProposalRun tr H proposer s' P)
    (hs₁ : s₀ ≤ s₁) (hvs : v + ΔF ≤ sp.ts s₁)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ℓ) (htH : tH ≤ tr.time k) {l}
    (hl : l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k))
    (hf : l.fast = true) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree)
    (hBl : B.root = l.block) (hks : tr.time k + sp.Δ ≤ sp.ts s₁) {h T : Nat}
    (hh : ((tr.state y k).fg.σ B.root).h = h) (hT : ((tr.state y k).fg.σ B.root).Th = T)
    (hh₀ : h₀ + 1 ≤ h) {ΔR a b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg gR ΔR a b) (hvb : v ≤ b)
    (hcatch : Healing.CatchRun tr H gR (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hPg : P.root ≠ sp.genesisRoot)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar gR + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (htu : tH ≤ sp.ts u) (huv : sp.ts u + 6 * sp.Δ ≤ v)
    (hXP : ∀ X ∈ (tr.state y k).fg.tree, X.root = T → Anc (tr.HonestBlocks H) X P) :
    (∃ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧
      Healing.cutZ sp.toParams gR < tr.time r ∧ tH ≤ tr.time r ∧ tr.time r ≤ v ∧
      h < ((tr.state z r).fg.σ C.root).h ∧
      (∀ X ∈ (tr.state y k).fg.tree, X.root = T → Anc (tr.HonestBlocks H) X C) ∧
      ∀ s P, Healing.HonestProposalRun tr H proposer s P → v + sp.Δ ≤ sp.ts s →
        ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) C Pr ∧
          ∀ y ∈ H, ∀ k, Pr ∈ (tr.state y k).fg.tree →
            h < ((tr.state y k).fg.σ Pr.root).h) ∨
    ∃ s', s₁ ≤ s' ∧ s' < s₁ + gM ∧ proposer s' ∈ H ∧ ∃ k X Pr,
      tr.ProposesAt (proposer s') k X ∧ X.slot = s' ∧ X.parent = some Pr.root ∧
      Pr ∈ (tr.state (proposer s') k).fg.tree ∧
      (h < ((tr.state (proposer s') k).fg.σ Pr.root).h ∨
        (((tr.post k).fg.σ X.root).hj = h ∧ ((tr.post k).fg.σ X.root).J = T ∧
          (((tr.state (proposer s') k).fg.σ Pr.root).bound →
            ((tr.post k).fg.σ X.root).hF =
              ((tr.state (proposer s') k).fg.σ Pr.root).hj))) := by
  have hBy : B ∈ (tr.state y k).fg.tree := Healing.mem_tree_of_frame hrun hy hc hB
  obtain ⟨X, hXk, hXr, -, hXh, -⟩ := lock_entry_block hrun hy hBy
  rcases window_reports_of_unanimous hp hcatch hP hslot hu hPg hun hgu hR
      (huv.trans hvb) htu huv hXP with hrep | ⟨x, hx, r, e, C, hto, htr, hrv, hPC, hlt⟩
  · exact window_justifies_or_parents_above_after' hrun hq hH hs hv hM4 hs₁ hvs hy hc htH hl
      hf hB hBl hks hh hT hh₀ hp hvb hrep
  have hnc := hp.noColl
  have hXPa := hXP X hXk (hXr.trans hT)
  have hCx : C ∈ (tr.state x r).fg.tree :=
    Healing.mem_tree_of_frame hrun hx hto.1 (toFG_live_fast_lock hto).1
  have hPx : P ∈ (tr.state x r).fg.tree := Healing.mem_of_honest_anc hrun hnc hx hPC hCx
  have hXx : X ∈ (tr.state x r).fg.tree := Healing.mem_of_honest_anc hrun hnc hx hXPa hPx
  have hle := Healing.h_le_of_store_anc (Compose.fg_reachable hrun.toLocalRun hx r)
    (Healing.store_anc_of_honest_anc hrun hnc hx hXPa hPx)
  rw [Healing.σ_eq_honest hrun hnc hx hy hXx hXk, hXh, hh] at hle
  have hhC : h < ((tr.state x r).fg.σ C.root).h := by omega
  refine Or.inl ⟨x, hx, r, e, C, hto, ?_, htr, hrv, hhC,
    fun X' hX' hX'r => (hXP X' hX' hX'r).trans hPC, fun s P' hP' hsv => ?_⟩
  · have hrh := hH.toHealedRecords.rh
    exact hp.cutZ_lt_of_high hx hCx (by omega)
  · exact crossed_parents_above hrun hnc hH hx hto htr hhC hP' (by linarith)

/-- **L5.4: the entry is justified on the parent's chain (r14 s5).** The premises of
`window_justifies_or_parents_above_unanimous''`. Conclusion: (A) for every held `X` of `y` with
root `T` (the entry block of `(h, T)`), every honest proposal `P` of a slot `s` with
`v + Δ ≤ t_s` and `s ≤ σ[X].ThSlot + δt` has an honest parent `Pr ⪰ X`, and at every honest
holder of `Pr` some held `D` with `X ⪯ D ⪯ Pr` justified `(h, T)` (`σ[D].h = h + 1`,
`σ[D].h_j = h`, `σ[D].J = T`) and, if `σ[X]` is bound, finalized the predecessor block
(`σ[D].F = σ[X].J`, `σ[D].h_F = σ[X].h_j`, L6.1 (i)); or (B) the window conclusion. -/
theorem window_entry_justified_or_window (hrun : GoldilocksRun proposer dg H tr)
    (hq : Hᶜ.ncard < sp.toParams.fg.q)
    {g ΔF v gR tH : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : Healed tr H proposer gR tH h₀ E)
    (hs : Healing.HSShared tr H dg g ΔF) (hv : gbar g ≤ v) {s₀ gM s₁ : Nat}
    (hM4 : ∀ s, s₀ ≤ s → ∃ s', s ≤ s' ∧ s' < s + gM ∧
      ∃ P, Healing.HonestProposalRun tr H proposer s' P)
    (hs₁ : s₀ ≤ s₁) (hvs : v + ΔF ≤ sp.ts s₁)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ℓ) (htH : tH ≤ tr.time k) {l}
    (hl : l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k))
    (hf : l.fast = true) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree)
    (hBl : B.root = l.block) (hks : tr.time k + sp.Δ ≤ sp.ts s₁) {h T : Nat}
    (hh : ((tr.state y k).fg.σ B.root).h = h) (hT : ((tr.state y k).fg.σ B.root).Th = T)
    (hh₀ : h₀ + 1 ≤ h) {ΔR a b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg gR ΔR a b) (hvb : v ≤ b)
    (hcatch : Healing.CatchRun tr H gR (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hPg : P.root ≠ sp.genesisRoot)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar gR + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (htu : tH ≤ sp.ts u) (huv : sp.ts u + 6 * sp.Δ ≤ v)
    (hXP : ∀ X ∈ (tr.state y k).fg.tree, X.root = T → Anc (tr.HonestBlocks H) X P) :
    (∀ X ∈ (tr.state y k).fg.tree, X.root = T →
      ∀ s P, Healing.HonestProposalRun tr H proposer s P → v + sp.Δ ≤ sp.ts s →
        s ≤ ((tr.state y k).fg.σ X.root).ThSlot + sp.toParams.fg.δt →
        ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) X Pr ∧
          ∀ w ∈ H, ∀ j, Pr ∈ (tr.state w j).fg.tree →
            ∃ D ∈ (tr.state w j).fg.tree, (tr.state w j).fg.Anc X D ∧
              (tr.state w j).fg.Anc D Pr ∧ ((tr.state w j).fg.σ D.root).h = h + 1 ∧
              ((tr.state w j).fg.σ D.root).hj = h ∧ ((tr.state w j).fg.σ D.root).J = T ∧
              (((tr.state y k).fg.σ X.root).bound →
                ((tr.state w j).fg.σ D.root).F = ((tr.state y k).fg.σ X.root).J ∧
                ((tr.state w j).fg.σ D.root).hF = ((tr.state y k).fg.σ X.root).hj)) ∨
    ∃ s', s₁ ≤ s' ∧ s' < s₁ + gM ∧ proposer s' ∈ H ∧ ∃ k X Pr,
      tr.ProposesAt (proposer s') k X ∧ X.slot = s' ∧ X.parent = some Pr.root ∧
      Pr ∈ (tr.state (proposer s') k).fg.tree ∧
      (h < ((tr.state (proposer s') k).fg.σ Pr.root).h ∨
        (((tr.post k).fg.σ X.root).hj = h ∧ ((tr.post k).fg.σ X.root).J = T ∧
          (((tr.state (proposer s') k).fg.σ Pr.root).bound →
            ((tr.post k).fg.σ X.root).hF =
              ((tr.state (proposer s') k).fg.σ Pr.root).hj))) := by
  have hBy : B ∈ (tr.state y k).fg.tree := Healing.mem_tree_of_frame hrun hy hc hB
  obtain ⟨X₀, hX₀, hX₀r, -, hX₀h, hX₀T⟩ := lock_entry_block hrun hy hBy
  rcases window_justifies_or_parents_above_unanimous_entry hrun hq hH hs hv hM4 hs₁ hvs hy hc htH
    hl hf hB hBl hks hh hT hh₀ hp hvb hcatch hP hslot hu hPg hun hgu hR htu huv hXP with
    ⟨-, -, -, -, C, -, -, -, -, -, hXC, hA⟩ | hW
  · refine Or.inl fun X hX hXr s P' hP' hsv hsδ => ?_
    obtain rfl : X = X₀ := eq_of_root_eq hrun hy hX hX₀ (hXr.trans (hX₀r.trans hT).symm)
    obtain ⟨Pr, hPr, hpar, hCPr, habove⟩ := hA s P' hP' hsv
    have hXPr := (hXC X hX hXr).trans hCPr
    refine ⟨Pr, hPr, hpar, hXPr, fun w hw j hPrj => ?_⟩
    have hnc := hp.noColl
    have hXw := Healing.mem_of_honest_anc hrun hnc hw hXPr hPrj
    have hσ := Healing.σ_eq_honest hrun hnc hy hw hX hXw
    obtain ⟨-, ℓ', -, -, -, -, -, -, -, hPs, -, -, j', -, hacc, -⟩ := hP'.2
    have hP'm : P' ∈ tr.HonestBlocks H := ⟨_, hP'.1, j', hp.acceptAt_mem hP'.1 hacc⟩
    have hPrs : Pr.slot < P'.slot := hp.honest_coherent.2 Pr hPr P' hP'm hpar
    have hXh : ((tr.state w j).fg.σ X.root).h = h := by rw [← hσ, hX₀h, hh]
    have hXT : ((tr.state w j).fg.σ X.root).Th = T := by rw [← hσ, hX₀T, hX₀r, hT]
    obtain ⟨D, hD, hXD, hDPr, h1, h2, h3, h4⟩ := Store.entry_justified_of_anc
      (Compose.fg_reachable hrun.toLocalRun hw j) hXw
      (Healing.store_anc_of_honest_anc hrun hnc hw hXPr hPrj)
      (by rw [hXh]; exact habove w hw j hPrj) (by rw [← hσ]; omega)
    rw [hXh] at h1 h2
    rw [hXT] at h3
    rw [← hσ] at h4
    exact ⟨D, hD, hXD, hDPr, h1, h2, h3, h4⟩
  · exact Or.inr hW

/-- **The entry slot of the lock's entry block.** For a held `X` of an honest `y` with root
`σ[B].Th` (the entry block of the held `B`), `σ[X].ThSlot = X.slot`. -/
theorem lock_entry_ThSlot (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {B X : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y k).fg.tree)
    (hX : X ∈ (tr.state y k).fg.tree) (hXr : X.root = ((tr.state y k).fg.σ B.root).Th) :
    ((tr.state y k).fg.σ X.root).ThSlot = X.slot ∧ ((tr.state y k).fg.σ X.root).Th = X.root := by
  obtain ⟨X₀, hX₀, hX₀r, -, -, hX₀T⟩ := lock_entry_block hrun hy hB
  obtain rfl : X = X₀ := eq_of_root_eq hrun hy hX hX₀ (hXr.trans hX₀r.symm)
  exact ⟨Healing.Store.ThSlot_eq_slot (Compose.fg_reachable hrun.toLocalRun hy k) hX hX₀T, hX₀T⟩

/-- **L5.4 with the M4 proposal (r14 s5).** `window_entry_justified_or_window` with the timing
premise discharged by M4: for a slot `s₂ ≥ s₀` with `v + Δ ≤ t_{s₂}`, in case (A), for every held
`X` of `y` with root `T` and `s₂ + gM ≤ X.slot + δt + 1`, some honest proposal `P` of a slot
`s ∈ [s₂, s₂ + gM)` has an honest parent `Pr ⪰ X` on whose chain, at every honest holder, a held
`D` with `X ⪯ D ⪯ Pr` justified `(h, T)` (and finalized the predecessor if `σ[X]` is bound). The
entry slot is `σ[X].ThSlot = X.slot` (`lock_entry_ThSlot`). -/
theorem window_entry_justified_M4 (hrun : GoldilocksRun proposer dg H tr)
    (hq : Hᶜ.ncard < sp.toParams.fg.q)
    {g ΔF v gR tH : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : Healed tr H proposer gR tH h₀ E)
    (hs : Healing.HSShared tr H dg g ΔF) (hv : gbar g ≤ v) {s₀ gM s₁ : Nat}
    (hM4 : ∀ s, s₀ ≤ s → ∃ s', s ≤ s' ∧ s' < s + gM ∧
      ∃ P, Healing.HonestProposalRun tr H proposer s' P)
    (hs₁ : s₀ ≤ s₁) (hvs : v + ΔF ≤ sp.ts s₁)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ℓ) (htH : tH ≤ tr.time k) {l}
    (hl : l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k))
    (hf : l.fast = true) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree)
    (hBl : B.root = l.block) (hks : tr.time k + sp.Δ ≤ sp.ts s₁) {h T : Nat}
    (hh : ((tr.state y k).fg.σ B.root).h = h) (hT : ((tr.state y k).fg.σ B.root).Th = T)
    (hh₀ : h₀ + 1 ≤ h) {ΔR a b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg gR ΔR a b) (hvb : v ≤ b)
    (hcatch : Healing.CatchRun tr H gR (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hPg : P.root ≠ sp.genesisRoot)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar gR + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (htu : tH ≤ sp.ts u) (huv : sp.ts u + 6 * sp.Δ ≤ v)
    (hXP : ∀ X ∈ (tr.state y k).fg.tree, X.root = T → Anc (tr.HonestBlocks H) X P)
    {s₂ : Nat} (hs₂ : s₀ ≤ s₂) (hvs₂ : v + sp.Δ ≤ sp.ts s₂) :
    (∀ X ∈ (tr.state y k).fg.tree, X.root = T → s₂ + gM ≤ X.slot + sp.toParams.fg.δt + 1 →
      ∃ s, s₂ ≤ s ∧ s < s₂ + gM ∧ ∃ P, Healing.HonestProposalRun tr H proposer s P ∧
        ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) X Pr ∧
          ∀ w ∈ H, ∀ j, Pr ∈ (tr.state w j).fg.tree →
            ∃ D ∈ (tr.state w j).fg.tree, (tr.state w j).fg.Anc X D ∧
              (tr.state w j).fg.Anc D Pr ∧ ((tr.state w j).fg.σ D.root).h = h + 1 ∧
              ((tr.state w j).fg.σ D.root).hj = h ∧ ((tr.state w j).fg.σ D.root).J = T ∧
              (((tr.state y k).fg.σ X.root).bound →
                ((tr.state w j).fg.σ D.root).F = ((tr.state y k).fg.σ X.root).J ∧
                ((tr.state w j).fg.σ D.root).hF = ((tr.state y k).fg.σ X.root).hj)) ∨
    ∃ s', s₁ ≤ s' ∧ s' < s₁ + gM ∧ proposer s' ∈ H ∧ ∃ k X Pr,
      tr.ProposesAt (proposer s') k X ∧ X.slot = s' ∧ X.parent = some Pr.root ∧
      Pr ∈ (tr.state (proposer s') k).fg.tree ∧
      (h < ((tr.state (proposer s') k).fg.σ Pr.root).h ∨
        (((tr.post k).fg.σ X.root).hj = h ∧ ((tr.post k).fg.σ X.root).J = T ∧
          (((tr.state (proposer s') k).fg.σ Pr.root).bound →
            ((tr.post k).fg.σ X.root).hF =
              ((tr.state (proposer s') k).fg.σ Pr.root).hj))) := by
  have hBy : B ∈ (tr.state y k).fg.tree := Healing.mem_tree_of_frame hrun hy hc hB
  rcases window_entry_justified_or_window hrun hq hH hs hv hM4 hs₁ hvs hy hc htH hl hf hB hBl
    hks hh hT hh₀ hp hvb hcatch hP hslot hu hPg hun hgu hR htu huv hXP with hA | hW
  · refine Or.inl fun X hX hXr hδ => ?_
    obtain ⟨s, hs₂s, hss, P', hP'⟩ := hM4 s₂ hs₂
    have hThs := (lock_entry_ThSlot hrun hy hBy hX (hXr.trans hT.symm)).1
    have hts : sp.ts s₂ ≤ sp.ts s := (SA.ts_le_iff sp).2 (by exact_mod_cast hs₂s)
    exact ⟨s, hs₂s, hss, P', hP', hA X hX hXr s P' hP' (hvs₂.trans hts) (by rw [hThs]; omega)⟩
  · exact Or.inr hW

/-- **L5.4 with the M4 proposal, the entry below the parent in the window case.**
`window_entry_justified_M4` with one more fact in case (B): every held `X'` of `y` with root
`T` has `X' ⪯ Pr` for the held parent `Pr` of the window proposal, in both arms (C3 of `Healed`:
the parent of an honest proposal of a slot `≥ s₁` extends the lock block `B`, and the entry
block of `B` is below `B`). -/
theorem window_entry_justified_M4_anc (hrun : GoldilocksRun proposer dg H tr)
    (hq : Hᶜ.ncard < sp.toParams.fg.q)
    {g ΔF v gR tH : Time} {h₀ : Nat}
    {E : Nat → SA.Blk sp.n (List (FG.Att sp.n))} (hH : Healed tr H proposer gR tH h₀ E)
    (hs : Healing.HSShared tr H dg g ΔF) (hv : gbar g ≤ v) {s₀ gM s₁ : Nat}
    (hM4 : ∀ s, s₀ ≤ s → ∃ s', s ≤ s' ∧ s' < s + gM ∧
      ∃ P, Healing.HonestProposalRun tr H proposer s' P)
    (hs₁ : s₀ ≤ s₁) (hvs : v + ΔF ≤ sp.ts s₁)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ℓ) (htH : tH ≤ tr.time k) {l}
    (hl : l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k))
    (hf : l.fast = true) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ℓ.frame.tree)
    (hBl : B.root = l.block) (hks : tr.time k + sp.Δ ≤ sp.ts s₁) {h T : Nat}
    (hh : ((tr.state y k).fg.σ B.root).h = h) (hT : ((tr.state y k).fg.σ B.root).Th = T)
    (hh₀ : h₀ + 1 ≤ h) {ΔR a b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg gR ΔR a b) (hvb : v ≤ b)
    (hcatch : Healing.CatchRun tr H gR (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hPg : P.root ≠ sp.genesisRoot)
    (hun : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar gR + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (htu : tH ≤ sp.ts u) (huv : sp.ts u + 6 * sp.Δ ≤ v)
    (hXP : ∀ X ∈ (tr.state y k).fg.tree, X.root = T → Anc (tr.HonestBlocks H) X P)
    {s₂ : Nat} (hs₂ : s₀ ≤ s₂) (hvs₂ : v + sp.Δ ≤ sp.ts s₂) :
    (∀ X ∈ (tr.state y k).fg.tree, X.root = T → s₂ + gM ≤ X.slot + sp.toParams.fg.δt + 1 →
      ∃ s, s₂ ≤ s ∧ s < s₂ + gM ∧ ∃ P, Healing.HonestProposalRun tr H proposer s P ∧
        ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) X Pr ∧
          ∀ w ∈ H, ∀ j, Pr ∈ (tr.state w j).fg.tree →
            ∃ D ∈ (tr.state w j).fg.tree, (tr.state w j).fg.Anc X D ∧
              (tr.state w j).fg.Anc D Pr ∧ ((tr.state w j).fg.σ D.root).h = h + 1 ∧
              ((tr.state w j).fg.σ D.root).hj = h ∧ ((tr.state w j).fg.σ D.root).J = T ∧
              (((tr.state y k).fg.σ X.root).bound →
                ((tr.state w j).fg.σ D.root).F = ((tr.state y k).fg.σ X.root).J ∧
                ((tr.state w j).fg.σ D.root).hF = ((tr.state y k).fg.σ X.root).hj)) ∨
    ∃ s', s₁ ≤ s' ∧ s' < s₁ + gM ∧ proposer s' ∈ H ∧ ∃ kp X Pr,
      tr.ProposesAt (proposer s') kp X ∧ X.slot = s' ∧ X.parent = some Pr.root ∧
      Pr ∈ (tr.state (proposer s') kp).fg.tree ∧
      (h < ((tr.state (proposer s') kp).fg.σ Pr.root).h ∨
        (((tr.post kp).fg.σ X.root).hj = h ∧ ((tr.post kp).fg.σ X.root).J = T ∧
          (((tr.state (proposer s') kp).fg.σ Pr.root).bound →
            ((tr.post kp).fg.σ X.root).hF =
              ((tr.state (proposer s') kp).fg.σ Pr.root).hj))) ∧
      ∀ X' ∈ (tr.state y k).fg.tree, X'.root = T → Anc (tr.HonestBlocks H) X' Pr := by
  have hnc := hp.noColl
  have hBy : B ∈ (tr.state y k).fg.tree := Healing.mem_tree_of_frame hrun hy hc hB
  obtain ⟨X₀, hX₀, hX₀r, hX₀B, -, -⟩ := lock_entry_block hrun hy hBy
  rcases window_entry_justified_M4 hrun hq hH hs hv hM4 hs₁ hvs hy hc htH hl hf hB hBl hks hh
    hT hh₀ hp hvb hcatch hP hslot hu hPg hun hgu hR htu huv hXP hs₂ hvs₂ with hA | hW
  · exact Or.inl hA
  obtain ⟨s', hs's, hs'g, hpH, k', Xp, Pr, hprop, hsl, hpar, hPr, harm⟩ := hW
  have hXr := Healing.honestProposalRun_of_proposesAt hrun hnc hpH
    (proposesAt_designated hrun hpH hprop) hprop rfl
  have hts : tr.time k + sp.Δ ≤ sp.ts Xp.slot :=
    hks.trans ((SA.ts_le_iff sp).2 (by rw [hsl]; exact_mod_cast hs's))
  obtain ⟨Pr', hPr'H, hpar', hanc⟩ := hH.c3 y hy k ℓ hc htH l hl hf B hB hBl Xp.slot Xp hXr hts
  obtain rfl : Pr' = Pr := (Compose.honest_blocks_coherent hrun.toLocalRun hnc).1 hPr'H
    ⟨_, hpH, k', hPr⟩ (Option.some.inj (hpar'.symm.trans hpar))
  refine Or.inr ⟨s', hs's, hs'g, hpH, k', Xp, Pr', hprop, hsl, hpar, hPr, harm,
    fun X' hX' hX'r => ?_⟩
  obtain rfl : X' = X₀ := eq_of_root_eq hrun hy hX' hX₀ (hX'r.trans (hX₀r.trans hT).symm)
  exact (Anc.mono (T := tr.HonestBlocks H) (fun _ hZ => ⟨y, hy, k, hZ⟩) hX₀B).trans hanc

end Refinement

end Consensus.Goldilocks

end
