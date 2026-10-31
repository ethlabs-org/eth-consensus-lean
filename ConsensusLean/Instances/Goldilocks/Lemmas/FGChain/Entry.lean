module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Transition

public section

/-! # Goldilocks FG: the blocks a chain state names

On one chain (G0.2 (c), (h) without the entry blocks of `M₁`): an accepted block becomes the
state's latest block, at its slot; the entry, the justification and the finalization of a
chain's state are roots of the chain; and the entry of the current height is the last block of
a prefix whose state already has that height and entry. -/

namespace Consensus.Goldilocks.FG

namespace FGParams

variable (gp : FGParams)

/-- The height events keep the latest block and its slot; they keep the height and entry or
enter a new height with the latest block. The entry, justification, finalization and pending
pairs stay among the old entry, justification, finalization, latest block and pending pairs. -/
private theorem heightEvents_fields (σ : ChainState gp.n) :
    (gp.heightEvents σ).L = σ.L ∧ (gp.heightEvents σ).s = σ.s ∧
      (((gp.heightEvents σ).h = σ.h ∧ (gp.heightEvents σ).Th = σ.Th) ∨
        (gp.heightEvents σ).Th = σ.L) ∧
      ∀ R : Nat → Prop, R σ.Th → R σ.J → R σ.F → R σ.L → (∀ p ∈ σ.pending, R p.2) →
        R (gp.heightEvents σ).Th ∧ R (gp.heightEvents σ).J ∧ R (gp.heightEvents σ).F ∧
          ∀ p ∈ (gp.heightEvents σ).pending, R p.2 := by
  obtain ⟨F, hF, σ₁, rfl, hc, hcase⟩ := gp.heightEvents_cases σ
  have hF' : ∀ R : Nat → Prop, R σ.F → (∀ p ∈ σ.pending, R p.2) → R F := by
    intro R h1 h2
    rcases hc with ⟨rfl, -⟩ | ⟨hm, -⟩
    · exact h1
    · exact h2 _ hm
  have hp' : ∀ p ∈ σ.pending.filter (fun p => hF < p.1), p ∈ σ.pending :=
    fun p hp => List.mem_of_mem_filter hp
  rcases hcase with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ <;> rw [he] <;>
    dsimp only [ChainState.advance]
  · refine ⟨rfl, rfl, Or.inr rfl, fun R hTh hJ hFR hL hp => ⟨hL, hTh, hF' R hFR hp, ?_⟩⟩
    intro q hq
    rcases List.mem_append.1 (List.mem_of_mem_drop hq) with hq | hq
    · exact hp q (hp' q hq)
    · simp only [List.mem_singleton] at hq
      subst hq
      exact hTh
  · exact ⟨rfl, rfl, Or.inr rfl, fun R hTh hJ hFR hL hp =>
      ⟨hL, hJ, hF' R hFR hp, fun q hq => hp q (hp' q hq)⟩⟩
  · exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩, fun R hTh hJ hFR hL hp =>
      ⟨hTh, hJ, hF' R hFR hp, fun q hq => hp q (hp' q hq)⟩⟩

/-- An accepted block's state: the counted state with the block as latest block at its slot,
through the height events. -/
private theorem stateTransition_fields {σ σ' : ChainState gp.n} {B : FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') :
    σ.s < B.slot ∧ ∃ σ₀ : ChainState gp.n, σ₀.L = B.root ∧ σ₀.s = B.slot ∧ σ₀.h = σ.h ∧
      σ₀.Th = σ.Th ∧ σ₀.J = σ.J ∧ σ₀.F = σ.F ∧ σ₀.pending = σ.pending ∧
      gp.heightEvents σ₀ = σ' := by
  obtain ⟨⟨hs, -⟩, he⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, hf⟩ := ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [hf] at he
  exact ⟨hs, { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, he⟩

/-- An accepted block is the latest block of its state, at its slot, above its parent's slot. -/
theorem stateTransition_L_s {σ σ' : ChainState gp.n} {B : FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') : σ'.L = B.root ∧ σ'.s = B.slot ∧ σ.s < B.slot := by
  obtain ⟨hs, σ₀, hL, hs₀, -, -, -, -, -, rfl⟩ := gp.stateTransition_fields h
  obtain ⟨h1, h2, -⟩ := gp.heightEvents_fields σ₀
  exact ⟨h1.trans hL, h2.trans hs₀, hs⟩

/-- The entry, the justification and the finalization of a chain's state are roots of the
chain. -/
theorem mem_roots_of_chainState {c : List (FGBlock gp.n)} {σ : ChainState gp.n}
    (h : gp.chainState c = some σ) : σ.Th ∈ gp.roots c ∧ σ.J ∈ gp.roots c ∧ σ.F ∈ gp.roots c := by
  suffices σ.Th ∈ gp.roots c ∧ σ.J ∈ gp.roots c ∧ σ.F ∈ gp.roots c ∧ σ.L ∈ gp.roots c ∧
      ∀ p ∈ σ.pending, p.2 ∈ gp.roots c from ⟨this.1, this.2.1, this.2.2.1⟩
  refine gp.chainState_induction (P := fun c σ => σ.Th ∈ gp.roots c ∧ σ.J ∈ gp.roots c ∧
    σ.F ∈ gp.roots c ∧ σ.L ∈ gp.roots c ∧ ∀ p ∈ σ.pending, p.2 ∈ gp.roots c)
    (by simp [ChainState.init, roots]) (fun c σ B σ' _ ih hB => ?_) h
  obtain ⟨hTh, hJ, hF, hL, hp⟩ := ih
  have lift : ∀ r ∈ gp.roots c, r ∈ gp.roots (c ++ [B]) := fun r hr => by
    simp only [roots, List.map_append, List.map_cons, List.map_nil, List.mem_cons,
      List.mem_append] at hr ⊢
    tauto
  have hB' : B.root ∈ gp.roots (c ++ [B]) := by simp [roots]
  obtain ⟨-, σ₀, hL₀, -, -, hTh₀, hJ₀, hF₀, hp₀, rfl⟩ := gp.stateTransition_fields hB
  obtain ⟨hL', -, -, hR⟩ := gp.heightEvents_fields σ₀
  obtain ⟨h1, h2, h3, h4⟩ := hR (· ∈ gp.roots (c ++ [B])) (hTh₀ ▸ lift _ hTh) (hJ₀ ▸ lift _ hJ)
    (hF₀ ▸ lift _ hF) (hL₀ ▸ hB') (hp₀ ▸ fun p hq => lift _ (hp p hq))
  exact ⟨h1, h2, h3, hL' ▸ hL₀ ▸ hB', h4⟩

/-- The entry of a chain's height is the last root of a prefix whose state has the same height
and entry. -/
theorem exists_entry_prefix {c : List (FGBlock gp.n)} {σ : ChainState gp.n}
    (h : gp.chainState c = some σ) :
    ∃ c', c' <+: c ∧ ∃ σ', gp.chainState c' = some σ' ∧ σ'.h = σ.h ∧ σ'.Th = σ.Th ∧
      (gp.roots c').getLast? = some σ.Th := by
  refine gp.chainState_induction (P := fun c σ => ∃ c', c' <+: c ∧ ∃ σ',
    gp.chainState c' = some σ' ∧ σ'.h = σ.h ∧ σ'.Th = σ.Th ∧ (gp.roots c').getLast? = some σ.Th)
    ⟨[], List.prefix_rfl, _, gp.chainState_nil, rfl, rfl, by simp [roots, ChainState.init]⟩
    (fun c σ B σ' hc ih hB => ?_) h
  obtain ⟨-, σ₀, hL₀, -, hh₀, hTh₀, -, -, -, he⟩ := gp.stateTransition_fields hB
  obtain ⟨-, -, hcase, -⟩ := gp.heightEvents_fields σ₀
  rw [he] at hcase
  rcases hcase with ⟨hh, hTh⟩ | hTh
  · obtain ⟨c', hpre, σ'', h1, h2, h3, h4⟩ := ih
    exact ⟨c', hpre.trans (List.prefix_append _ _), σ'', h1, h2.trans (hh.trans hh₀).symm,
      h3.trans (hTh.trans hTh₀).symm, h4.trans (by rw [hTh, hTh₀])⟩
  · refine ⟨c ++ [B], List.prefix_rfl, σ', by rw [gp.chainState_append, hc]; exact hB, rfl, rfl,
      ?_⟩
    simp only [roots, hTh, hL₀, List.map_append, List.map_cons, List.map_nil, ← List.cons_append,
      List.getLast?_concat]

end FGParams

end Consensus.Goldilocks.FG

end
