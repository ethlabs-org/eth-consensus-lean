module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGSafety
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Transition

public section

/-! # Goldilocks FG: chain-state invariants (G0.2, G0.7 (c), G0.9)

The invariants of every chain state that a chain reaches (G0.2 (a), (d), (e) and
`Q_target ⊆ Q_prog`), by induction over the chain with one block at a time; then the facts
about one accepted block: the height step and entry constancy (G0.2 (b), (h), (i)), gated
consumption (G0.7 (c)) and retention (G0.9 (a), (b)). -/

namespace Consensus.Goldilocks.FG

namespace FGParams

variable (gp : FGParams)

/-- The invariants of `ChainInvariants` for one chain state. -/
private structure Good (σ : ChainState gp.n) : Prop where
  one_le_h : 1 ≤ σ.h
  hF_le_hj : σ.hF ≤ σ.hj
  hj_lt_h : σ.hj < σ.h
  J_eq : σ.hj = 0 → σ.J = gp.genesis
  F_eq : σ.hF = 0 → σ.F = gp.genesis
  length_le : σ.pending.length ≤ KW
  pairwise : σ.pending.Pairwise (fun p r => p.1 < r.1)
  mem_pending : ∀ p ∈ σ.pending, σ.hF < p.1 ∧ p.1 ≤ σ.hj
  getLast : σ.hF < σ.hj → σ.pending.getLast? = some (σ.hj, σ.J)
  target_subset : σ.target ⊆ σ.prog

private theorem getLast?_filter {l : List (Nat × Nat)} {x : Nat × Nat} {P : Nat × Nat → Bool}
    (h : l.getLast? = some x) (hx : P x) : (l.filter P).getLast? = some x := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 h
  simp [List.filter_append, hx]

private theorem good_finalize {σ : ChainState gp.n} (hG : gp.Good σ) {F hF : Nat}
    (hc : (F = σ.F ∧ hF = σ.hF) ∨ ((hF, F) ∈ σ.pending ∧ gp.q ≤ (σ.fin hF).card)) :
    σ.hF ≤ hF ∧
      gp.Good { σ with F := F, hF := hF, pending := σ.pending.filter (fun p => hF < p.1) } := by
  have hle : σ.hF ≤ hF ∧ hF ≤ σ.hj ∧ (hF = 0 → F = gp.genesis) := by
    rcases hc with ⟨rfl, rfl⟩ | ⟨hm, -⟩
    · exact ⟨le_rfl, hG.hF_le_hj, hG.F_eq⟩
    · have := hG.mem_pending _ hm
      exact ⟨this.1.le, this.2, by omega⟩
  refine ⟨hle.1, hG.one_le_h, hle.2.1, hG.hj_lt_h, hG.J_eq, hle.2.2,
    (List.length_filter_le _ _).trans hG.length_le, hG.pairwise.filter _, ?_, ?_, hG.target_subset⟩
  · intro p hp
    simp only [List.mem_filter, decide_eq_true_eq] at hp
    exact ⟨hp.2, (hG.mem_pending p hp.1).2⟩
  · intro h
    dsimp only at h ⊢
    exact getLast?_filter (hG.getLast (by omega)) (by simpa using h)

/-- One accepted block: after counting, the finality step and the prune give `σ₁` (same
height, entry and justification; `h_F` does not decrease; the latest block is `B`), which then
justifies, times out or stays. -/
private theorem step_cases {σ σ' : ChainState gp.n} {B : FGBlock gp.n} (hG : gp.Good σ)
    (h : gp.stateTransition σ B = some σ') :
    ∃ σ₁ : ChainState gp.n, gp.Good σ₁ ∧ σ.hF ≤ σ₁.hF ∧ σ₁.h = σ.h ∧ σ₁.Th = σ.Th ∧
      σ₁.J = σ.J ∧ σ₁.hj = σ.hj ∧ σ₁.L = B.root ∧
      σ₁.pending = σ.pending.filter (fun p => σ₁.hF < p.1) ∧
      ((gp.justifies σ₁ ∧ σ' = ChainState.advance
          { σ₁ with J := σ₁.Th, hj := σ₁.h,
                    pending := (σ₁.pending ++ [(σ₁.h, σ₁.Th)]).drop
                      ((σ₁.pending ++ [(σ₁.h, σ₁.Th)]).length - KW),
                    fin := Function.update σ₁.fin σ₁.h ∅ }) ∨
        (¬ gp.justifies σ₁ ∧ gp.timesOut σ₁ ∧ σ' = ChainState.advance σ₁) ∨
        (¬ gp.justifies σ₁ ∧ ¬ gp.timesOut σ₁ ∧ σ' = σ₁)) := by
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  have hsub := ChainState.foldl_processAtt_target_subset { σ with s := B.slot } B.atts
    hG.target_subset
  obtain ⟨f, p, t, he⟩ := ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he] at hsub ⊢
  obtain ⟨F, hF, σ₁, rfl, hc, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  have hG₀ : gp.Good { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t } :=
    ⟨hG.one_le_h, hG.hF_le_hj, hG.hj_lt_h, hG.J_eq, hG.F_eq, hG.length_le, hG.pairwise,
      hG.mem_pending, hG.getLast, hsub⟩
  obtain ⟨hle, h₁⟩ := gp.good_finalize hG₀ hc
  refine ⟨_, h₁, hle, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  rcases hcase with ⟨h1, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, h2, he⟩
  · exact Or.inl ⟨h1, he⟩
  · exact Or.inr (Or.inl ⟨h1, h2, he⟩)
  · exact Or.inr (Or.inr ⟨h1, h2, he⟩)

private theorem good_step {σ σ' : ChainState gp.n} {B : FGBlock gp.n} (hG : gp.Good σ)
    (h : gp.stateTransition σ B = some σ') : gp.Good σ' := by
  obtain ⟨σ₁, h₁, -, -, -, -, -, -, -, hcase⟩ := gp.step_cases hG h
  have := h₁.one_le_h; have := h₁.hj_lt_h; have := h₁.hF_le_hj
  rcases hcase with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
  · refine ⟨by simp [ChainState.advance], ?_, ?_, ?_, h₁.F_eq, ?_, ?_, ?_, ?_,
    by simp [ChainState.advance]⟩ <;>
      simp only [ChainState.advance]
    · omega
    · omega
    · omega
    · simp [KW]; omega
    · refine List.Pairwise.sublist (List.drop_sublist _ _) ?_
      refine List.pairwise_append.2 ⟨h₁.pairwise, by simp, fun p hp r hr => ?_⟩
      simp only [List.mem_singleton] at hr
      subst hr
      have := h₁.mem_pending p hp; omega
    · intro p hp
      rcases List.mem_append.1 (List.mem_of_mem_drop hp) with hp | hp
      · have := h₁.mem_pending p hp; omega
      · simp only [List.mem_singleton] at hp
        subst hp
        simp only; omega
    · intro _
      rw [List.getLast?_drop]
      simp [KW]
      omega
  · exact ⟨by simp only [ChainState.advance]; omega, h₁.hF_le_hj,
      by simp only [ChainState.advance]; omega,
      h₁.J_eq, h₁.F_eq, h₁.length_le, h₁.pairwise, h₁.mem_pending, h₁.getLast,
      by simp [ChainState.advance]⟩
  · exact h₁

private theorem good {c : List (FGBlock gp.n)} {σ : ChainState gp.n}
    (h : gp.chainState c = some σ) : gp.Good σ :=
  gp.chainState_induction (P := fun _ σ => gp.Good σ)
    ⟨le_rfl, le_rfl, Nat.one_pos, fun _ => rfl, fun _ => rfl, by simp [ChainState.init, KW],
      List.Pairwise.nil, by simp [ChainState.init], by simp [ChainState.init],
      by simp [ChainState.init]⟩
    (fun _ _ _ _ _ hG hB => gp.good_step hG hB) h

end FGParams

variable (gp : FGParams)

/-- **G0.2 (a), (c) part, (d), (e).** -/
theorem chain_invariants : ChainInvariants gp := fun _ _ h =>
  let hG := gp.good h
  ⟨hG.one_le_h, hG.hF_le_hj, hG.hj_lt_h, hG.J_eq, hG.F_eq, hG.length_le, hG.pairwise,
    hG.mem_pending, hG.getLast, hG.target_subset⟩

/-- **G0.2 (b), (h), (i).** -/
theorem height_step : HeightStep gp := by
  intro c σ σ' B hc h
  have hG := gp.good hc
  have hG' : gp.Good σ' := gp.good_step hG h
  obtain ⟨σ₁, h₁, hle, hh, hTh, hJ, hj, hL, -, hcase⟩ := gp.step_cases hG h
  have := hG.one_le_h; have := hG.hj_lt_h; have := h₁.hF_le_hj
  rcases hcase with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
  · dsimp only [ChainState.advance, ChainState.previousHeightJustified] at hG' ⊢
    refine ⟨by omega, by omega, hle, by omega, fun _ => ⟨hL, by omega, fun _ => ?_⟩⟩
    exact ⟨by omega, hG'.getLast (by dsimp only; omega)⟩
  · dsimp only [ChainState.advance, ChainState.previousHeightJustified]
    refine ⟨by omega, by omega, hle, by omega, fun _ => ⟨hL, by omega, fun hb => by omega⟩⟩
  · exact ⟨Or.inl hh, hj.ge, hle, fun _ => ⟨hTh, hJ, hj⟩, by omega⟩

/-- **G0.7 (c).** -/
theorem gated_consumption : GatedConsumption gp := by
  intro c σ hc
  have hq : 1 ≤ gp.q := by have := gp.hn; simp only [FGParams.q]; omega
  refine gp.chainState_induction (P := fun _ σ => gp.q ≤ σ.target.card →
    σ.previousHeightJustified ∧ (σ.hj, σ.J) ∈ σ.pending ∧ σ.hF < σ.hj ∧ σ.s < σ.ThSlot + gp.δt)
    (fun h => by simp [ChainState.init] at h; omega) (fun c σ B σ' hc _ hB => ?_) hc
  obtain ⟨σ₁, h₁, -, -, -, -, -, -, -, hcase⟩ := gp.step_cases (gp.good hc) hB
  intro ht
  rcases hcase with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨hJ, hT, rfl⟩
  · simp [ChainState.advance] at ht; omega
  · simp [ChainState.advance] at ht; omega
  · simp only [FGParams.justifies, FGParams.timesOut, not_and, not_or, not_not, not_le] at hJ hT
    obtain ⟨hb, hne⟩ := hJ ht
    have hlt : σ'.hF < σ'.hj := lt_of_le_of_ne h₁.hF_le_hj hne
    exact ⟨hb, List.mem_of_getLast? (h₁.getLast hlt), hlt,
      hT (ht.trans (Finset.card_le_card h₁.target_subset))⟩

/-- **G0.9 (a).** -/
theorem retention : Retention gp := by
  intro c σ σ' B hc h _ hh hlt
  have hG := gp.good hc
  obtain ⟨σ₁, -, hle, hh₁, -, -, hj, -, hp, hcase⟩ := gp.step_cases hG h
  rcases hcase with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
  · simp only [ChainState.advance] at hh; omega
  · simp only [ChainState.advance] at hh; omega
  · rw [hp, List.mem_filter]
    exact ⟨List.mem_of_getLast? (hG.getLast (by omega)), by simpa [hj] using hlt⟩

/-- **G0.9 (b).** -/
theorem retention_through_append : RetentionThroughAppend gp := by
  intro c σ σ' B P hc h hP hlt
  obtain ⟨σ₁, -, -, -, -, -, -, -, hp, hcase⟩ := gp.step_cases (gp.good hc) h
  have hP₁ : σ₁.pending.getLast? = some P := hp ▸ FGParams.getLast?_filter hP (by
    rcases hcase with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simpa [ChainState.advance] using hlt)
  rcases hcase with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
  · obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 hP₁
    simp [ChainState.advance, hys, FGParams.KW]
  · exact List.mem_of_getLast? hP₁
  · exact List.mem_of_getLast? hP₁

end Consensus.Goldilocks.FG

end
