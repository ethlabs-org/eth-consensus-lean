module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.State

public section

/-! # Goldilocks FG: one block of the state transition

The step facts that the chain-level proofs share: the chain fold one block at a time, the
counting of a block's attestations (it changes only `fin`, `prog` and `target`), and the
finality step (`bestFinal` picks the highest pending pair with a finality quorum; the prune
keeps the pairs above the new `h_F`). -/

namespace Consensus.Goldilocks.FG

/-- In a list of pairs strictly increasing in height, a height names at most one pair. -/
theorem eq_of_pairwise_fst_lt {l : List (Nat × Nat)} (hl : l.Pairwise (fun p r => p.1 < r.1))
    {p r : Nat × Nat} (hp : p ∈ l) (hr : r ∈ l) (h : p.1 = r.1) : p = r := by
  induction l with
  | nil => simp at hp
  | cons x l ih =>
    rw [List.pairwise_cons] at hl
    simp only [List.mem_cons] at hp hr
    rcases hp with rfl | hp <;> rcases hr with rfl | hr
    · rfl
    · exact absurd h (hl.1 r hr).ne
    · exact absurd h (hl.1 p hp).ne'
    · exact ih hl.2 hp hr

namespace ChainState

variable {n : Nat}

private theorem processAtt_eq (σ : ChainState n) (a : Att n) :
    ∃ fin prog target, σ.processAtt a = { σ with fin := fin, prog := prog, target := target } := by
  unfold processAtt
  dsimp only
  repeat' split
  all_goals exact ⟨_, _, _, rfl⟩

/-- Counting attestations changes only the finality, progress and target bits. -/
theorem foldl_processAtt_eq (σ : ChainState n) (atts : List (Att n)) :
    ∃ fin prog target, atts.foldl processAtt σ =
      { σ with fin := fin, prog := prog, target := target } := by
  induction atts generalizing σ with
  | nil => exact ⟨_, _, _, rfl⟩
  | cons a as ih =>
    obtain ⟨f, p, t, he⟩ := σ.processAtt_eq a
    obtain ⟨f', p', t', he'⟩ := ih (σ.processAtt a)
    rw [List.foldl_cons, he', he]
    exact ⟨f', p', t', rfl⟩

/-- Counting attestations keeps `Q_target ⊆ Q_prog`. -/
theorem foldl_processAtt_target_subset (σ : ChainState n) (atts : List (Att n))
    (h : σ.target ⊆ σ.prog) :
    (atts.foldl processAtt σ).target ⊆ (atts.foldl processAtt σ).prog := by
  induction atts generalizing σ with
  | nil => exact h
  | cons a as ih =>
    refine ih _ ?_
    unfold processAtt
    dsimp only
    repeat' split
    all_goals first
      | exact h
      | exact Finset.insert_subset_insert _ h
      | exact h.trans (Finset.subset_insert _ _)

end ChainState

namespace FGParams

variable (gp : FGParams)

theorem chainState_nil : gp.chainState [] = some (ChainState.init gp) := rfl

theorem chainState_append (c : List (FGBlock gp.n)) (B : FGBlock gp.n) :
    gp.chainState (c ++ [B]) = (gp.chainState c).bind (gp.stateTransition · B) := by
  simp only [chainState, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Induction over the chains that have a state, one block at a time. -/
theorem chainState_induction {P : List (FGBlock gp.n) → ChainState gp.n → Prop}
    (init : P [] (ChainState.init gp))
    (step : ∀ c σ B σ', gp.chainState c = some σ → P c σ → gp.stateTransition σ B = some σ' →
      P (c ++ [B]) σ')
    {c : List (FGBlock gp.n)} {σ : ChainState gp.n} (h : gp.chainState c = some σ) : P c σ := by
  induction c using List.reverseRecOn generalizing σ with
  | nil => cases h; exact init
  | append_singleton c B ih =>
    rw [chainState_append, Option.bind_eq_some_iff] at h
    obtain ⟨σ₀, h₀, hB⟩ := h
    exact step c σ₀ B σ h₀ (ih h₀) hB

theorem stateTransition_eq_some {σ σ' : ChainState gp.n} {B : FGBlock gp.n} :
    gp.stateTransition σ B = some σ' ↔
      (B.proposer = gp.proposer B.slot ∧ σ.s < B.slot ∧
        ∀ a ∈ B.atts, a.WellFormed ∧ σ.validAtt a) ∧
      gp.heightEvents
        { B.atts.foldl ChainState.processAtt { σ with s := B.slot } with L := B.root } = σ' := by
  unfold stateTransition
  split_ifs with h
  · exact ⟨fun e => ⟨h, Option.some.inj e⟩, fun ⟨_, e⟩ => congrArg some e⟩
  · exact ⟨fun e => (nomatch e), fun ⟨h', _⟩ => absurd h' h⟩

/-- One step of the fold of `bestFinal`: a pair with a quorum replaces a lower one. -/
private def pick (Q : Nat × Nat → Prop) [DecidablePred Q] (acc : Option (Nat × Nat))
    (p : Nat × Nat) : Option (Nat × Nat) :=
  if Q p then
    match acc with
    | none => some p
    | some r => if r.1 < p.1 then some p else some r
  else acc

section pick

variable {Q : Nat × Nat → Prop} [DecidablePred Q]

private theorem pick_eq_some {acc : Option (Nat × Nat)} {p r : Nat × Nat}
    (h : pick Q acc p = some r) : acc = some r ∨ (r = p ∧ Q p) := by
  unfold pick at h
  split_ifs at h with hq
  · rcases acc with _ | r₀
    · exact Or.inr ⟨(Option.some.inj h).symm, hq⟩
    · dsimp only at h; split_ifs at h <;> cases h <;> simp [hq]
  · exact Or.inl h

private theorem pick_ge {acc : Option (Nat × Nat)} {p : Nat × Nat} :
    (Q p → ∃ r, pick Q acc p = some r ∧ p.1 ≤ r.1) ∧
      ∀ r₀, acc = some r₀ → ∃ r, pick Q acc p = some r ∧ r₀.1 ≤ r.1 := by
  unfold pick
  refine ⟨fun hq => ?_, fun r₀ h => ?_⟩ <;> subst_vars
  · rcases acc with _ | r₀
    · simp [hq]
    · by_cases hlt : r₀.1 < p.1 <;> simp [hq, hlt]; omega
  · by_cases hq : Q p
    · by_cases hlt : r₀.1 < p.1 <;> simp [hq, hlt]; omega
    · simp [hq]

private theorem foldl_pick_eq_some {l : List (Nat × Nat)} {acc : Option (Nat × Nat)}
    {r : Nat × Nat} (h : l.foldl (pick Q) acc = some r) :
    (acc = some r ∨ (r ∈ l ∧ Q r)) ∧ (∀ p ∈ l, Q p → p.1 ≤ r.1) ∧
      ∀ r₀, acc = some r₀ → r₀.1 ≤ r.1 := by
  induction l generalizing acc with
  | nil => simp_all
  | cons p l ih =>
    obtain ⟨h1, h2, h3⟩ := ih h
    refine ⟨?_, ?_, fun r₀ h₀ => ?_⟩
    · rcases h1 with h1 | h1
      · rcases pick_eq_some h1 with h1 | ⟨rfl, hq⟩
        · exact Or.inl h1
        · exact Or.inr ⟨List.mem_cons_self, hq⟩
      · exact Or.inr ⟨List.mem_cons_of_mem _ h1.1, h1.2⟩
    · simp only [List.mem_cons, forall_eq_or_imp]
      refine ⟨fun hq => ?_, h2⟩
      obtain ⟨r', hr', hle⟩ := pick_ge.1 hq
      exact hle.trans (h3 r' hr')
    · obtain ⟨r', hr', hle⟩ := pick_ge (Q := Q) (p := p).2 r₀ h₀
      exact hle.trans (h3 r' hr')

private theorem foldl_pick_ne_none {l : List (Nat × Nat)} {r₀ : Nat × Nat} :
    l.foldl (pick Q) (some r₀) ≠ none := by
  induction l generalizing r₀ with
  | nil => simp
  | cons p l ih =>
    obtain ⟨r, hr, -⟩ := pick_ge (Q := Q) (p := p).2 r₀ rfl
    rw [List.foldl_cons, hr]
    exact ih

private theorem foldl_pick_eq_none {l : List (Nat × Nat)} {acc : Option (Nat × Nat)}
    (h : l.foldl (pick Q) acc = none) : ∀ p ∈ l, ¬ Q p := by
  induction l generalizing acc with
  | nil => simp
  | cons p l ih =>
    simp only [List.mem_cons, forall_eq_or_imp]
    refine ⟨fun hq => ?_, ih h⟩
    obtain ⟨r, hr, -⟩ := pick_ge (Q := Q) (acc := acc).1 hq
    rw [List.foldl_cons, hr] at h
    exact foldl_pick_ne_none h

end pick

private theorem bestFinal_eq_foldl (σ : ChainState gp.n) :
    gp.bestFinal σ = σ.pending.foldl (pick (fun p => gp.q ≤ (σ.fin p.1).card)) none := rfl

/-- `bestFinal` picks a pending pair with a finality quorum, of the greatest height among
them. -/
theorem bestFinal_eq_some {σ : ChainState gp.n} {r : Nat × Nat} (h : gp.bestFinal σ = some r) :
    r ∈ σ.pending ∧ gp.q ≤ (σ.fin r.1).card ∧
      ∀ p ∈ σ.pending, gp.q ≤ (σ.fin p.1).card → p.1 ≤ r.1 := by
  rw [bestFinal_eq_foldl] at h
  obtain ⟨h1, h2, -⟩ := foldl_pick_eq_some h
  simp only [reduceCtorEq, false_or] at h1
  exact ⟨h1.1, h1.2, h2⟩

/-- `bestFinal` is none only when no pending pair has a finality quorum. -/
theorem bestFinal_eq_none {σ : ChainState gp.n} (h : gp.bestFinal σ = none) :
    ∀ p ∈ σ.pending, (σ.fin p.1).card < gp.q := by
  rw [bestFinal_eq_foldl] at h
  simpa using foldl_pick_eq_none h

/-- The finality step moves `(F, h_F)` to a pending pair with a finality quorum or keeps it,
and the prune keeps the pairs above the new `h_F`. -/
theorem finalizePrune_eq (σ : ChainState gp.n) :
    ∃ F hF, gp.finalizePrune σ =
        { σ with F := F, hF := hF, pending := σ.pending.filter (fun p => hF < p.1) } ∧
      ((F = σ.F ∧ hF = σ.hF) ∨ ((hF, F) ∈ σ.pending ∧ gp.q ≤ (σ.fin hF).card)) := by
  unfold finalizePrune
  cases hb : gp.bestFinal σ with
  | none => exact ⟨σ.F, σ.hF, rfl, Or.inl ⟨rfl, rfl⟩⟩
  | some r =>
    obtain ⟨h1, h2, -⟩ := gp.bestFinal_eq_some hb
    exact ⟨r.2, r.1, rfl, Or.inr ⟨h1, h2⟩⟩

/-- The height events: the finality step and the prune give `σ₁`, which then justifies
(append the entry, keep the newest `K_W` pairs, advance), times out (advance) or stays. -/
theorem heightEvents_cases (σ : ChainState gp.n) :
    ∃ F hF σ₁, σ₁ = { σ with F := F, hF := hF, pending := σ.pending.filter (fun p => hF < p.1) } ∧
      ((F = σ.F ∧ hF = σ.hF) ∨ ((hF, F) ∈ σ.pending ∧ gp.q ≤ (σ.fin hF).card)) ∧
      ((gp.justifies σ₁ ∧ gp.heightEvents σ = ChainState.advance
          { σ₁ with J := σ₁.Th, hj := σ₁.h,
                    pending := (σ₁.pending ++ [(σ₁.h, σ₁.Th)]).drop
                      ((σ₁.pending ++ [(σ₁.h, σ₁.Th)]).length - KW),
                    fin := Function.update σ₁.fin σ₁.h ∅ }) ∨
        (¬ gp.justifies σ₁ ∧ gp.timesOut σ₁ ∧ gp.heightEvents σ = ChainState.advance σ₁) ∨
        (¬ gp.justifies σ₁ ∧ ¬ gp.timesOut σ₁ ∧ gp.heightEvents σ = σ₁)) := by
  obtain ⟨F, hF, he, hc⟩ := gp.finalizePrune_eq σ
  refine ⟨F, hF, _, rfl, hc, ?_⟩
  unfold heightEvents
  rw [he]
  dsimp only
  split_ifs with h₁ h₂
  · exact Or.inl ⟨h₁, rfl⟩
  · exact Or.inr (Or.inl ⟨h₁, h₂, rfl⟩)
  · exact Or.inr (Or.inr ⟨h₁, h₂, rfl⟩)

end FGParams

end Consensus.Goldilocks.FG

end
