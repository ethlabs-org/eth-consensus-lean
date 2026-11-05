module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Invariants

public section

/-! # Goldilocks FG: step facts for liveness

Two facts of one accepted block that the liveness argument uses:
* a block that enters a new height without justifying the old one (a timeout) has a slot at
  least `δt` after the entry of the old height;
* a block that justifies a height whose previous height is justified has finalized its predecessor:
  the loose-BJ gate reads the finalization of the same block;
* at a height whose previous height is justified the predecessor is pending or finalized,
  and a step that enters a height whose previous height is not justified is a timeout, so its slot
  is at least `δt` after the old entry;
* a client whose record is clean at the entry's height sends a target for that entry, not a
  timeout. -/

namespace Consensus.Goldilocks.FG

namespace FGParams

variable (gp : FGParams)

/-- An accepted block's state is the height events of the counted state: the parent's state at
the block's slot, with the block as latest block; counting changes only the bits. -/
private theorem stateTransition_counted {σ σ' : ChainState gp.n} {B : FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') :
    ∃ σ₀ : ChainState gp.n, σ₀.s = B.slot ∧ σ₀.h = σ.h ∧ σ₀.Th = σ.Th ∧
      σ₀.ThSlot = σ.ThSlot ∧ σ₀.hj = σ.hj ∧ gp.heightEvents σ₀ = σ' := by
  obtain ⟨-, he⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, hf⟩ := ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [hf] at he
  exact ⟨{ σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }, rfl, rfl, rfl,
    rfl, rfl, he⟩

/-- **Timeout slot (lemma T).** A block that enters the next height without
justifying the current one has a slot at least `δt` after the slot of the current entry. -/
theorem timeout_step_slot {σ σ' : ChainState gp.n} {B : FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') (hh : σ'.h = σ.h + 1) (hj : σ'.hj ≠ σ.h) :
    σ.ThSlot + gp.δt ≤ B.slot := by
  obtain ⟨σ₀, hs, hh₀, -, hT, -, rfl⟩ := gp.stateTransition_counted h
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases σ₀
  rcases hcase with ⟨-, he⟩ | ⟨-, ⟨-, ht⟩, -⟩ | ⟨-, -, he⟩
  · rw [he] at hj
    exact absurd (by simp [ChainState.advance, hh₀]) hj
  · simpa [hs, hT] using ht
  · rw [he] at hh
    simp [hh₀] at hh

/-- **A justification at a height whose previous height is justified finalizes its predecessor.** A
block that justifies the current height of a state whose previous height is justified has finalized
the predecessor height `h_j` in its own finality step. -/
theorem previousHeightJustified_justify_finalizes {σ σ' : ChainState gp.n} {B : FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') (hb : σ.previousHeightJustified) (hj : σ'.hj = σ.h) :
    σ'.hF = σ.hj := by
  obtain ⟨σ₀, -, hh₀, -, -, hj₀, rfl⟩ := gp.stateTransition_counted h
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases σ₀
  have hb' : (0 < σ₀.hj ∧ σ₀.hj + 1 = σ₀.h) := by
    rw [hh₀, hj₀]; exact hb
  rcases hcase with ⟨⟨-, hg⟩, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩
  · rw [he]
    rcases hg with hnb | hfe
    · exact absurd hb' hnb
    · simpa [ChainState.advance, hj₀] using hfe
  · rw [he] at hj
    simp [ChainState.advance] at hj
    omega
  · rw [he] at hj
    simp at hj
    omega

/-- **Predecessor pending or finalized (W2).** On a chain, at a height whose previous height
is justified the predecessor pair `(h_j, J)` is pending, or `h_j` is finalized. -/
theorem pred_pending_or_finalized {c : List (FGBlock gp.n)} {σ : ChainState gp.n}
    (hc : gp.chainState c = some σ) : (σ.hj, σ.J) ∈ σ.pending ∨ σ.hF = σ.hj := by
  obtain ⟨-, hle, -, -, -, -, -, -, hlast, -⟩ := chain_invariants gp c σ hc
  rcases Nat.lt_or_ge σ.hF σ.hj with hlt | hge
  · exact Or.inl (List.mem_of_getLast? (hlast hlt))
  · exact Or.inr (le_antisymm hle hge)

/-- **Crossing by progress (L3.3a; the window tables).** A block whose counted state has a
progress quorum, at a slot at least `δt` after the entry, enters the next height: it justifies
or times out. -/
theorem cross_of_progress {σ σ' : ChainState gp.n} {B : FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ')
    (hq : gp.q ≤ (B.atts.foldl ChainState.processAtt { σ with s := B.slot }).prog.card)
    (hage : σ.ThSlot + gp.δt ≤ B.slot) : σ'.h = σ.h + 1 := by
  obtain ⟨-, he⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, hf⟩ := ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [hf] at he hq
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, fin := f, prog := p, target := t, L := B.root }
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, hto, -⟩
  · rw [he'] at he; subst he; rfl
  · rw [he'] at he; subst he; rfl
  · exact absurd ⟨hq, hage⟩ hto

/-- **An entry whose previous height is not justified justifies with a target quorum (window
tables).** A block whose counted state has a target quorum, at a height whose previous height is not
justified, justifies the entry: the loose-BJ gate does not apply. -/
theorem justify_of_target_previousHeightNotJustified {σ σ' : ChainState gp.n} {B : FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ')
    (hq : gp.q ≤ (B.atts.foldl ChainState.processAtt { σ with s := B.slot }).target.card)
    (hnb : ¬ σ.previousHeightJustified) : σ'.hj = σ.h ∧ σ'.J = σ.Th := by
  obtain ⟨-, he⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, hf⟩ := ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [hf] at he hq
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, fin := f, prog := p, target := t, L := B.root }
  rcases hcase with ⟨-, he'⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩
  · rw [he'] at he; subst he; exact ⟨rfl, rfl⟩
  · exact absurd ⟨hq, Or.inl (by simpa [ChainState.previousHeightJustified] using hnb)⟩ hn
  · exact absurd ⟨hq, Or.inl (by simpa [ChainState.previousHeightJustified] using hnb)⟩ hn

/-- **An early crossing justifies.** A block that enters the next height
at a slot before `ThSlot + δt` justifies the old height (it is no timeout, lemma T), and at a
height whose previous height is justified it has finalized the predecessor (the loose-BJ gate). -/
theorem early_cross_justifies {σ σ' : ChainState gp.n} {B : FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') (hh : σ'.h = σ.h + 1)
    (hs : B.slot < σ.ThSlot + gp.δt) :
    σ'.hj = σ.h ∧ (σ.previousHeightJustified → σ'.hF = σ.hj) := by
  have hj : σ'.hj = σ.h := by
    by_contra hne
    exact absurd (gp.timeout_step_slot h hh hne) (Nat.not_le.2 hs)
  exact ⟨hj, fun hb => gp.previousHeightJustified_justify_finalizes h hb hj⟩

/-- **An entry whose previous height is justified justifies with a target and a finality
quorum.** On a chain, if the predecessor pair
`(h_j, J)` is pending, a block whose counted state has a target quorum and a finality quorum at
`h_j` finalizes `h_j` and justifies the entry: the finality step picks `h_j` (no pending pair is
higher), so the gate holds, and the justification arm runs before the timeout arm. -/
theorem justify_of_target_previousHeightJustified {c : List (FGBlock gp.n)} {σ σ' : ChainState gp.n}
    {B : FGBlock gp.n} (hc : gp.chainState c = some σ) (h : gp.stateTransition σ B = some σ')
    (hp : (σ.hj, σ.J) ∈ σ.pending)
    (hq : gp.q ≤ (B.atts.foldl ChainState.processAtt { σ with s := B.slot }).target.card)
    (hf : gp.q ≤ ((B.atts.foldl ChainState.processAtt { σ with s := B.slot }).fin σ.hj).card) :
    σ'.hj = σ.h ∧ σ'.J = σ.Th ∧ σ'.hF = σ.hj := by
  obtain ⟨-, -, -, -, -, -, -, hmem, -, -⟩ := chain_invariants gp c σ hc
  obtain ⟨-, he⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, hfl⟩ := ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [hfl] at he hq hf
  subst he
  cases hbf : gp.bestFinal
      { σ with s := B.slot, fin := f, prog := p, target := t, L := B.root } with
  | none =>
    exact absurd hf (Nat.not_le.2 (gp.bestFinal_eq_none hbf _ hp))
  | some r =>
    obtain ⟨hr, -, hmax⟩ := gp.bestFinal_eq_some hbf
    have h1 := hmax _ hp hf
    have h2 := (hmem r hr).2
    have hr1 : r.1 = σ.hj := le_antisymm h2 h1
    unfold heightEvents finalizePrune
    rw [hbf]
    dsimp only
    split_ifs with hj1
    · simp [ChainState.advance, hr1]
    all_goals exact absurd ⟨hq, Or.inr hr1⟩ hj1

/-- **A finalized predecessor justifies with a target quorum (the finalized case of
W2).** On a chain, if `h_F = h_j`, no pair is pending (pending heights are in `(h_F, h_j]`),
so the finality step keeps `h_F`, and the loose-BJ gate holds: a block whose counted state has a
target quorum justifies the entry, with no finality quorum, and keeps `h_F = h_j`. -/
theorem justify_of_target_finalized {c : List (FGBlock gp.n)} {σ σ' : ChainState gp.n}
    {B : FGBlock gp.n} (hc : gp.chainState c = some σ) (h : gp.stateTransition σ B = some σ')
    (hfe : σ.hF = σ.hj)
    (hq : gp.q ≤ (B.atts.foldl ChainState.processAtt { σ with s := B.slot }).target.card) :
    σ'.hj = σ.h ∧ σ'.J = σ.Th ∧ σ'.hF = σ.hj := by
  obtain ⟨-, -, -, -, -, -, -, hmem, -, -⟩ := chain_invariants gp c σ hc
  have hnil : σ.pending = [] :=
    List.eq_nil_iff_forall_not_mem.2 fun p hp => by have := hmem p hp; omega
  obtain ⟨-, he⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, hf⟩ := ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [hf] at he hq
  obtain ⟨F, hF, σ₁, rfl, hfin, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, fin := f, prog := p, target := t, L := B.root }
  have hF0 : hF = σ.hF := by
    rcases hfin with ⟨-, e⟩ | ⟨hm, -⟩
    · exact e
    · exact absurd hm (by simp [hnil])
  subst hF0
  rcases hcase with ⟨-, he'⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩
  · rw [he'] at he; subst he; exact ⟨rfl, rfl, by simp [ChainState.advance, hfe]⟩
  · exact absurd ⟨hq, Or.inr hfe⟩ hn
  · exact absurd ⟨hq, Or.inr hfe⟩ hn

/-- **Justification at one chain step, by W2.** On a chain, a block whose counted state has a
target quorum, and a finality quorum at `h_j` when the height has its previous height justified and
`(h_j, J)` is pending, justifies the entry, and at a height whose previous height is justified it
has `h_F = h_j`. -/
theorem justify_of_target_chain {c : List (FGBlock gp.n)} {σ σ' : ChainState gp.n}
    {B : FGBlock gp.n} (hc : gp.chainState c = some σ) (h : gp.stateTransition σ B = some σ')
    (hq : gp.q ≤ (B.atts.foldl ChainState.processAtt { σ with s := B.slot }).target.card)
    (hf : σ.previousHeightJustified → (σ.hj, σ.J) ∈ σ.pending →
      gp.q ≤ ((B.atts.foldl ChainState.processAtt { σ with s := B.slot }).fin σ.hj).card) :
    σ'.hj = σ.h ∧ σ'.J = σ.Th ∧ (σ.previousHeightJustified → σ'.hF = σ.hj) := by
  by_cases hb : σ.previousHeightJustified
  · rcases gp.pred_pending_or_finalized hc with hp | hfe
    · obtain ⟨h1, h2, h3⟩ := gp.justify_of_target_previousHeightJustified hc h hp hq (hf hb hp)
      exact ⟨h1, h2, fun _ => h3⟩
    · obtain ⟨h1, h2, h3⟩ := gp.justify_of_target_finalized hc h hfe hq
      exact ⟨h1, h2, fun _ => h3⟩
  · obtain ⟨h1, h2⟩ := gp.justify_of_target_previousHeightNotJustified h hq hb
    exact ⟨h1, h2, fun e => absurd e hb⟩

/-- **A pending pair at height `h_j` is `(h_j, J)` (G0.2 (d), (e)).** On a chain, the
pending heights are strictly increasing and the newest pair is `(h_j, J)`, so a pending pair at
height `h_j` is that pair. -/
theorem pending_eq_of_fst_eq_hj {c : List (FGBlock gp.n)} {σ : ChainState gp.n}
    (hc : gp.chainState c = some σ) {p : Nat × Nat} (hp : p ∈ σ.pending) (he : p.1 = σ.hj) :
    p = (σ.hj, σ.J) := by
  obtain ⟨-, -, -, -, -, -, hpw, hmem, hlast, -⟩ := chain_invariants gp c σ hc
  have hlt : σ.hF < σ.hj := he ▸ (hmem p hp).1
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 (hlast hlt)
  rw [hys] at hp hpw
  rcases List.mem_append.1 hp with hy | hy
  · have := (List.pairwise_append.1 hpw).2.2 p hy _ (List.mem_singleton_self _)
    simp only at this
    omega
  · exact List.mem_singleton.1 hy

/-- One accepted block: its finalization `(F, h_F)` is the parent's or a pending pair of the
parent; it justified the parent's height, or it kept `(J, h_j)`. -/
private theorem step_fin {σ σ' : ChainState gp.n} {B : FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') :
    ((σ'.F = σ.F ∧ σ'.hF = σ.hF) ∨ (σ'.hF, σ'.F) ∈ σ.pending) ∧
      (σ'.hj = σ.h ∨ (σ'.hj = σ.hj ∧ σ'.J = σ.J)) := by
  obtain ⟨-, he⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, hf⟩ := ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [hf] at he
  obtain ⟨F, hF, σ₁, rfl, hfin, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, fin := f, prog := p, target := t, L := B.root }
  have hfin' : (F = σ.F ∧ hF = σ.hF) ∨ (hF, F) ∈ σ.pending := by
    rcases hfin with e | ⟨hm, -⟩
    · exact Or.inl e
    · exact Or.inr hm
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he'] at he <;> subst he
  · exact ⟨hfin', Or.inl rfl⟩
  · exact ⟨hfin', Or.inr ⟨rfl, rfl⟩⟩
  · exact ⟨hfin', Or.inr ⟨rfl, rfl⟩⟩

/-- **Finalized at `h_j` means finalized `J` (G0.2 (c)).** On a chain, if
`h_F = h_j` then `F = J`. -/
theorem F_eq_J_of_hF_eq_hj {c : List (FGBlock gp.n)} {σ : ChainState gp.n}
    (hc : gp.chainState c = some σ) (he : σ.hF = σ.hj) : σ.F = σ.J := by
  refine gp.chainState_induction (P := fun _ σ => σ.hF = σ.hj → σ.F = σ.J)
    (fun _ => rfl) (fun c σ B σ' hc ih hB => ?_) hc he
  intro he'
  obtain ⟨-, hle, hlt, -, -, -, -, hmem, -, -⟩ := chain_invariants gp c σ hc
  obtain ⟨hfin, hj⟩ := gp.step_fin hB
  rcases hj with hj | ⟨hj, hJ⟩
  · rcases hfin with ⟨-, e⟩ | hm
    · omega
    · have := (hmem _ hm).2; simp only at this; omega
  · rcases hfin with ⟨e1, e2⟩ | hm
    · rw [e1, hJ]; exact ih (by omega)
    · have := gp.pending_eq_of_fst_eq_hj hc hm (by simp only; omega)
      rw [hJ]; exact (Prod.mk.inj this).2

/-- **A justification at a height whose previous height is justified finalizes the predecessor
block.** On a chain, a block that justifies the current height of a state whose previous height is
justified has `F = J` of the parent state: the predecessor block, not only its height. -/
theorem previousHeightJustified_justify_finalizes_block {c : List (FGBlock gp.n)}
    {σ σ' : ChainState gp.n} {B : FGBlock gp.n} (hc : gp.chainState c = some σ)
    (h : gp.stateTransition σ B = some σ')
    (hb : σ.previousHeightJustified) (hj : σ'.hj = σ.h) : σ'.F = σ.J ∧ σ'.hF = σ.hj := by
  have hF := gp.previousHeightJustified_justify_finalizes h hb hj
  refine ⟨?_, hF⟩
  rcases (gp.step_fin h).1 with ⟨e1, e2⟩ | hm
  · rw [e1]; exact gp.F_eq_J_of_hF_eq_hj hc (by omega)
  · exact (Prod.mk.inj (gp.pending_eq_of_fst_eq_hj hc hm hF)).2

/-- One accepted block keeps the height with its entry and justification, or enters the next
height, with `J` the old entry block when it justified. -/
private theorem step_stay_or_cross {σ σ' : ChainState gp.n} {B : FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') :
    (σ'.h = σ.h ∧ σ'.Th = σ.Th ∧ σ'.ThSlot = σ.ThSlot ∧ σ'.J = σ.J ∧ σ'.hj = σ.hj) ∨
      (σ'.h = σ.h + 1 ∧ (σ'.J = σ.Th ∨ σ'.hj = σ.hj)) := by
  obtain ⟨-, he⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, hf⟩ := ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [hf] at he
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, fin := f, prog := p, target := t, L := B.root }
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he'] at he <;> subst he
  · exact Or.inr ⟨rfl, Or.inl rfl⟩
  · exact Or.inr ⟨rfl, Or.inr rfl⟩
  · exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **One block keeps the entry, or enters the next height at its own slot.** For
`stateTransition σ B = some σ'`, either the height, the entry slot and the entry stay, or the
height goes up by one and the entry is `B` at its slot (`Th := B.root`, `ThSlot := B.slot`). -/
theorem stateTransition_ThSlot {σ σ' : ChainState gp.n} {B : FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') :
    (σ'.h = σ.h ∧ σ'.ThSlot = σ.ThSlot ∧ σ'.Th = σ.Th) ∨
      (σ'.h = σ.h + 1 ∧ σ'.ThSlot = B.slot ∧ σ'.Th = B.root) := by
  obtain ⟨-, he⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, hf⟩ := ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [hf] at he
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, fin := f, prog := p, target := t, L := B.root }
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he'] at he <;> subst he
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl, rfl⟩

/-- **A crossing that is early or justifies, so it justifies (prefix form).** Let `c` reach `σ` and
`c ++ d` reach `τ` with `σ.h < τ.h`. If every block `B` of `d` that is applied to a state `ρ` of
height `σ.h` and enters the next height (state `ρ'`) has a slot before `ρ.ThSlot + δt` or justifies
(`ρ'.hj = ρ.h`), then a block of `d` justified the entry `(σ.h, σ.Th)`, and finalized the
predecessor block if `σ` has its previous height justified. The second disjunct covers a crossing at
age `≥ δt` with a target quorum: the justify test precedes the timeout test. -/
theorem cross_chain_justifies' {c d : List (FGBlock gp.n)} {σ τ : ChainState gp.n}
    (hc : gp.chainState c = some σ) (hd : gp.chainState (c ++ d) = some τ) (hh : σ.h < τ.h)
    (hs : ∀ d₁ B d₂ ρ ρ', d = d₁ ++ B :: d₂ → gp.chainState (c ++ d₁) = some ρ →
      gp.chainState (c ++ d₁ ++ [B]) = some ρ' → ρ.h = σ.h → ρ'.h = ρ.h + 1 →
      B.slot < ρ.ThSlot + gp.δt ∨ ρ'.hj = ρ.h) :
    ∃ d₁ B d₂ σ₂, d = d₁ ++ B :: d₂ ∧ gp.chainState (c ++ d₁ ++ [B]) = some σ₂ ∧
      σ₂.h = σ.h + 1 ∧ σ₂.hj = σ.h ∧ σ₂.J = σ.Th ∧
      (σ.previousHeightJustified → σ₂.F = σ.J ∧ σ₂.hF = σ.hj) := by
  suffices H : ∀ τ, gp.chainState (c ++ d) = some τ →
      (τ.h = σ.h ∧ τ.Th = σ.Th ∧ τ.ThSlot = σ.ThSlot ∧ τ.J = σ.J ∧ τ.hj = σ.hj) ∨
      ∃ d₁ B d₂ σ₂, d = d₁ ++ B :: d₂ ∧ gp.chainState (c ++ d₁ ++ [B]) = some σ₂ ∧
        σ₂.h = σ.h + 1 ∧ σ₂.hj = σ.h ∧ σ₂.J = σ.Th ∧
        (σ.previousHeightJustified → σ₂.F = σ.J ∧ σ₂.hF = σ.hj) by
    rcases H τ hd with ⟨e, -⟩ | hx
    · omega
    · exact hx
  clear hd hh τ
  revert hs
  induction d using List.reverseRecOn with
  | nil =>
    intro _ τ hτ
    rw [List.append_nil, hc] at hτ
    cases hτ
    exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩
  | append_singleton d B ih =>
    intro hs τ hτ
    have hs' : ∀ d₁ B' d₂ ρ ρ', d = d₁ ++ B' :: d₂ → gp.chainState (c ++ d₁) = some ρ →
        gp.chainState (c ++ d₁ ++ [B']) = some ρ' → ρ.h = σ.h → ρ'.h = ρ.h + 1 →
        B'.slot < ρ.ThSlot + gp.δt ∨ ρ'.hj = ρ.h := fun d₁ B' d₂ ρ ρ' e hρ hρ' =>
      hs d₁ B' (d₂ ++ [B]) ρ ρ' (by rw [e]; simp) hρ hρ'
    rw [← List.append_assoc, gp.chainState_append, Option.bind_eq_some_iff] at hτ
    obtain ⟨τ₀, h₀, hB⟩ := hτ
    have hτ' : gp.chainState (c ++ d ++ [B]) = some τ := by
      rw [gp.chainState_append, h₀]; exact hB
    rcases ih hs' τ₀ h₀ with ⟨e1, e2, e3, e4, e5⟩ | ⟨d₁, B', d₂, σ₂, rfl, h1, h2⟩
    · rcases gp.step_stay_or_cross hB with ⟨f1, f2, f3, f4, f5⟩ | ⟨f1, f2⟩
      · exact Or.inl ⟨f1.trans e1, f2.trans e2, f3.trans e3, f4.trans e4, f5.trans e5⟩
      · have hj : τ.hj = τ₀.h := by
          rcases hs d B [] τ₀ τ (by simp) h₀ hτ' e1 f1 with hsl | hj
          · exact (gp.early_cross_justifies hB f1 hsl).1
          · exact hj
        have hJ : τ.J = τ₀.Th := by
          rcases f2 with f2 | f2
          · exact f2
          · have := (chain_invariants gp _ _ h₀).2.2.1; omega
        refine Or.inr ⟨d, B, [], τ, by simp, hτ', by omega, by omega, by rw [hJ, e2], ?_⟩
        intro hb
        have hb₀ : τ₀.previousHeightJustified := by
          simp only [ChainState.previousHeightJustified] at hb ⊢; omega
        obtain ⟨g1, g2⟩ := gp.previousHeightJustified_justify_finalizes_block h₀ hB hb₀ hj
        exact ⟨g1.trans e4, g2.trans e5⟩
    · exact Or.inr ⟨d₁, B', d₂ ++ [B], σ₂, by simp, h1, h2⟩

/-- **Theorem F, chain part, crossings early or justifying.** `theorem_F_chain` with the timing
premise replaced by: every block of `d` applied at height `σ.h` or `σ.h + 1` that enters the
next height has a slot before the entry slot plus `δt`, or justifies (`ρ'.hj = ρ.h`). -/
theorem theorem_F_chain' {c d : List (FGBlock gp.n)} {σ τ : ChainState gp.n}
    (hc : gp.chainState c = some σ) (hd : gp.chainState (c ++ d) = some τ)
    (hh : σ.h + 1 < τ.h)
    (hs : ∀ d₁ B d₂ ρ ρ', d = d₁ ++ B :: d₂ → gp.chainState (c ++ d₁) = some ρ →
      gp.chainState (c ++ d₁ ++ [B]) = some ρ' → (ρ.h = σ.h ∨ ρ.h = σ.h + 1) →
      ρ'.h = ρ.h + 1 → B.slot < ρ.ThSlot + gp.δt ∨ ρ'.hj = ρ.h) :
    ∃ d₁ B₁ d₂ B₂ d₃ σ₁ σ₂, d = d₁ ++ B₁ :: (d₂ ++ B₂ :: d₃) ∧
      gp.chainState (c ++ d₁ ++ [B₁]) = some σ₁ ∧
      σ₁.h = σ.h + 1 ∧ σ₁.hj = σ.h ∧ σ₁.J = σ.Th ∧
      gp.chainState (c ++ d₁ ++ [B₁] ++ d₂ ++ [B₂]) = some σ₂ ∧
      σ₂.h = σ.h + 2 ∧ σ₂.hj = σ.h + 1 ∧ σ₂.J = σ₁.Th ∧
      σ₂.F = σ.Th ∧ σ₂.hF = σ.h := by
  obtain ⟨d₁, B₁, d₂, σ₁, rfl, h1, h1h, h1j, h1J, -⟩ :=
    gp.cross_chain_justifies' hc hd (by omega) fun d₁ B d₂ ρ ρ' e hρ hρ' hρh =>
      hs d₁ B d₂ ρ ρ' e hρ hρ' (Or.inl hρh)
  have hd' : gp.chainState (c ++ d₁ ++ [B₁] ++ d₂) = some τ := by simpa using hd
  obtain ⟨d₂', B₂, d₃, σ₂, rfl, h2, h2h, h2j, h2J, h2F⟩ :=
    gp.cross_chain_justifies' h1 hd' (by omega) fun e₁ B e₂ ρ ρ' e hρ hρ' hρh =>
      hs (d₁ ++ B₁ :: e₁) B e₂ ρ ρ' (by rw [e]; simp) (by simpa using hρ) (by simpa using hρ')
        (Or.inr (by omega))
  have hb : σ₁.previousHeightJustified := by
    have := (chain_invariants gp _ _ hc).1
    simp only [ChainState.previousHeightJustified]; omega
  obtain ⟨hF, hhF⟩ := h2F hb
  exact ⟨d₁, B₁, d₂', B₂, d₃, σ₁, σ₂, by simp, h1, h1h, h1j, h1J, h2, by omega,
    by omega, h2J, hF.trans h1J, hhF.trans h1j⟩

end FGParams

namespace Record

end Record

end Consensus.Goldilocks.FG

end
