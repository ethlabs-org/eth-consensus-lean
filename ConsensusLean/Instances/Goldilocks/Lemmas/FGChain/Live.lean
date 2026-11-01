module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Invariants

public section

/-! # Goldilocks FG: step facts for liveness

Two facts of one accepted block that the liveness argument uses (workbench
`fg-liveness/r14-end-to-end`, s5 lemma T and s6 L6.1):
* a block that enters a new height without justifying the old one (a timeout) has a slot at
  least `δt` after the entry of the old height;
* a block that justifies a bound height has finalized its predecessor: the loose-BJ gate reads
  the finalization of the same block;
* at a bound height the predecessor is pending or finalized (s5 W2), and a step that enters an
  unbound height is a timeout, so its slot is at least `δt` after the old entry. -/

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

/-- **Timeout slot (r14 s5, lemma T).** A block that enters the next height without
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

/-- **A bound justification finalizes its predecessor (r14 s6, L6.1).** A block that
justifies the current height of a bound state has finalized the predecessor height `h_j`
in its own finality step. -/
theorem bound_justify_finalizes {σ σ' : ChainState gp.n} {B : FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ') (hb : σ.bound) (hj : σ'.hj = σ.h) :
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

/-- **Predecessor pending or finalized (r14 s5, W2).** On a chain, at a bound height the
predecessor pair `(h_j, J)` is pending, or `h_j` is finalized. -/
theorem pred_pending_or_finalized {c : List (FGBlock gp.n)} {σ : ChainState gp.n}
    (hc : gp.chainState c = some σ) : (σ.hj, σ.J) ∈ σ.pending ∨ σ.hF = σ.hj := by
  obtain ⟨-, hle, -, -, -, -, -, -, hlast, -⟩ := chain_invariants gp c σ hc
  rcases Nat.lt_or_ge σ.hF σ.hj with hlt | hge
  · exact Or.inl (List.mem_of_getLast? (hlast hlt))
  · exact Or.inr (le_antisymm hle hge)

/-- **An unbound entry is a timeout (r14 s5, X with T).** On a chain, a block that enters the
next height and leaves it unbound has a slot at least `δt` after the old entry. -/
theorem unbound_step_slot {c : List (FGBlock gp.n)} {σ σ' : ChainState gp.n} {B : FGBlock gp.n}
    (hc : gp.chainState c = some σ) (h : gp.stateTransition σ B = some σ')
    (hh : σ'.h = σ.h + 1) (hnb : ¬ σ'.bound) : σ.ThSlot + gp.δt ≤ B.slot := by
  obtain ⟨-, -, -, -, hbd⟩ := height_step gp c σ σ' B hc h
  obtain ⟨-, hiff, -⟩ := hbd hh
  exact gp.timeout_step_slot h hh (fun e => hnb (hiff.2 e))

end FGParams

end Consensus.Goldilocks.FG

end
