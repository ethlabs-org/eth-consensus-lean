module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Invariants
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Client

public section

/-! # Goldilocks FG: step facts for liveness

Two facts of one accepted block that the liveness argument uses (workbench
`fg-liveness/r14-end-to-end`, s5 lemma T and s6 L6.1):
* a block that enters a new height without justifying the old one (a timeout) has a slot at
  least `δt` after the entry of the old height;
* a block that justifies a bound height has finalized its predecessor: the loose-BJ gate reads
  the finalization of the same block;
* at a bound height the predecessor is pending or finalized (s5 W2), and a step that enters an
  unbound height is a timeout, so its slot is at least `δt` after the old entry;
* a client whose record is clean at the entry's height sends a target for that entry, not a
  timeout (s5 C). -/

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

/-- **Crossing by progress (r14 s3 L3.3a; the window tables).** A block whose counted state has a
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

/-- **An unbound entry justifies with a target quorum (r14 s3, window tables).** A block whose
counted state has a target quorum, at an unbound height, justifies the entry: the loose-BJ gate
does not apply. -/
theorem justify_of_target_unbound {σ σ' : ChainState gp.n} {B : FGBlock gp.n}
    (h : gp.stateTransition σ B = some σ')
    (hq : gp.q ≤ (B.atts.foldl ChainState.processAtt { σ with s := B.slot }).target.card)
    (hnb : ¬ σ.bound) : σ'.hj = σ.h ∧ σ'.J = σ.Th := by
  obtain ⟨-, he⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, hf⟩ := ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [hf] at he hq
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, fin := f, prog := p, target := t, L := B.root }
  rcases hcase with ⟨-, he'⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩
  · rw [he'] at he; subst he; exact ⟨rfl, rfl⟩
  · exact absurd ⟨hq, Or.inl (by simpa [ChainState.bound] using hnb)⟩ hn
  · exact absurd ⟨hq, Or.inl (by simpa [ChainState.bound] using hnb)⟩ hn

end FGParams

namespace Record

/-- **A clean record sends a target (r14 s5, C).** If the record has no lock, no timeout
and no target at the entry's height that name another block, and has sent nothing at that
height, then `create_attestation` sends a target (not a timeout) for the entry. -/
theorem createAtt_target {n : Nat} {Λ : Record} {v : Fin n} {σe : ChainState n}
    (hl : Λ.lock σe.h = none ∨ Λ.lock σe.h = some σe.Th) (ht : Λ.timeout σe.h = ∅)
    (htg : Λ.target σe.h = none ∨ Λ.target σe.h = some σe.Th)
    (hs : ∀ b ∈ Λ.sent, b.1 ≠ σe.h) :
    Λ.createAtt v σe = some (⟨v, σe.h, σe.Th, false, Λ.finalityPair σe⟩,
      Λ.recordAtt ⟨v, σe.h, σe.Th, false, Λ.finalityPair σe⟩) := by
  have hp : Λ.heightPair σe.h σe.Th = some (σe.h, σe.Th, false) := by
    rcases hl with h1 | h1 <;> rcases htg with h2 | h2 <;> simp [heightPair, h1, h2, ht]
  unfold createAtt
  rw [hp]
  dsimp only
  split_ifs with hc
  · obtain ⟨b, hb, he⟩ := List.any_eq_true.1 hc
    exact absurd (of_decide_eq_true he).1 (hs b hb)
  · rfl

end Record

end Consensus.Goldilocks.FG

end
