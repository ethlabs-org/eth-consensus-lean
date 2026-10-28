module
public import ConsensusBlocks.TimeGrid

@[expose] public section

/-! # Selection premises (building block)

Progress requirements over a time grid: a slot pattern (nonempty offsets) that
must recur, honest and ready, within every window of `gap` slots. The premise
is typed over the environment point, the PKI and the selection only: it cannot
see events, states or the hash. Admissibility is by typing (D-2): a pattern is
nonempty and a gap is positive. -/

namespace Consensus.Blocks

/-- A slot pattern: nonempty offsets from a start slot (D-2). `[0]` = one
honest proposer; `[0,1,2,3,4]` = Streamlet. -/
structure Pattern where
  /-- Slot offsets from the start slot. -/
  offsets : List Nat
  nonempty : offsets ≠ []

/-- One honest proposer: the pattern `[0]`. -/
def Pattern.single : Pattern := ⟨[0], by simp⟩

/-- A progress requirement: a pattern recurring within every window of `gap`
slots; `gap` is positive by type (D-2). -/
structure ProgressReq where
  /-- The pattern that must recur. -/
  pattern : Pattern
  /-- The window length in slots. -/
  gap : ℕ+

variable {V : Type} [Fintype V] {R : Type}

/-- Role `r` is nonempty and every key selected for it is honest and ready at
`t` (D-12). -/
def HonestReadyIn (p : EnvPoint V) (key : Fin (Fintype.card V) ≃ V)
    (sel : R → Finset (Fin (Fintype.card V))) (r : R) (c t : Time) : Prop :=
  (sel r).Nonempty ∧ ∀ k ∈ sel r, key k ∈ p.honest ∧ p.Ready c (key k) t

/-- Pattern recurrence: from `max start 0` (D-22), every window of `gap` slots
inside the horizon contains a start slot `s` (strictly after `t`, at most
`t + gap · slotLen`) at which the whole pattern is honest and ready: for each
offset `j`, the role `lead (s + j)` at the time of slot `s + j`. Typed over the
environment point, PKI and selection only: it cannot see events, states or
the hash. -/
def PatternRecurrence (p : EnvPoint V) (key : Fin (Fintype.card V) ≃ V)
    (sel : R → Finset (Fin (Fintype.card V))) (lead : Slot → R) (G : TimeGrid)
    (π : ProgressReq) (c start : Time) : Prop :=
  ∀ t, start ≤ t → 0 ≤ t → t + ((π.gap : Nat) : Time) * G.slotLen p.env.Δ ≤ p.horizon →
    ∃ s, t < G.slotTime p.env.Δ s ∧
      G.slotTime p.env.Δ s ≤ t + ((π.gap : Nat) : Time) * G.slotLen p.env.Δ ∧
      ∀ j ∈ π.pattern.offsets,
        HonestReadyIn p key sel (lead (s + j)) c (G.slotTime p.env.Δ (s + j))

variable {p : EnvPoint V} {key : Fin (Fintype.card V) ≃ V}
  {sel : R → Finset (Fin (Fintype.card V))} {lead : Slot → R} {G : TimeGrid}
  {π : ProgressReq} {c start : Time}

/-- If every slot has an honest ready pattern, recurrence holds from any start
(no domain hypothesis: windows start at `t ≥ 0`, gaps are positive). -/
theorem patternRecurrence_of_all (hΔ : 0 < p.env.Δ)
    (h : ∀ s j, j ∈ π.pattern.offsets →
      HonestReadyIn p key sel (lead (s + j)) c (G.slotTime p.env.Δ (s + j))) :
    PatternRecurrence p key sel lead G π c start := by
  intro t _ ht _
  obtain ⟨s, hs₁, hs₂⟩ := G.exists_slot_in_window hΔ ht (k := (π.gap : Nat)) π.gap.pos
  exact ⟨s, hs₁, hs₂, fun j hj => h s j hj⟩

/-- Recurrence is non-vacuous: if one window fits in the horizon, the premise
yields an honest selected key (used by tests and witnesses). -/
theorem PatternRecurrence.exists_honest (h : PatternRecurrence p key sel lead G π c start)
    (ht : max start 0 + ((π.gap : Nat) : Time) * G.slotLen p.env.Δ ≤ p.horizon) :
    ∃ s k, k ∈ sel (lead s) ∧ key k ∈ p.honest := by
  obtain ⟨s, -, -, hall⟩ := h (max start 0) (le_max_left _ _) (le_max_right _ _) ht
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ π.pattern.nonempty
  obtain ⟨⟨k, hk⟩, hks⟩ := hall j hj
  exact ⟨s + j, k, hk, (hks k hk).1⟩

end Consensus.Blocks
end
