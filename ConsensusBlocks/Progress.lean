module
public import ConsensusBlocks.TimeGrid

@[expose] public section

/-! # Progress requirements (building block)

Leader-based progress over a time grid, in two forms (`ProgressReq`):

* `recur ρ`: a slot pattern (nonempty offsets) recurs, honest and ready,
  within every window of `gap` slots (slot proposers);
* `notReadyAtMost m`: at most `m` validators are not ready at each time (for
  `m ≥ card V` this holds trivially; the liveness it feeds is
  reader-conditional, so it then owes nothing where nobody is ready).
  It is a pointwise bound (see the README's Scope for the round-robin
  caveat).

Both are typed over the environment point, the PKI and the selection only:
they cannot see events, states or the hash. Admissibility is by typing: a
pattern is nonempty, a gap and a bound are positive.

A requirement holds on a window `[start, stop]`: windows and times start at or
after `max start 0`, and the **whole pattern** of each window (the window plus
the pattern's span) must end by `stop` and by the horizon. Nothing after
`stop` is read. -/

namespace Consensus.Blocks

/-- A slot pattern: nonempty offsets from a start slot. `[0]` = one honest
proposer; `[0,1,2,3,4]` = Streamlet. -/
structure Pattern where
  /-- Slot offsets from the start slot. -/
  offsets : List Nat
  nonempty : offsets ≠ []

/-- One honest proposer: the pattern `[0]`. -/
def Pattern.single : Pattern := ⟨[0], by simp⟩

/-- `n` consecutive honest proposers: the pattern `[0, …, n − 1]`. -/
def Pattern.range (n : ℕ+) : Pattern := ⟨List.range n, by simp⟩

/-- The largest offset of a pattern. -/
def Pattern.span (P : Pattern) : Nat := P.offsets.foldr max 0

/-- A recurrence: a pattern recurring within every window of `gap` slots;
`gap` is positive by type. -/
structure Recurrence where
  /-- The pattern that must recur. -/
  pattern : Pattern
  /-- The window length in slots. -/
  gap : ℕ+

/-- The slots a recurrence window reads: the window plus the pattern's span. -/
def Recurrence.len (ρ : Recurrence) : Nat := (ρ.gap : Nat) + ρ.pattern.span

/-- A recurrence leaves room for a bad proposer slot in every window:
`span + 2 ≤ gap`. With a bad slot every `span + 2` slots, every window of
`gap` slots holds a bad slot and a start slot whose whole pattern avoids the
bad slots (`patternRecurrence_of_periodic`; the run-level witness is
`RealizableActive.badProposer`). A gap of one slot (an honest ready proposer
in *every* slot) or a pattern without slack is rejected
(`ProgressReq.Tolerates`; test `recur_single_one_not_tolerant`). -/
def Recurrence.BadSlotSlack (ρ : Recurrence) : Prop := ρ.pattern.span + 2 ≤ (ρ.gap : Nat)

instance (ρ : Recurrence) : Decidable ρ.BadSlotSlack := by
  unfold Recurrence.BadSlotSlack; infer_instance

/-- A progress requirement: pattern recurrence (slot proposers), or a bound on
the validators that are not ready (round-robin leaders). -/
inductive ProgressReq where
  | recur (ρ : Recurrence)
  | notReadyAtMost (m : ℕ+)

variable {V : Type} [Fintype V]

/-- The keys selected for slot `s` form a nonempty set, and each is ready at
`t` (ready includes honest). -/
def HonestReadyIn (p : EnvPoint V) (key : Fin (Fintype.card V) ≃ V)
    (sel : Slot → Finset (Fin (Fintype.card V))) (s : Slot) (c t : Time) : Prop :=
  (sel s).Nonempty ∧ ∀ k ∈ sel s, p.Ready c (key k) t

/-- Pattern recurrence on `[start, stop]`: every window `(t, t + gap·slotLen]`
with `t ≥ max start 0` whose whole pattern ends by `stop` and by the horizon
(`t + (gap + span)·slotLen ≤ min stop horizon`) contains a start slot `s` at
which the whole pattern is honest and ready: for each offset `j`, the keys
selected for slot `s + j`, at the time of slot `s + j`. -/
def PatternRecurrence (p : EnvPoint V) (key : Fin (Fintype.card V) ≃ V)
    (sel : Slot → Finset (Fin (Fintype.card V))) (G : TimeGrid) (ρ : Recurrence)
    (c start stop : Time) : Prop :=
  ∀ t, max start 0 ≤ t → t + (ρ.len : Time) * G.slotLen p.env.Δ ≤ stop →
    t + (ρ.len : Time) * G.slotLen p.env.Δ ≤ p.horizon →
    ∃ s, t < G.slotTime p.env.Δ s ∧
      G.slotTime p.env.Δ s ≤ t + ((ρ.gap : Nat) : Time) * G.slotLen p.env.Δ ∧
      ∀ j ∈ ρ.pattern.offsets, HonestReadyIn p key sel (s + j) c (G.slotTime p.env.Δ (s + j))

/-- At most `m` validators are not ready (faulty, or honest and not ready) at
`t`. -/
def _root_.Consensus.EnvPoint.NotReadyAtMost [DecidableEq V] (p : EnvPoint V) (m : Nat)
    (c t : Time) : Prop :=
  Fintype.card V ≤ (p.readyAt c t).card + m

/-- At most `m` validators are not ready at every time of `[max start 0, stop]`
within the horizon. No bound on `m` against the validator count: `m ≥ card V`
holds trivially (`NotReadyOn.of_card_le`), which is what lets a contract index
by every `m` for a fixed population (L0 `Realizable` fixes `V` before the
index); the liveness it feeds (`ProposalLiveReady`) is reader-conditional, so a
trivial bound owes nothing where nobody is ready. -/
def NotReadyOn [DecidableEq V] (p : EnvPoint V) (m : Nat) (c start stop : Time) : Prop :=
  ∀ t, max start 0 ≤ t → t ≤ stop → t ≤ p.horizon → p.NotReadyAtMost m c t

end Consensus.Blocks
end
