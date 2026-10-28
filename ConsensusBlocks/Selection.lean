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
  This is a pointwise bound: the set of non-ready validators may change from
  time to time, so it does **not** by itself give a ready honest round-robin
  leader within `m + 1` rounds (a schedule that sleeps exactly the current
  leader through its round, with enough validators that the few still
  catching up stay within `m`, meets it while no round has a ready leader).
  A concrete round-robin proof needs a temporal
  leader-opportunity argument or a revised requirement; that is protocol
  work, not part of this definition.

Both are typed over the environment point, the PKI and the selection only:
they cannot see events, states or the hash. Admissibility is by typing: a
pattern is nonempty, a gap and a bound are positive.

A requirement holds on a window `[start, stop]`: recurrence windows start at or
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

theorem Pattern.le_span {P : Pattern} {j : Nat} (h : j ∈ P.offsets) : j ≤ P.span := by
  unfold Pattern.span
  generalize P.offsets = l at h ⊢
  induction l with
  | nil => cases h
  | cons a l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- The single pattern has span `0`. -/
theorem Pattern.span_single : Pattern.single.span = 0 := rfl

/-- A pattern's span is at most any bound on its offsets. -/
theorem Pattern.span_le {P : Pattern} {b : Nat} (h : ∀ j ∈ P.offsets, j ≤ b) : P.span ≤ b := by
  unfold Pattern.span
  generalize P.offsets = l at h ⊢
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a List.mem_cons_self) (ih fun j hj => h j (List.mem_cons_of_mem _ hj))

/-- `n` consecutive slots span `n − 1`. -/
theorem Pattern.span_range (n : ℕ+) : (Pattern.range n).span = n - 1 :=
  le_antisymm (Pattern.span_le fun j hj => by
      have := List.mem_range.mp hj; omega)
    (Pattern.le_span (List.mem_range.mpr (by have := n.pos; omega)))

/-- A recurrence: a pattern recurring within every window of `gap` slots;
`gap` is positive by type. -/
structure Recurrence where
  /-- The pattern that must recur. -/
  pattern : Pattern
  /-- The window length in slots. -/
  gap : ℕ+

/-- The slots a recurrence window reads: the window plus the pattern's span. -/
def Recurrence.len (ρ : Recurrence) : Nat := (ρ.gap : Nat) + ρ.pattern.span

/-- A progress requirement: pattern recurrence (slot proposers), or a bound on
the validators that are not ready (round-robin leaders). -/
inductive ProgressReq where
  | recur (ρ : Recurrence)
  | notReadyAtMost (m : ℕ+)

variable {V : Type} [Fintype V] {R : Type}

/-- Role `r` is nonempty and every key selected for it is honest and ready at
`t`. -/
def HonestReadyIn (p : EnvPoint V) (key : Fin (Fintype.card V) ≃ V)
    (sel : R → Finset (Fin (Fintype.card V))) (r : R) (c t : Time) : Prop :=
  (sel r).Nonempty ∧ ∀ k ∈ sel r, key k ∈ p.honest ∧ p.Ready c (key k) t

/-- Pattern recurrence on `[start, stop]`: every window `(t, t + gap·slotLen]`
with `t ≥ max start 0` whose whole pattern ends by `stop` and by the horizon
(`t + (gap + span)·slotLen ≤ min stop horizon`) contains a start slot `s` at
which the whole pattern is honest and ready: for each offset `j`, the role
`lead (s + j)` at the time of slot `s + j`. -/
def PatternRecurrence (p : EnvPoint V) (key : Fin (Fintype.card V) ≃ V)
    (sel : R → Finset (Fin (Fintype.card V))) (lead : Slot → R) (G : TimeGrid)
    (ρ : Recurrence) (c start stop : Time) : Prop :=
  ∀ t, start ≤ t → 0 ≤ t → t + (ρ.len : Time) * G.slotLen p.env.Δ ≤ stop →
    t + (ρ.len : Time) * G.slotLen p.env.Δ ≤ p.horizon →
    ∃ s, t < G.slotTime p.env.Δ s ∧
      G.slotTime p.env.Δ s ≤ t + ((ρ.gap : Nat) : Time) * G.slotLen p.env.Δ ∧
      ∀ j ∈ ρ.pattern.offsets,
        HonestReadyIn p key sel (lead (s + j)) c (G.slotTime p.env.Δ (s + j))

/-- At most `m` validators are not ready at every time of `[max start 0, stop]`
within the horizon. No bound on `m` against the validator count: `m ≥ card V`
holds trivially (`NotReadyOn.of_card_le`), which is what lets a contract index
by every `m` for a fixed population (L0 `Realizable` fixes `V` before the
index); the liveness it feeds (`ProposalLiveReady`) is reader-conditional, so a
trivial bound owes nothing where nobody is ready. -/
def NotReadyOn [DecidableEq V] (p : EnvPoint V) (m : Nat) (c start stop : Time) : Prop :=
  ∀ t, max start 0 ≤ t → t ≤ stop → t ≤ p.horizon → p.NotReadyAtMost m c t

variable {p : EnvPoint V} {key : Fin (Fintype.card V) ≃ V}
  {sel : R → Finset (Fin (Fintype.card V))} {lead : Slot → R} {G : TimeGrid}
  {ρ : Recurrence} {c start stop : Time}

/-- A later start and an earlier stop are weaker. -/
theorem PatternRecurrence.mono {start' stop' : Time}
    (h : PatternRecurrence p key sel lead G ρ c start stop) (hs : start ≤ start')
    (he : stop' ≤ stop) : PatternRecurrence p key sel lead G ρ c start' stop' :=
  fun t ht h0 hst hh => h t (le_trans hs ht) h0 (le_trans hst he) hh

/-- A smaller horizon is weaker. -/
theorem PatternRecurrence.shrink {b : Time} (hb : b ≤ p.horizon)
    (h : PatternRecurrence p key sel lead G ρ c start stop) :
    PatternRecurrence { p with horizon := b } key sel lead G ρ c start stop :=
  fun t ht h0 hst hh => h t ht h0 hst (le_trans hh hb)

/-- A later start and an earlier stop are weaker. -/
theorem NotReadyOn.mono [DecidableEq V] {m : Nat} {start' stop' : Time}
    (h : NotReadyOn p m c start stop) (hs : start ≤ start') (he : stop' ≤ stop) :
    NotReadyOn p m c start' stop' :=
  fun t ht hst hh => h t (le_trans (max_le_max hs le_rfl) ht) (le_trans hst he) hh

/-- A smaller horizon is weaker. -/
theorem NotReadyOn.shrink [DecidableEq V] {m : Nat} {b : Time} (hb : b ≤ p.horizon)
    (h : NotReadyOn p m c start stop) : NotReadyOn { p with horizon := b } m c start stop :=
  fun t ht hst hh => h t ht hst (le_trans hh hb)

/-- A bound at least the validator count holds on every point and window. -/
theorem NotReadyOn.of_card_le [DecidableEq V] {m : Nat} (hm : Fintype.card V ≤ m) :
    NotReadyOn p m c start stop :=
  fun _ _ _ _ => le_trans hm (Nat.le_add_left _ _)

/-- Below the validator count the bound is not vacuous: some validator is
ready at every time of the window. -/
theorem NotReadyOn.readyAt_nonempty [DecidableEq V] {m : Nat} (hm : m < Fintype.card V)
    (h : NotReadyOn p m c start stop) {t : Time} (ht : max start 0 ≤ t) (hst : t ≤ stop)
    (hh : t ≤ p.horizon) : (p.readyAt c t).Nonempty := by
  have h2 : Fintype.card V ≤ (p.readyAt c t).card + m := h t ht hst hh
  exact Finset.card_pos.mp (by omega)

/-- Bounded dependence: recurrence on `[start, stop]` reads only `Δ` and the
honest-ready status of the keys at times up to `min stop horizon` (readiness
at `t` is the awake history up to `t`). A point `p'` with the same `Δ`, no
larger effective window, and every honest-ready key of `p` also honest-ready
in `p'` at those times inherits the recurrence; in particular a point that
agrees with `p` up to `min stop horizon` (suffix replacement). -/
theorem PatternRecurrence.reads_upTo {p' : EnvPoint V} (hΔ : p'.env.Δ = p.env.Δ)
    (hh : min stop p'.horizon ≤ p.horizon)
    (hr : ∀ v t, t ≤ min stop p'.horizon → v ∈ p.honest → p.Ready c v t →
      v ∈ p'.honest ∧ p'.Ready c v t)
    (h : PatternRecurrence p key sel lead G ρ c start stop) :
    PatternRecurrence p' key sel lead G ρ c start stop := by
  intro t ht h0 hst hhz
  rw [hΔ] at hst hhz ⊢
  have hm : t + (ρ.len : Time) * G.slotLen p.env.Δ ≤ min stop p'.horizon := le_min hst hhz
  obtain ⟨s, hs1, hs2, hall⟩ := h t ht h0 hst (le_trans hm hh)
  refine ⟨s, hs1, hs2, fun j hj => ?_⟩
  obtain ⟨hne, hk⟩ := hall j hj
  refine ⟨hne, fun k hk' => hr _ _ ?_ (hk k hk').1 (hk k hk').2⟩
  have hl := G.slotLen_pos p.env.Δ_pos
  have hj' : (j : Time) ≤ ρ.pattern.span := by exact_mod_cast Pattern.le_span hj
  have hlen : (ρ.len : Time) = ((ρ.gap : Nat) : Time) + (ρ.pattern.span : Time) := by
    simp [Recurrence.len]
  rw [hlen] at hm
  rw [G.slotTime_add]
  nlinarith

/-- Head extraction: a pattern with offset `0` gives one honest ready proposer
per window, losing the pattern's span at the end of the window `[start, stop]`
(the single pattern reads only the window itself). -/
theorem PatternRecurrence.single_of_zero (h0 : 0 ∈ ρ.pattern.offsets)
    (h : PatternRecurrence p key sel lead G ρ c start stop) :
    PatternRecurrence p key sel lead G ⟨Pattern.single, ρ.gap⟩ c start
      (min stop p.horizon - (ρ.pattern.span : Time) * G.slotLen p.env.Δ) := by
  intro t ht ht0 hst _
  have hlen : ((⟨Pattern.single, ρ.gap⟩ : Recurrence).len : Time) = ((ρ.gap : Nat) : Time) := by
    simp [Recurrence.len, Pattern.span_single]
  have hlen' : (ρ.len : Time) = ((ρ.gap : Nat) : Time) + (ρ.pattern.span : Time) := by
    simp [Recurrence.len]
  rw [hlen] at hst
  have hm1 := min_le_left stop p.horizon
  have hm2 := min_le_right stop p.horizon
  obtain ⟨s, hs1, hs2, hall⟩ := h t ht ht0 (by rw [hlen']; linarith) (by rw [hlen']; linarith)
  refine ⟨s, hs1, hs2, fun j hj => ?_⟩
  have hj0 : j = 0 := List.mem_singleton.mp hj
  subst hj0
  exact hall 0 h0

/-- If every slot has an honest ready pattern, recurrence holds on every
window (no domain hypothesis: windows start at `t ≥ 0`, gaps are positive). -/
theorem patternRecurrence_of_all (hΔ : 0 < p.env.Δ)
    (h : ∀ s j, j ∈ ρ.pattern.offsets →
      HonestReadyIn p key sel (lead (s + j)) c (G.slotTime p.env.Δ (s + j))) :
    PatternRecurrence p key sel lead G ρ c start stop := by
  intro t _ ht _ _
  obtain ⟨s, hs₁, hs₂⟩ := G.exists_slot_in_window hΔ ht (k := (ρ.gap : Nat)) ρ.gap.pos
  exact ⟨s, hs₁, hs₂, fun j hj => h s j hj⟩

/-- Recurrence is non-vacuous: if one whole window fits in `[max start 0, stop]`
and the horizon, the requirement yields an honest selected key. -/
theorem PatternRecurrence.exists_honest (h : PatternRecurrence p key sel lead G ρ c start stop)
    (hs : max start 0 + (ρ.len : Time) * G.slotLen p.env.Δ ≤ stop)
    (ht : max start 0 + (ρ.len : Time) * G.slotLen p.env.Δ ≤ p.horizon) :
    ∃ s k, k ∈ sel (lead s) ∧ key k ∈ p.honest := by
  obtain ⟨s, -, -, hall⟩ := h (max start 0) (le_max_left _ _) (le_max_right _ _) hs ht
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ ρ.pattern.nonempty
  obtain ⟨⟨k, hk⟩, hks⟩ := hall j hj
  exact ⟨s + j, k, hk, (hks k hk).1⟩

/-- With one whole window inside `[max start 0, stop]` and the horizon,
recurrence yields a start slot whose whole pattern is honest, ready and inside
the horizon. -/
theorem PatternRecurrence.exists_inside (h : PatternRecurrence p key sel lead G ρ c start stop)
    (hs : max start 0 + (ρ.len : Time) * G.slotLen p.env.Δ ≤ stop)
    (ht : max start 0 + (ρ.len : Time) * G.slotLen p.env.Δ ≤ p.horizon) :
    ∃ s, ∀ j ∈ ρ.pattern.offsets, G.slotTime p.env.Δ (s + j) ≤ p.horizon ∧
      HonestReadyIn p key sel (lead (s + j)) c (G.slotTime p.env.Δ (s + j)) := by
  have hl := G.slotLen_pos p.env.Δ_pos
  obtain ⟨s, -, hs', hall⟩ := h (max start 0) (le_max_left _ _) (le_max_right _ _) hs ht
  refine ⟨s, fun j hj => ⟨?_, hall j hj⟩⟩
  have hj' : (j : Time) ≤ ρ.pattern.span := by exact_mod_cast Pattern.le_span hj
  have hlen : (ρ.len : Time) = ((ρ.gap : Nat) : Time) + (ρ.pattern.span : Time) := by
    simp [Recurrence.len]
  rw [hlen] at ht
  rw [G.slotTime_add]
  nlinarith

end Consensus.Blocks
end
