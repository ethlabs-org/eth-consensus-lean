module
public import ConsensusLean.Spec.Blocks.TimeGrid
public import ConsensusLean.Spec.Blocks.Progress
public import ConsensusLean.Spec.Blocks.Chains
public import ConsensusLean.Spec.Blocks.Payload

@[expose] public section

/-! # Building-block facts (outside the trusted surface)

The lemmas about the definitions of `TimeGrid`, `Progress` and `Payload`
(names unchanged). The definition files hold definitions and instances only. -/

namespace Consensus.Blocks

/-! ## Time grid -/

namespace TimeGrid

variable (G : TimeGrid)

theorem slotLen_pos {Δ : Time} (hΔ : 0 < Δ) : 0 < G.slotLen Δ :=
  Int.mul_pos (by exact_mod_cast G.slotDeltas.pos) hΔ

theorem slotAt?_eq_some {Δ : Time} (hΔ : 0 < Δ) {off t : Time} {s : Slot} :
    G.slotAt? Δ off t = some s ↔ G.slotTime Δ s + off = t := by
  have hl := G.slotLen_pos hΔ
  unfold slotAt? slotTime
  by_cases hc : 0 ≤ t - off ∧ (t - off) % G.slotLen Δ = 0
  · rw [ite_eq_left hc, Option.some.injEq]
    obtain ⟨h0, hm⟩ := hc
    have hdiv : 0 ≤ (t - off) / G.slotLen Δ := Int.ediv_nonneg h0 hl.le
    have ht : (t - off) / G.slotLen Δ * G.slotLen Δ = t - off :=
      Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hm)
    constructor
    · rintro rfl
      rw [Int.toNat_of_nonneg hdiv, ht]; ring
    · intro he
      have : t - off = (s : Time) * G.slotLen Δ := by linarith
      rw [this, Int.mul_ediv_cancel _ hl.ne']; simp
  · rw [ite_eq_right hc]
    refine ⟨fun h => (nomatch h), fun he => ?_⟩
    have : t - off = (s : Time) * G.slotLen Δ := by linarith
    exact absurd ⟨this ▸ Int.mul_nonneg (by positivity) hl.le, this ▸ Int.mul_emod_left _ _⟩ hc

theorem slotTime_add {Δ : Time} (s j : Slot) :
    G.slotTime Δ (s + j) = G.slotTime Δ s + (j : Time) * G.slotLen Δ := by
  unfold slotTime; push_cast; ring

/-- Every window `(t, t + k · slotLen]` with `t ≥ 0` and `k ≥ 1` contains a slot
start. -/
theorem exists_slot_in_window {Δ : Time} (hΔ : 0 < Δ) {t : Time} (ht : 0 ≤ t) {k : Nat}
    (hk : 1 ≤ k) :
    ∃ s, t < G.slotTime Δ s ∧ G.slotTime Δ s ≤ t + k * G.slotLen Δ := by
  have hl := G.slotLen_pos hΔ
  refine ⟨(t / G.slotLen Δ).toNat + 1, ?_, ?_⟩
  · have hq : 0 ≤ t / G.slotLen Δ := Int.ediv_nonneg ht hl.le
    unfold slotTime
    push_cast
    rw [Int.toNat_of_nonneg hq]
    have := Int.lt_ediv_add_one_mul_self t hl
    linarith
  · have hq : 0 ≤ t / G.slotLen Δ := Int.ediv_nonneg ht hl.le
    unfold slotTime
    push_cast
    rw [Int.toNat_of_nonneg hq]
    have h1 := Int.ediv_mul_le t hl.ne'
    have hk' : (1 : Time) ≤ k := by exact_mod_cast hk
    nlinarith

end TimeGrid

/-! ## Progress requirements -/

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

variable {V : Type} [Fintype V]

variable {p : EnvPoint V} {key : Fin (Fintype.card V) ≃ V}
  {sel : Slot → Finset (Fin (Fintype.card V))} {G : TimeGrid}
  {ρ : Recurrence} {c start stop : Time}

/-- A later start and an earlier stop are weaker. -/
theorem PatternRecurrence.mono {start' stop' : Time}
    (h : PatternRecurrence p key sel G ρ c start stop) (hs : start ≤ start')
    (he : stop' ≤ stop) : PatternRecurrence p key sel G ρ c start' stop' :=
  fun t ht hst hh => h t (le_trans (max_le_max hs le_rfl) ht) (le_trans hst he) hh

/-- A smaller horizon is weaker. -/
theorem PatternRecurrence.shrink {b : Time} (hb : b ≤ p.horizon)
    (h : PatternRecurrence p key sel G ρ c start stop) :
    PatternRecurrence { p with horizon := b } key sel G ρ c start stop :=
  fun t ht hst hh => h t ht hst (le_trans hh hb)

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

/-- Head extraction: a pattern with offset `0` gives one honest ready proposer
per window, losing the pattern's span at the end of the window `[start, stop]`
(the single pattern reads only the window itself). -/
theorem PatternRecurrence.single_of_zero (h0 : 0 ∈ ρ.pattern.offsets)
    (h : PatternRecurrence p key sel G ρ c start stop) :
    PatternRecurrence p key sel G ⟨Pattern.single, ρ.gap⟩ c start
      (min stop p.horizon - (ρ.pattern.span : Time) * G.slotLen p.env.Δ) := by
  intro t ht hst _
  have hlen : ((⟨Pattern.single, ρ.gap⟩ : Recurrence).len : Time) = ((ρ.gap : Nat) : Time) := by
    simp [Recurrence.len, Pattern.span_single]
  have hlen' : (ρ.len : Time) = ((ρ.gap : Nat) : Time) + (ρ.pattern.span : Time) := by
    simp [Recurrence.len]
  rw [hlen] at hst
  have hm1 := min_le_left stop p.horizon
  have hm2 := min_le_right stop p.horizon
  obtain ⟨s, hs1, hs2, hall⟩ := h t ht (by rw [hlen']; linarith) (by rw [hlen']; linarith)
  refine ⟨s, hs1, hs2, fun j hj => ?_⟩
  have hj0 : j = 0 := List.mem_singleton.mp hj
  subst hj0
  exact hall 0 h0

/-- If every slot has an honest ready pattern, recurrence holds on every
window (no domain hypothesis: windows start at `t ≥ 0`, gaps are positive). -/
theorem patternRecurrence_of_all (hΔ : 0 < p.env.Δ)
    (h : ∀ s j, j ∈ ρ.pattern.offsets →
      HonestReadyIn p key sel (s + j) c (G.slotTime p.env.Δ (s + j))) :
    PatternRecurrence p key sel G ρ c start stop := by
  intro t ht _ _
  obtain ⟨s, hs₁, hs₂⟩ :=
    G.exists_slot_in_window hΔ (le_trans (le_max_right _ _) ht) (k := (ρ.gap : Nat)) ρ.gap.pos
  exact ⟨s, hs₁, hs₂, fun j hj => h s j hj⟩

/-- The periodic bad slots of a recurrence with slack: with period
`P = span + 2`, the slots `s` with `s % P = P − 1`. Every `gap ≥ P`
consecutive slots contain one. -/
theorem Recurrence.exists_bad_slot (hρ : ρ.BadSlotSlack) (a : Nat) :
    ∃ s, a ≤ s ∧ s < a + (ρ.gap : Nat) ∧
      s % (ρ.pattern.span + 2) = ρ.pattern.span + 1 := by
  unfold Recurrence.BadSlotSlack at hρ
  have hd := Nat.mod_add_div a (ρ.pattern.span + 2)
  have hm := Nat.mod_lt a (show 0 < ρ.pattern.span + 2 by omega)
  refine ⟨(ρ.pattern.span + 2) * (a / (ρ.pattern.span + 2)) + (ρ.pattern.span + 1), ?_, ?_, ?_⟩
  · omega
  · omega
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- A start slot `s` with `s % (span + 2) = 0` has its whole pattern off the
periodic bad slots. -/
theorem Recurrence.pattern_good {s j : Nat} (hs : s % (ρ.pattern.span + 2) = 0)
    (hj : j ∈ ρ.pattern.offsets) : (s + j) % (ρ.pattern.span + 2) ≠ ρ.pattern.span + 1 := by
  have hjs := Pattern.le_span hj
  rw [Nat.add_mod, hs, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega : j < _)]
  omega

/-- Recurrence with a bad slot in every window: if the pattern is honest and
ready from every start slot `s` with `s % (span + 2) = 0` (the periodic bad
slots `s % (span + 2) = span + 1` are avoided, `Recurrence.pattern_good`),
and the gap has the slack `span + 2 ≤ gap`, recurrence holds on every window,
although every window holds a bad slot (`Recurrence.exists_bad_slot`). -/
theorem patternRecurrence_of_periodic (hΔ : 0 < p.env.Δ) (hρ : ρ.BadSlotSlack)
    (h : ∀ s j, s % (ρ.pattern.span + 2) = 0 → j ∈ ρ.pattern.offsets →
      HonestReadyIn p key sel (s + j) c (G.slotTime p.env.Δ (s + j))) :
    PatternRecurrence p key sel G ρ c start stop := by
  intro t ht _ _
  unfold Recurrence.BadSlotSlack at hρ
  obtain ⟨P, hP⟩ : ∃ P, P = ρ.pattern.span + 2 := ⟨_, rfl⟩
  rw [← hP] at h
  have hl := G.slotLen_pos hΔ
  obtain ⟨s₁, hs₁, hs₁'⟩ : ∃ s₁ : ℕ, t < G.slotTime p.env.Δ s₁ ∧
      G.slotTime p.env.Δ s₁ ≤ t + ((1 : ℕ) : Time) * G.slotLen p.env.Δ :=
    G.exists_slot_in_window hΔ (le_trans (le_max_right _ _) ht) (k := 1) le_rfl
  obtain ⟨x, hx⟩ : ∃ x : Nat, x = s₁ + (P - 1) := ⟨_, rfl⟩
  have hd := Nat.mod_add_div x P
  have hm := Nat.mod_lt x (show 0 < P by omega)
  obtain ⟨m, hm'⟩ : ∃ m, m = x / P := ⟨_, rfl⟩
  rw [← hm'] at hd
  have hlo : s₁ ≤ P * m := by omega
  have hhi : P * m ≤ s₁ + (P - 1) := by omega
  refine ⟨P * m, ?_, ?_, fun j hj => h _ j (Nat.mul_mod_right _ _) hj⟩
  · obtain ⟨d, hd'⟩ := Nat.exists_eq_add_of_le hlo
    rw [hd', G.slotTime_add]
    have : (0 : Time) ≤ (d : Time) * G.slotLen p.env.Δ := by positivity
    linarith
  · obtain ⟨d, hd'⟩ := Nat.exists_eq_add_of_le hlo
    have hdP : d ≤ P - 1 := by omega
    rw [hd', G.slotTime_add]
    have hd'' : (d : Time) + 1 ≤ ((ρ.gap : Nat) : Time) := by
      have : d + 1 ≤ (ρ.gap : Nat) := by omega
      exact_mod_cast this
    push_cast at hs₁'
    nlinarith

/-- With one whole window inside `[max start 0, stop]` and the horizon,
recurrence yields a start slot whose whole pattern is honest, ready and inside
the horizon. -/
theorem PatternRecurrence.exists_inside (h : PatternRecurrence p key sel G ρ c start stop)
    (hs : max start 0 + (ρ.len : Time) * G.slotLen p.env.Δ ≤ stop)
    (ht : max start 0 + (ρ.len : Time) * G.slotLen p.env.Δ ≤ p.horizon) :
    ∃ s, ∀ j ∈ ρ.pattern.offsets, G.slotTime p.env.Δ (s + j) ≤ p.horizon ∧
      HonestReadyIn p key sel (s + j) c (G.slotTime p.env.Δ (s + j)) := by
  have hl := G.slotLen_pos p.env.Δ_pos
  obtain ⟨s, -, hs', hall⟩ := h (max start 0) le_rfl hs ht
  refine ⟨s, fun j hj => ⟨?_, hall j hj⟩⟩
  have hj' : (j : Time) ≤ ρ.pattern.span := by exact_mod_cast Pattern.le_span hj
  have hlen : (ρ.len : Time) = ((ρ.gap : Nat) : Time) + (ρ.pattern.span : Time) := by
    simp [Recurrence.len]
  rw [hlen] at ht
  rw [G.slotTime_add]
  nlinarith

/-! ## Payload -/

@[simp] theorem decode_encodeTxs (xs : List Tx) : decodeTxs (encodeTxs xs) = xs := by
  simp [decodeTxs, encodeTxs]

variable {Info : Type}

/-- `ledgerOf` is monotone under prefixes. -/
theorem ledgerOf_prefix {c d : Chain Info} (h : c <+: d) : ledgerOf c <+: ledgerOf d := by
  obtain ⟨es, rfl⟩ := h
  unfold ledgerOf
  rw [List.flatMap_append, List.eraseDups_append]
  exact List.prefix_append _ _

@[simp] theorem mem_ledgerOf (x : Tx) (c : Chain Info) :
    x ∈ ledgerOf c ↔ ∃ h ∈ c, x ∈ decodeTxs h.input := by
  simp [ledgerOf, List.mem_eraseDups, List.mem_flatMap, Function.comp_def]

end Consensus.Blocks
end
