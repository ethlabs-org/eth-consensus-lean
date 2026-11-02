module
public import ConsensusLean.Spec.Blocks.Progress

public section

/-! # Goldilocks Refinement: two-query placement of the seed and the window (#136, route A)

consensus-lean#136, workbench `window_start_h0.md` §6 and `route_a_gap2.md` §3. Pure time and slot
arithmetic on the results of `PatternRecurrence`. Query 1 at `t₁ = max(max start 0,
slotTime(u_min) − 1)` returns the seed slot `u ≥ u_min`; query 2 at `q` returns the window start
`s₀`. Under the placement condition `(P)`, `t₁ + (gap + δt)·slotLen ≤ q + slotLen`, the seed is
at least `δt` slots before the window: `u + δt ≤ s₀`. Query 1 fits whenever query 2 fits.

No producer is assumed: the duties are `HonestReadyIn`, not proposals (duty → proposal is the
adapter's step). -/

namespace Consensus.Goldilocks.Refinement

open Consensus.Blocks

variable {V : Type} [Fintype V]

/-- `slotTime` is order-reflecting. -/
private theorem slot_le_of_slotTime_le (G : TimeGrid) {s s' : Slot}
    (h : G.slotTime s ≤ G.slotTime s') : s ≤ s' := by
  unfold TimeGrid.slotTime at h
  have := G.slotLen_pos
  have h' : (s : Int) ≤ s' := le_of_mul_le_mul_right h this
  exact_mod_cast h'

/-- **Query 1 fits when query 2 fits.** Under `(P)`, a pattern read from `t₁` ends by the end of
the pattern read from `q`. -/
theorem query_one_fit (G : TimeGrid) (ρ : Recurrence) {δt : Nat} {t₁ q : Time}
    (hP : t₁ + (((ρ.gap : Nat) + δt : Nat) : Time) * G.slotLen ≤ q + G.slotLen) :
    t₁ + (ρ.len : Time) * G.slotLen ≤ q + (ρ.len : Time) * G.slotLen := by
  have hL := G.slotLen_pos
  have hg : (1 : Time) ≤ ((ρ.gap : Nat) : Time) := by exact_mod_cast ρ.gap.pos
  unfold Recurrence.len
  push_cast at hP ⊢
  nlinarith

/-- **Two-query placement.** Query 1 at `t₁ = max(max start 0, slotTime(u_min) − 1)` gives a seed
slot `u ≥ u_min`, `0 < u`, with its offset-0 duty; query 2 at `q ≥ max start 0` gives the window
start `s₀` with all its duties. Under `(P)`, `u + δt ≤ s₀`; the window's pattern ends by
`q + len·slotLen`. Only the fit of query 2 is assumed (`query_one_fit`). -/
theorem two_query_placement {p : EnvPoint V} {key : Fin (Fintype.card V) ≃ V}
    {sel : Slot → Finset (Fin (Fintype.card V))} {G : TimeGrid} {ρ : Recurrence}
    {c start stop : Time} (hrec : PatternRecurrence p key sel G ρ c start stop)
    (h0 : 0 ∈ ρ.pattern.offsets) {u_min δt : Nat} {q : Time}
    (hP : max (max start 0) (G.slotTime u_min - 1) +
      (((ρ.gap : Nat) + δt : Nat) : Time) * G.slotLen ≤ q + G.slotLen)
    (hq : max start 0 ≤ q) (hstop : q + (ρ.len : Time) * G.slotLen ≤ stop)
    (hhor : q + (ρ.len : Time) * G.slotLen ≤ p.horizon) :
    ∃ u s₀ : Slot, u_min ≤ u ∧ 0 < u ∧ u + δt ≤ s₀ ∧
      G.slotTime u ≤ max (max start 0) (G.slotTime u_min - 1) +
        ((ρ.gap : Nat) : Time) * G.slotLen ∧
      HonestReadyIn p key sel u c (G.slotTime u) ∧
      q < G.slotTime s₀ ∧ G.slotTime s₀ ≤ q + ((ρ.gap : Nat) : Time) * G.slotLen ∧
      G.slotTime (s₀ + ρ.pattern.span) ≤ q + (ρ.len : Time) * G.slotLen ∧
      ∀ j ∈ ρ.pattern.offsets, HonestReadyIn p key sel (s₀ + j) c (G.slotTime (s₀ + j)) := by
  set t₁ := max (max start 0) (G.slotTime u_min - 1) with ht₁
  have hL := G.slotLen_pos
  have hfit := query_one_fit G ρ hP
  obtain ⟨u, hu1, hu2, hdu⟩ := hrec t₁ (le_max_left _ _) (hfit.trans hstop) (hfit.trans hhor)
  obtain ⟨s₀, hs1, hs2, hds⟩ := hrec q hq hstop hhor
  have hmin : u_min ≤ u := by
    refine slot_le_of_slotTime_le G ?_
    have : G.slotTime u_min - 1 < G.slotTime u := lt_of_le_of_lt (le_max_right _ _) hu1
    exact Int.le_of_sub_one_lt this
  have hpos : 0 < u := by
    refine Nat.pos_of_ne_zero fun hz => ?_
    subst hz
    have : (0 : Time) ≤ t₁ := (le_max_right start 0).trans (le_max_left _ _)
    simp [TimeGrid.slotTime] at hu1
    linarith
  have hsep : u + δt ≤ s₀ := by
    have hlt : ((u + δt : Nat) : Time) * G.slotLen < (s₀ + 1 : Int) * G.slotLen := by
      unfold TimeGrid.slotTime at hu2 hs1
      push_cast at hP hu2 hs1 ⊢
      nlinarith
    have h1 := lt_of_mul_lt_mul_right hlt hL.le
    have h2 : u + δt < s₀ + 1 := by exact_mod_cast h1
    exact Nat.lt_succ_iff.mp h2
  have hspan : G.slotTime (s₀ + ρ.pattern.span) ≤ q + (ρ.len : Time) * G.slotLen := by
    unfold TimeGrid.slotTime at hs2 ⊢
    unfold Recurrence.len
    push_cast at hs2 ⊢
    nlinarith
  exact ⟨u, s₀, hmin, hpos, hsep, hu2, hdu 0 h0, hs1, hs2, hspan, hds⟩

end Consensus.Goldilocks.Refinement

end
