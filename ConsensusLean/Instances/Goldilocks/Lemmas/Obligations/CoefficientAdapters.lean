module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
public import ConsensusLean.Lemmas.Blocks.Facts
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Conditional coefficient adapters

Arithmetic and recurrence from workbench `coefficient-envelope-current.md` at 6414ac9.
These bounds do not choose the shared witnesses or supply semantic service producers.
All readiness comparisons use the same interval; changing catch-up does not recover
progress opportunities before the new start.
-/

namespace Consensus.Goldilocks.Obligations
open AsChainShape
open Blocks

/-- Convert a nonnegative node-delay tail to engine units, including a literal offset. -/
theorem node_tail_le_engine {d B r : Time} (hd : 1 ≤ d) (hB : 0 ≤ B) (hr : 0 ≤ r) :
    B * (d + 1) + r ≤ (2 * B + r) * d := by
  nlinarith [mul_nonneg hB (show 0 ≤ d - 1 by linarith),
    mul_nonneg hr (show 0 ≤ d - 1 by linarith)]

/-- Maturity includes catch-up inside healing, with the readiness unit charged once. -/
theorem ready_le_heal {g d c h : Time} (hd : 1 ≤ d) (hh : c + 1 ≤ h) :
    max g 0 + c * d + 1 ≤ max g 0 + h * d := by
  nlinarith

/-- A producer taking `B(d+1)+r` after ready fits in this conditional healing budget. -/
theorem ready_tail_le_heal {g d c h B r : Time} (hd : 1 ≤ d)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hh : c + 2 * B + r + 1 ≤ h) :
    max g 0 + c * d + 1 + (B * (d + 1) + r) ≤ max g 0 + h * d := by
  have := node_tail_le_engine hd hB hr
  nlinarith

/-- Strict pre-read reserve, including the worst one-unit stored-clock lag.
`B` is the semantic repair budget; `K` is an independent budget sharing the envelope.
The extra two units over completion-at-heal are literal integer units. -/
theorem repair_lt_heal_sub_one {g d c h B K r τ : Time} (hd : 1 ≤ d)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hh : c + 2 * max B K + r + 3 ≤ h)
    (hrepair : τ ≤ max g 0 + c * d + 1 + (B * (d + 1) + r)) :
    τ < max g 0 + h * d - 1 := by
  have hbudget : c + 2 * B + (r + 2) + 1 ≤ h := by
    have := le_max_left B K
    linarith
  have htail := ready_tail_le_heal (g := g) hd hB
    (show 0 ≤ r + 2 by linarith) hbudget
  linarith

/-- The four-anchor recurrence (span `3c`, `c = cF r`) and an independently supplied semantic tail
fit in `L`. -/
theorem final_recurrence_tail_le_latency (S : Setup) (A : ContractAssumptions S) (X : ℕ+)
    {d B r L : Time} (hd : 1 ≤ d) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hL : 8 * ((X : Nat) + 3 * cF A.fgDelay) + 2 * B + r ≤ L) :
    4 * ((X : Nat) + 3 * cF A.fgDelay) * (d + 1) +
      (B * (d + 1) + r) ≤ L * d := by
  have hX : 0 ≤ (X : Time) := by positivity
  have := node_tail_le_engine hd
    (show 0 ≤ 4 * ((X : Nat) + 3 * cF A.fgDelay) + B by linarith) hr
  nlinarith

/-- Recurrence is queried at the integer query itself: no fresh-slot rounding phase.
The entire window must fit both the stop and the finite horizon. -/
theorem final_recurrence_anchors (S : Setup) (A : ContractAssumptions S) (X : ℕ+)
    {V : Type} [Fintype V] {p : EnvPoint V}
    {key : Fin (Fintype.card V) ≃ V} {sel : Slot → Finset (Fin (Fintype.card V))}
    {G : TimeGrid} {d c start stop query : Time}
    (hG : G.slotLen = 4 * (d + 1))
    (hp : PatternRecurrence p key sel G ⟨finalWindow A, X⟩ c start stop)
    (hq : max start 0 ≤ query)
    (hs : query + 4 * ((X : Nat) + 3 * cF A.fgDelay) * (d + 1) ≤ stop)
    (hh : query + 4 * ((X : Nat) + 3 * cF A.fgDelay) * (d + 1) ≤ p.horizon) :
    ∃ s, query < G.slotTime s ∧
      ∀ j ∈ (finalWindow A).offsets,
        G.slotTime (s + j) ≤ query +
          4 * ((X : Nat) + 3 * cF A.fgDelay) * (d + 1) ∧
        HonestReadyIn p key sel (s + j) c (G.slotTime (s + j)) := by
  have hlen : ((⟨finalWindow A, X⟩ : Recurrence).len : Time) * G.slotLen =
      4 * ((X : Nat) + 3 * cF A.fgDelay) * (d + 1) := by
    simp only [Recurrence.len, finalWindow_span, hG]
    push_cast
    ring
  obtain ⟨s, hfresh, hfirst, hready⟩ := hp query hq (by rwa [hlen]) (by rwa [hlen])
  refine ⟨s, hfresh, fun j hj => ⟨?_, hready j hj⟩⟩
  have hjbound : (j : Time) ≤ 3 * (cF A.fgDelay : Time) := by
    have := Pattern.le_span hj
    rw [finalWindow_span] at this
    exact_mod_cast this
  rw [G.slotTime_add]
  have hmul := mul_le_mul_of_nonneg_right hjbound G.slotLen_pos.le
  rw [hG] at hfirst hmul ⊢
  linarith

/-- Longer ready histories imply shorter ones, not conversely. -/
theorem ready_of_duration_le {V : Type} {p : EnvPoint V} {v : V} {c₁ c₂ t : Time}
    (hc : c₁ ≤ c₂) (h : p.Ready c₂ v t) : p.Ready c₁ v t := by
  refine ⟨h.1, fun u hu hut => h.2 u ?_ hut⟩
  exact (max_le_max_left 0 (by linarith)).trans hu

/-- Readiness can be weakened on the same recurrence interval without moving its start. -/
theorem recurrence_of_duration_le {V : Type} [Fintype V] {p : EnvPoint V}
    {key : Fin (Fintype.card V) ≃ V} {sel : Slot → Finset (Fin (Fintype.card V))}
    {G : TimeGrid} {ρ : Recurrence} {c₁ c₂ start stop : Time}
    (hc : c₁ ≤ c₂) (h : PatternRecurrence p key sel G ρ c₂ start stop) :
    PatternRecurrence p key sel G ρ c₁ start stop := by
  intro t ht hs hh
  obtain ⟨s, hfirst, hlast, hall⟩ := h t ht hs hh
  refine ⟨s, hfirst, hlast, fun j hj => ?_⟩
  exact ⟨(hall j hj).1, fun k hk => ready_of_duration_le hc ((hall j hj).2 k hk)⟩

/-- A sufficient coefficient for retaining the whole node-delay tail in ready history. -/
theorem node_tail_le_ready_history {d B r c : Time} (hd : 1 ≤ d)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hc : 2 * B + r ≤ c) :
    B * (d + 1) + r ≤ c * d + 1 := by
  have := node_tail_le_engine hd hB hr
  nlinarith

/-- Choose a later-reader opening after all three lower bounds and inside ready history.
This only supplies timing and wakefulness, not the missing semantic producer. -/
theorem ready_reader_opening {V : Type} {p : EnvPoint V} {v : V}
    {s g t c d R : Time} (ht : max (max s g) 0 + R ≤ t)
    (hR : R ≤ c * d + 1) (hready : p.Ready (c * d) v t) :
    let a := max (max (max s g) 0) (t - c * d - 1)
    s ≤ a ∧ g ≤ a ∧ 0 ≤ a ∧ a + R ≤ t ∧ p.AwakeOnClosed v a t := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, fun u hu hut => hready.2 u ?_ hut⟩
  · exact le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
  · exact le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
  · exact le_max_of_le_left (le_max_right _ _)
  · have := (max_le (by linarith) (by linarith) :
      max (max (max s g) 0) (t - c * d - 1) ≤ t - R)
    linarith
  · exact max_le (le_trans (le_max_of_le_left (le_max_right _ _)) hu)
      (le_trans (le_max_right _ _) hu)

end Consensus.Goldilocks.Obligations
