module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.WindowAnchors
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealedUpTo
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Obligations: window coverage from four anchors, through a horizon

`anchors_chain_upTo` and `window_anchors_chain_upTo`:
The anchor part of S3 (`WindowAnchors`) from `ResetPremisesUpTo … b`, by C4 through the horizon
(`honest_proposal_below_next_upTo`, `honest_proposal_below_later_upTo`). Guards: the later
proposal of each pair has `t_{s₁} ≤ b`, and an adjacent pair `s₁ = s₀ + 1` also has the service
reserve `t_{s₀} + 6Δ ≤ b`. For the four anchors this is `t_{s 3} ≤ b` and, when `s 3 = s 2 + 1`,
`t_{s 2} + 6Δ ≤ b`: every other adjacent pair `(i, j)` has `s i + 2 ≤ s 3`, so
`t_{s i} + 8Δ ≤ t_{s 3}`. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- **S3, anchor part, through the horizon** (from `ResetPremisesUpTo … b`):
with `t_{s₁} ≤ b`, and `t_{s₀} + 6Δ ≤ b` when `s₁ = s₀ + 1`. -/
theorem anchors_chain_upTo (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {s₀ s₁ : Nat}
    {P₀ P₁ : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP₀ : Healing.HonestProposalRun tr H proposer s₀ P₀)
    (hR : Healing.drainTime sp a ≤ sp.ts s₀)
    (hP₁ : Healing.HonestProposalRun tr H proposer s₁ P₁) (hs : s₀ < s₁)
    (hb : sp.ts s₁ ≤ b) (hadj : s₁ = s₀ + 1 → sp.ts s₀ + 6 * sp.Δ ≤ b) :
    Anc (tr.HonestBlocks H) P₀ P₁ := by
  rcases Nat.lt_or_ge s₁ (s₀ + 2) with hl | hl
  · obtain rfl : s₁ = s₀ + 1 := by omega
    exact honest_proposal_below_next_upTo hp hc hP₀ hR hP₁ (hadj rfl)
  · exact honest_proposal_below_later_upTo hp hc hP₀ hR hP₁ hl hb

/-- Two slots apart, the slot times are `8Δ` apart. -/
private theorem ts_add_eight_le {m n : Nat} (h : m + 2 ≤ n) :
    sp.ts m + 8 * sp.Δ ≤ sp.ts n := by
  have e : sp.ts (m + 2 : Nat) = sp.ts m + 8 * sp.Δ := by
    simp only [SA.SAParams.ts]; push_cast; ring
  have : sp.ts (m + 2 : Nat) ≤ sp.ts n := (SA.ts_le_iff sp).2 (by push_cast; omega)
  linarith

/-- The ordered pairs of `Fin 4`: the last pair, a pair below `3`, or a pair `(i, 3)`, `i < 2`. -/
private theorem fin4_pairs : ∀ i j : Fin 4, i < j →
    (i = 2 ∧ j = 3) ∨ j < 3 ∨ (i < 2 ∧ j = 3) := by decide

/-- **S3, anchor part, for four anchors, through the horizon** (from
`ResetPremisesUpTo … b`): with `t_{s 3} ≤ b`, and `t_{s 2} + 6Δ ≤ b` when `s 3 = s 2 + 1`. -/
theorem window_anchors_chain_upTo (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {s : Fin 4 → Nat}
    {P : Fin 4 → SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ∀ i, Healing.HonestProposalRun tr H proposer (s i) (P i)) (hs : StrictMono s)
    (hR : Healing.drainTime sp a ≤ sp.ts (s 0)) (hb : sp.ts (s 3) ≤ b)
    (hadj : s 3 = s 2 + 1 → sp.ts (s 2) + 6 * sp.Δ ≤ b) :
    ∀ i j, i ≤ j → Anc (tr.HonestBlocks H) (P i) (P j) := by
  intro i j hij
  rcases hij.lt_or_eq with hlt | rfl
  · have hRi : Healing.drainTime sp a ≤ sp.ts (s i) :=
      hR.trans ((SA.ts_le_iff sp).2 (by exact_mod_cast hs.monotone (Fin.zero_le i)))
    have hj3 : s j ≤ s 3 := hs.monotone (Fin.le_last j)
    have hjb : sp.ts (s j) ≤ b := ((SA.ts_le_iff sp).2 (by exact_mod_cast hj3)).trans hb
    refine anchors_chain_upTo hp hc (hP i) hRi (hP j) (hs hlt) hjb fun he => ?_
    have hΔ := sp.toParams.hΔ
    rcases fin4_pairs i j hlt with ⟨rfl, rfl⟩ | hj | ⟨hi, rfl⟩
    · exact hadj he
    · have := hs hj
      linarith [ts_add_eight_le (sp := sp) (by omega : s i + 2 ≤ s 3)]
    · have := hs hi
      have := hs (by decide : (2 : Fin 4) < 3)
      omega
  · exact Relation.ReflTransGen.refl

end Consensus.Goldilocks.Obligations

end
