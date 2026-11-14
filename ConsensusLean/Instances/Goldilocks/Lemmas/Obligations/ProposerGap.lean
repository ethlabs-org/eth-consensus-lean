module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Suffix
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Goldilocks Obligations: the proposer gap core

The upstream core of the honest-proposer gap.

* `recurrence_gap`: a recurrence whose pattern has offset `0` gives an honest-ready duty in every
  window `[a, a + gap)` inside `[s₀, N]`. The query is at `t = slotTime a − slotLen`: the start
  slot `s` has `t < slotTime s ≤ t + gap · slotLen`, so `a ≤ s ≤ a + gap − 1`. The window gap is
  `G = gap`, not `gap + span + 1`: the span enters only the margin
  `slotTime N + span · slotLen ≤ min stop horizon`.
-/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Blocks Shape

section Gap

variable {V : Type} [Fintype V] {p : EnvPoint V} {key : Fin (Fintype.card V) ≃ V}
  {sel : Slot → Finset (Fin (Fintype.card V))} {G : TimeGrid} {ρ : Recurrence}
  {c start stop : Time}

/-- **The duty gap of a recurrence.** With offset `0` in the pattern, every slot window
`[a, a + gap)` inside `[s₀, N]` has a slot whose selected keys are honest and ready, when
`max start 0 + slotLen ≤ slotTime s₀` and the pattern of slot `N` ends by `stop` and by the
horizon. -/
theorem recurrence_gap (h : PatternRecurrence p key sel G ρ c start stop)
    (h0 : 0 ∈ ρ.pattern.offsets) {s₀ N : Nat}
    (hs : max start 0 + G.slotLen ≤ G.slotTime s₀)
    (hstop : G.slotTime N + (ρ.pattern.span : Time) * G.slotLen ≤ stop)
    (hhor : G.slotTime N + (ρ.pattern.span : Time) * G.slotLen ≤ p.horizon) :
    ∀ a, s₀ ≤ a → a + (ρ.gap : Nat) ≤ N + 1 → ∃ x, a ≤ x ∧ x < a + (ρ.gap : Nat) ∧
      HonestReadyIn p key sel x c (G.slotTime x) (ρ.hold * p.env.ΔAC) := by
  intro a ha haN
  have hL := G.slotLen_pos
  have hlen : (ρ.len : Time) = ((ρ.gap : Nat) : Time) + (ρ.pattern.span : Time) := by
    simp [Recurrence.len]
  have hg1 : 1 ≤ (ρ.gap : Nat) := ρ.gap.pos
  have haN' : ((a : Time) + ((ρ.gap : Nat) : Time)) ≤ (N : Time) + 1 := by exact_mod_cast haN
  have hsa : G.slotTime s₀ ≤ G.slotTime a := by
    unfold TimeGrid.slotTime
    have : (s₀ : Time) ≤ (a : Time) := by exact_mod_cast ha
    exact mul_le_mul_of_nonneg_right this hL.le
  have hend : G.slotTime a - G.slotLen + (ρ.len : Time) * G.slotLen ≤
      G.slotTime N + (ρ.pattern.span : Time) * G.slotLen := by
    unfold TimeGrid.slotTime
    rw [hlen]
    linarith [mul_le_mul_of_nonneg_right haN' hL.le]
  obtain ⟨s, hs₁, hs₂, hall⟩ := h (G.slotTime a - G.slotLen) (by linarith)
    (hend.trans hstop) (hend.trans hhor)
  have hall0 := hall 0 h0
  rw [Nat.add_zero] at hall0
  unfold TimeGrid.slotTime at hs₁ hs₂
  have hlo : ((a : Time) - 1) * G.slotLen < (s : Time) * G.slotLen := by linarith
  have hhi : (s : Time) * G.slotLen ≤ ((a : Time) - 1 + ((ρ.gap : Nat) : Time)) * G.slotLen := by
    linarith
  have hlo' : (a : Int) - 1 < (s : Int) := lt_of_mul_lt_mul_right hlo hL.le
  have hhi' : (s : Int) ≤ (a : Int) - 1 + ((ρ.gap : Nat) : Int) :=
    le_of_mul_le_mul_right hhi hL
  refine ⟨s, ?_, ?_, hall0⟩
  · omega
  · omega

end Gap

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The run catch-up duration covers the protocol catch-up `18 Δp`. -/
theorem catchUp_le_cDur (run : (Sys (goldilocks S) V).Run) (hn : 1 ≤ Fintype.card V) :
    Regimes.catchUp (S.params (Model.pubOf run.1) hn) ≤
        (Sys (goldilocks S) V).cDur (K S A) run := by
  have hd : (1 : Time) ≤ run.1.ΔAC := run.1.ΔAC_pos
  have hc : (19 : Time) ≤ ((K S A).params.catchUp : Time) := by
    rw [goldilocksContract_params_eq]
    change (19 : Time) ≤ ((contract_coefficients S A).catchUp : Nat)
    rw [contract_coefficients_catchUp]
    exact_mod_cast contract_catchUp_ge_sleepy S A
  change 18 * run.1.ΔAC ≤ ((K S A).params.catchUp : Time) * run.1.ΔAC
  linarith [mul_le_mul_of_nonneg_right hc (zero_le_one.trans hd)]

end Consensus.Goldilocks.Obligations

end
