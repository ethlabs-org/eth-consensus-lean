module
public import AvailableChainGridCO.Proofs.StoreFacts
public import AvailableChainGridCO.Statements.Contract
public import Mathlib.Tactic.Ring

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic
open AvailableChain.Statements.Generic

theorem lifetime_nonneg (p : Params) : 0 ≤ lifetime p := by
  unfold lifetime
  have hm : (2 : ℤ) ≤ p.m := by exact_mod_cast p.mLarge
  have hc : 0 ≤ 4 * (p.m : ℤ) - 1 := by omega
  exact mul_nonneg hc (le_of_lt p.deltaPos)

theorem gridConstants_valid (p : Params) (G : Time) (hG : 0 < G) :
    (gridConstants p G).Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact p.thetaLower
  · exact p.thetaUpper
  · norm_num [gridConstants]
  · norm_num [gridConstants]
  · exact p.etaNonneg
  · dsimp [gridConstants]
    have h : 0 ≤ 6 * p.Δ := mul_nonneg (by norm_num) (le_of_lt p.deltaPos)
    exact ⟨h, h, h⟩
  · dsimp [gridConstants]
    exact mul_nonneg (by norm_num) (le_of_lt p.deltaPos)
  · dsimp [gridConstants]; linarith [p.deltaPos]
  · exact le_refl _
  · dsimp [gridConstants]
    exact le_min p.etaNonneg (lifetime_nonneg p)
  · dsimp [gridConstants]
    exact min_le_left _ _
  · dsimp [gridConstants]
    have hK : (0 : Time) ≤ p.grid.card := Int.natCast_nonneg _
    have hL : 0 ≤ lifetime p + p.Δ := by linarith [lifetime_nonneg p, p.deltaPos]
    have hprod := mul_nonneg hK hL
    nlinarith [p.deltaPos, hG]
  · exact hG

/-- The release cutoff is the next HEAD time. -/
theorem release_eq_next_vote (p : Params) (r : Slot) :
    releaseTime p r = voteTime p (r + 1) := by
  simp [releaseTime, voteTime, proposalTime, Nat.cast_add]
  ring

theorem lifetime_pos (p : Params) : 0 < lifetime p := by
  unfold lifetime
  have hm : (2 : Time) ≤ p.m := by exact_mod_cast p.mLarge
  have hc : 0 < 4 * (p.m : Time) - 1 := by linarith
  exact mul_pos hc p.deltaPos

private theorem foldl_max_le (xs : List Nat) (acc bound : Nat)
    (hacc : acc ≤ bound) (hall : ∀ g ∈ xs, g ≤ bound) :
    xs.foldl max acc ≤ bound := by
  induction xs generalizing acc with
  | nil => simpa using hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact max_le hacc (hall x (by simp))
      · intro g hg
        exact hall g (by simp [hg])

private theorem acc_le_foldl_max (xs : List Nat) (acc : Nat) :
    acc ≤ xs.foldl max acc := by
  induction xs generalizing acc with
  | nil => exact le_refl _
  | cons x xs ih =>
      exact le_trans (le_max_left acc x) (ih (max acc x))

private theorem mem_le_foldl_max (xs : List Nat) (acc g : Nat)
    (hg : g ∈ xs) : g ≤ xs.foldl max acc := by
  induction xs generalizing acc with
  | nil => simp at hg
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hg with h | h
      · subst x
        exact le_trans (le_max_right acc g) (acc_le_foldl_max xs (max acc g))
      · exact ih (max acc x) h

/-- Rounding never produces a level above observed support. -/
theorem roundedLevel_le (p : Params) (h : Nat) : roundedLevel p h ≤ h := by
  unfold roundedLevel gridLevel
  apply foldl_max_le
  · exact Nat.zero_le _
  · intro g hg
    have hp := (List.mem_filter.mp hg).2
    have hp' : g ∈ p.grid ∧ g ≤ h := by simpa using hp
    exact hp'.2

/-- More observed support cannot lower the selected fixed grid level. -/
theorem roundedLevel_mono (p : Params) {h k : Nat} (hhk : h ≤ k) :
    roundedLevel p h ≤ roundedLevel p k := by
  unfold roundedLevel gridLevel
  apply foldl_max_le
  · exact Nat.zero_le _
  · intro g hg
    have hmem : g ∈ (List.range (p.n + 1)).filter
        (fun x => x ∈ p.grid && x ≤ k) := by
      apply List.mem_filter.mpr
      obtain ⟨hrange, htest⟩ := List.mem_filter.mp hg
      have hp : g ∈ p.grid ∧ g ≤ h := by simpa using htest
      exact ⟨hrange, by simp [hp.1, le_trans hp.2 hhk]⟩
    exact mem_le_foldl_max _ 0 g hmem

/-- A positive support always reaches at least the grid's level one. -/
theorem one_le_roundedLevel (p : Params) (h : Nat) (hh : 1 ≤ h) :
    1 ≤ roundedLevel p h := by
  have hn : 1 ≤ p.n := p.levels_le 1 p.one_mem
  have hm : 1 ∈ (List.range (p.n + 1)).filter
      (fun g => g ∈ p.grid && g ≤ h) := by
    apply List.mem_filter.mpr
    constructor
    · exact List.mem_range.mpr (Nat.lt_succ_of_le hn)
    · simp [p.one_mem, hh]
  unfold roundedLevel gridLevel
  exact mem_le_foldl_max _ 0 1 hm

/-- The exposed outputs are nested at every honest read, in every run. -/
theorem outputOrder {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) : OutputOrder (gridCO p) (gridInterface p) rho := by
  refine ⟨?_⟩
  intro v hv t
  exact block_preceq_self _

/-- The release step only deletes existing obligations. -/
theorem release_subset (p : Params) {n : Nat} (st : State n) (r : Slot)
    (row : Block × Nat × Time)
    (h : row ∈ (release p st r).obligations) : row ∈ st.obligations := by
  simp only [release, List.mem_filter] at h
  exact h.1

/-- An accepted result that conflicts with a live target cannot change S
or write obligations at this gate. The raw G record may still advance. -/
theorem gate_veto (p : Params) {n : Nat} (st : State n) (r : Slot)
    (h : Block) (hc : confirmation p st r = some h)
    (hv : st.obligations.any (fun (target, _, _) =>
      !Block.compatible target h) = true) :
    (gate p st r).stableRecord = st.stableRecord ∧
      (gate p st r).obligations = st.obligations := by
  simp [gate, hc, hv]

theorem next_gate_four_delta (p : Params) (r : Slot) :
    gateTime p (r + 1) = gateTime p r + 4 * p.Δ := by
  simp [gateTime, proposalTime, Nat.cast_add]
  ring

/-- One recovery stage advances exactly m HEAD labels. -/
theorem healing_stage_time (p : Params) (r k : Nat) :
    voteTime p (r + k * p.m) = voteTime p r + (k : Time) * (lifetime p + p.Δ) := by
  simp only [voteTime, proposalTime, lifetime, Nat.cast_add, Nat.cast_mul]
  ring

/-- Even the pending gate from the last earlier HEAD writes a deadline
no later than the end of one stage. This includes its extra Δ. -/
theorem old_head_deadline_by_next_stage (p : Params) (r boundary : Slot)
    (hr : r < boundary) :
    gateTime p r + lifetime p ≤ voteTime p boundary + (lifetime p + p.Δ) := by
  have hc : (r : Time) + 1 ≤ boundary := by exact_mod_cast hr
  have hd := p.deltaPos
  dsimp [gateTime, voteTime, proposalTime]
  nlinarith

end AvailableChain.GridCO
end
