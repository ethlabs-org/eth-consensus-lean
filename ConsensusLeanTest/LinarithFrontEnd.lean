module
public import ConsensusLean.Lemmas.Tactic.Linarith
public import Mathlib.Tactic.Linarith
public section

/-! # Regressions for the `linarith` front end (`ConsensusLean/Lemmas/Tactic/Linarith.lean`)

With the front end imported, plain `linarith`/`nlinarith` first run without Mathlib's `natToInt`
preprocessor and fall back to Mathlib's rule on failure; every other form is Mathlib's. These
theorems pin the cases its review asked for: a goal that needs the ℕ facts (the fallback), a
nonlinear goal, extra terms, and that `!`, `only` and a configuration still reach Mathlib's rule
with their own meaning (a configuration that makes Mathlib's tactic fail must still fail). -/

namespace Consensus.Test.LinarithFrontEnd

open Lean Elab Tactic

/-- Needs `natToInt` (the bound on an ℕ variable): proved through the fallback to Mathlib's rule. -/
theorem nat_fallback (n : ℕ) (h : n < 3) : n ≤ 2 := by linarith

/-- Mixed ℕ and ℤ facts: the ℕ cast's nonnegativity comes from `natToInt`. -/
theorem nat_cast_fallback (n : ℕ) (x : ℤ) (h : x + (n : ℤ) < 0) : x < 0 := by linarith

/-- Pure ℤ arithmetic, the cheap path, with an extra term. -/
theorem int_with_term (a b c : ℤ) (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a ≤ b + c := by linarith [h₂]

/-- `nlinarith`'s products (here `Δ * (u - s - 2) ≥ 0`), the slot-time shape of the Goldilocks
proofs. -/
theorem nonlinear_slot (d s u : ℤ) (hd : 0 < d) (h : s + 2 ≤ u) :
    4 * d * s + 8 * d ≤ 4 * d * u := by
  nlinarith

/-- Nonlinear over ℕ: products and the ℕ facts, through the fallback. -/
theorem nonlinear_nat (n m : ℕ) (h : n * n < m) : n * n ≤ m := by nlinarith

/-- `only` sees only the listed facts, so with an empty list it cannot use `h`; a call that
ignored `only` would prove the goal from the context. -/
theorem only_passthrough (a b : ℤ) (h : a < b) : a ≤ b := by
  fail_if_success linarith only []
  fail_if_success nlinarith only []
  linarith only [h]

/-- The bang forms identify `id x` and `x`, unlike the default transparency. -/
theorem bang_passthrough (x : ℚ) : id x ≥ x ∧ id x ≥ x := by
  constructor
  · fail_if_success linarith
    linarith!
  · fail_if_success nlinarith
    nlinarith!

/-- A configuration reaches Mathlib's rule with its meaning: with no preprocessors, Mathlib's
tactics cannot put the hypotheses in their normal form and fail on this ℤ goal, which the cheap
path (the default preprocessors minus `natToInt`) proves. Were a configured call handled with
the default configuration, the `fail_if_success` would fail. -/
theorem config_passthrough (a b : ℤ) (h : a < b) : a ≤ b := by
  fail_if_success linarith (preprocessors := [])
  fail_if_success nlinarith (preprocessors := [])
  linarith

/-- A false goal still fails (both runs fail; the error is Mathlib's). -/
theorem false_goal_fails (x y : ℤ) (_h : x < y) : True := by
  fail_if_success (have : y < x := by linarith)
  fail_if_success (have : y < x := by nlinarith)
  trivial

/-- The cheap attempt alone (`Consensus.Tactic.Linarith.run`) really omits `natToInt`: without it
the ℕ bound of `nat_fallback` is out of reach, so this pins the filter in `cheapConfig` (were it a
no-op, the cheap attempt would prove the goal and the `fail_if_success` would fail). -/
theorem cheap_omits_natToInt (n : ℕ) (h : n < 3) : n ≤ 2 := by
  fail_if_success run_tac liftMetaFinishingTactic (Consensus.Tactic.Linarith.run false [])
  fail_if_success run_tac liftMetaFinishingTactic (Consensus.Tactic.Linarith.run true [])
  linarith

/-- Control for `cheap_omits_natToInt`: the cheap attempt alone proves an ℤ goal. -/
theorem cheap_proves_int (a b : ℤ) (h : a < b) : a ≤ b := by
  run_tac liftMetaFinishingTactic (Consensus.Tactic.Linarith.run false [])

end Consensus.Test.LinarithFrontEnd
