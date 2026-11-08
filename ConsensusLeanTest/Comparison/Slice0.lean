module
public import ConsensusLean.Comparison.Defaults

@[expose] public section

/-! # Slice 0 rejection tests

Cheap checks that the Slice 0 statements reject what they must: infeasible points (`L = 0` with a
split class, a fault cap above `n − 2`), coverage by a system with no valid run or an excuse on
every run, coverage of a finite liveness bound by runs that never exercise liveness (a safety-only
witness), and coverage of a finite claim about an absent output. A feasible split point exists. -/

namespace Consensus.Comparison.Test

open Consensus.Comparison

variable {V : Type} [Fintype V] {Prog : Type} {S : System V} {X : Progress S Prog}
  {K : Contract Prog}

/-- `L = 0` with a split class is infeasible. -/
theorem split_zero_infeasible (f : ℕ) (G : V → Bool) :
    ¬ (⟨0, f, .split G⟩ : Slice0Q V).Feasible := by
  rintro ⟨-, h, -⟩
  simp at h

/-- A fault cap above `n − 2` is infeasible. -/
theorem fcap_gt_infeasible (q : Slice0Q V) (h : Fintype.card V < q.fcap + 2) : ¬ q.Feasible :=
  fun hq => absurd hq.1 (by omega)

/-- A feasible split point: two validators in two groups, one incident delay, no faults. -/
theorem split_feasible_example : (⟨1, 0, .split (fun v : Fin 2 => decide (v = 0))⟩ :
    Slice0Q (Fin 2)).Feasible :=
  ⟨by simp, le_rfl, ⟨0, by decide⟩, ⟨1, by decide⟩⟩

/-- No valid run: no finite safety bound at a feasible point is covered. -/
theorem no_valid_not_covered (hS : ∀ r, ¬ S.Valid r) {cap : Capability} {i : K.Idx}
    {hs hl lat : Bound (Slice0Q V)} (q : Slice0Q V) (hq : q.Feasible) (hfin : hs q < ⊤) :
    ¬ HealCoverage0 S X K cap i hs hl lat := by
  intro h
  obtain ⟨-, r, b₀, b₁, hv, -⟩ := h.covers q hq (Or.inl hfin)
  exact hS r hv

/-- An excuse on every run: no finite safety bound at a feasible point is covered. -/
theorem excuse_not_covered (hS : ∀ r, S.Excuse r) {cap : Capability} {i : K.Idx}
    {hs hl lat : Bound (Slice0Q V)} (q : Slice0Q V) (hq : q.Feasible) (hfin : hs q < ⊤) :
    ¬ HealCoverage0 S X K cap i hs hl lat := by
  intro h
  obtain ⟨-, r, b₀, b₁, -, hne, -⟩ := h.covers q hq (Or.inl hfin)
  exact hne (hS r)

/-- **A safety-only witness does not cover a finite liveness bound**: on a system whose valid runs
have no transaction submissions (so liveness is never active, while safety may be), finite `hl`
and `lat` at a feasible point are not covered, whatever `hs` is. -/
theorem safety_only_not_covered (hS : ∀ r, S.Valid r → ∀ v t, (S.pt r).submit v t = [])
    {cap : Capability} {i : K.Idx} {hs hl lat : Bound (Slice0Q V)} (q : Slice0Q V)
    (hq : q.Feasible) (c d : ℕ) (hc : hl q = c) (hd : lat q = d) :
    ¬ HealCoverage0 S X K cap i hs hl lat := by
  intro h
  obtain ⟨-, r, b₀, b₁, hv, -, -, -, -, -, -, -, hlive⟩ :=
    h.covers q hq (Or.inr ⟨by simp [hc], by simp [hd]⟩)
  obtain ⟨x, t, t', u, w, -, -, -, hx, -⟩ := hlive c d hc hd
  simp [hS r hv] at hx

/-- **An absent output is never covered**: when `cap`'s output is not provided, no finite claim at
a feasible point is covered (its claims would be vacuous). -/
theorem absent_output_not_covered {cap : Capability} {i : K.Idx}
    (hcap : S.schema.output cap = none) {hs hl lat : Bound (Slice0Q V)} (q : Slice0Q V)
    (hq : q.Feasible) (hfin : hs q < ⊤ ∨ (hl q < ⊤ ∧ lat q < ⊤)) :
    ¬ HealCoverage0 S X K cap i hs hl lat := by
  intro h
  have := (h.covers q hq hfin).1
  simp [hcap] at this

/-- An absent output: no finite transaction latency at a feasible cap is covered. -/
theorem absent_output_not_covered_tx {cap : Capability} {i : K.Idx}
    (hcap : S.schema.output cap = none) {lat : Bound ℕ} (f d : ℕ)
    (hf : f + 2 ≤ Fintype.card V) (hd : lat f = d) :
    ¬ TxLatencyCoverage0 S X K cap i lat := by
  intro h
  have := (h.covers f d hf hd).1
  simp [hcap] at this

end Consensus.Comparison.Test

end
