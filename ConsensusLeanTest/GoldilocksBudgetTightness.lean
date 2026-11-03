module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OutageArmingSteps
@[expose] public section

/-! # Rejection test: the outage budget `4k − 4` breaks the restored-label bound

The outage budget (`acceptanceContract`, `Statements/Refinement/Accepted.lean`: `4k − 5` since
`b75cd7c5`) bounds the outage length: `b₁ − b₀ ≤ budget · Δ`. The lock-safety arithmetic
(`OutageLockSafety/Arming.lean`, the private `query_numbers`, conjunct 5) needs the end of the
outage before the restored-label bound of the cover label `j₀ = coverLabel b₀`:
`b₁ ≤ t_{j₀+k} + Δ`, so that the first restored label (the least `r` with `b₁ ≤ t_r + Δ`) is at
most `j₀ + k`. The cover gates give `b₀ < t_{j₀} + 6Δ` (`coverLabel_gates`), hence with budget
`4k − 5`, `b₁ ≤ t_{j₀} + 6Δ − 1 + (4k − 5)Δ = t_{j₀+k} + Δ − 1`: one tick of slack.

With budget `4k − 4` the bound fails. At `k = 2`, `Δ = 2` (slot length `4Δ = 8`; node and engine
`Δ` agree at half-open delivery): the start `b₀ = 11` has cover label `j₀ = 0` (its gates
`t₀ + 2Δ = 4 ≤ 11 < 12 = t₀ + 6Δ`, so `11` is the latest start of that label), and the longest
outage the budget allows ends at `b₁ = 11 + (4·2 − 4)·2 = 19`. But `t_{j₀+k} + Δ = t₂ + 2 = 18`,
so conjunct 5 fails (`19 > 18`), and the first restored label is `3 = j₀ + k + 1`, outside
`(j₀, j₀ + k]`. With `4k − 5` the same start allows at most `b₁ = 17 ≤ 18`, and in general every
start and every outage within that budget satisfies the bound (`budget_four_k_minus_five_bound`).

The arithmetic is stated directly on `SAParams` and `Compose.coverLabel`, as `query_numbers` is
private. Labelled by kind (CONTRIBUTING "Statements"): (r) `budget_four_k_minus_four_breaks`,
(control) `budget_four_k_minus_five_bound`. -/

namespace Consensus.Goldilocks.BudgetTightness

open SA (SAParams)

/-- One validator, `Δ = 2`, slot `s` starts at `8s = 4Δs`, genesis root `0`. -/
abbrev P₂ : Params where
  n := 1
  hn := le_rfl
  Δ := 2
  hΔ := by norm_num
  slotTime := fun s => 8 * (s : Int)
  slotTime_zero := by simp
  slotTime_strictMono := fun a b h => by change 8 * (a : Int) < 8 * (b : Int); omega
  slotTime_public := fun s => ⟨4 * (s : Int), by ring⟩
  genesisRoot := 0
  δt := 0

/-- The SA parameters `P₂` with the slow window `k = 2`. -/
abbrev sp₂ : SAParams where
  toParams := P₂
  slotTime_eq := fun s => by change 8 * (s : Int) = 4 * 2 * s; ring
  k := 2
  two_le_k := le_rfl

/-- `t_s = 8s` at `sp₂`. -/
theorem ts_eq (s : Int) : sp₂.ts s = 8 * s := by
  simp only [SAParams.ts]; ring

/-- The latest outage start of cover label `0`: `coverLabel 11 = 0`, with its gates
`t₀ + 2Δ ≤ 11 < t₀ + 6Δ` (the next integer start `12` has cover label `1`). -/
theorem cover_eleven :
    Compose.coverLabel sp₂ 11 = 0 ∧ sp₂.ts (0 : Nat) + 2 * sp₂.Δ ≤ 11 ∧
      (11 : Time) < sp₂.ts (0 : Nat) + 6 * sp₂.Δ ∧ Compose.coverLabel sp₂ 12 = 1 := by
  have h11 : Compose.coverLabel sp₂ 11 = 0 := by
    rw [Compose.coverLabel_eq]
    exact SA.slot_of_mem sp₂ 0 (by rw [ts_eq]; norm_num) (by rw [ts_eq]; norm_num)
  have h12 : Compose.coverLabel sp₂ 12 = 1 := by
    rw [Compose.coverLabel_eq]
    exact SA.slot_of_mem sp₂ 1 (by rw [ts_eq]; norm_num) (by rw [ts_eq]; norm_num)
  refine ⟨h11, ?_, ?_, h12⟩ <;> rw [ts_eq] <;> norm_num

/-- (r) **Budget `4k − 4` breaks the restored-label bound** at `k = 2`, `Δ = 2`: the outage
from `b₀ = 11` (cover label `j₀ = 0`) of the full budget ends at `b₁ = 19 > 18 = t_{j₀+k} + Δ`,
and the first restored label of `b₁` (the least `r` with `b₁ ≤ t_r + Δ`) is `3 = j₀ + k + 1`.
With budget `4k − 5` the same start allows at most `17 ≤ 18`. -/
theorem budget_four_k_minus_four_breaks :
    let j₀ := Compose.coverLabel sp₂ 11
    let b₁ : Time := 11 + ((4 * sp₂.k - 4 : Nat) : Int) * sp₂.Δ
    j₀ = 0 ∧ (4 * sp₂.k - 4 : Nat) = 4 ∧ b₁ = 19 ∧
      sp₂.ts (j₀ + sp₂.k : Nat) + sp₂.Δ = 18 ∧
      ¬ b₁ ≤ sp₂.ts (j₀ + sp₂.k : Nat) + sp₂.Δ ∧
      (∀ r : Nat, b₁ ≤ sp₂.ts (r : Nat) + sp₂.Δ ↔ 3 ≤ r) ∧
      (4 * sp₂.k - 5 : Nat) = 3 ∧
      (11 : Time) + ((4 * sp₂.k - 5 : Nat) : Int) * sp₂.Δ = 17 ∧
      (11 : Time) + ((4 * sp₂.k - 5 : Nat) : Int) * sp₂.Δ ≤
        sp₂.ts (j₀ + sp₂.k : Nat) + sp₂.Δ := by
  intro j₀ b₁
  have hj : j₀ = 0 := cover_eleven.1
  have hb : b₁ = 19 := by simp only [b₁]; norm_num
  have hk : sp₂.ts (j₀ + sp₂.k : Nat) + sp₂.Δ = 18 := by
    rw [hj, ts_eq]; norm_num
  refine ⟨hj, by norm_num, hb, hk, by rw [hb, hk]; norm_num, fun r => ?_, by norm_num,
    by norm_num, by rw [hk]; norm_num⟩
  rw [hb, ts_eq]
  change (19 : Int) ≤ 8 * (r : Int) + 2 ↔ 3 ≤ r
  omega

/-- (control) **Budget `4k − 5` keeps the restored-label bound** at `k = 2`, `Δ = 2`: for every
start `b₀ ≥ 2Δ` with cover label `j₀` and every end `b₁` within the budget,
`b₁ ≤ t_{j₀+k} + Δ − 1` (the one tick of slack of `query_numbers`' conjunct 5). -/
theorem budget_four_k_minus_five_bound (b₀ b₁ : Time) (hb₀ : 2 * sp₂.Δ ≤ b₀)
    (hb : b₁ - b₀ ≤ ((4 * sp₂.k - 5 : Nat) : Int) * sp₂.Δ) :
    b₁ ≤ sp₂.ts (Compose.coverLabel sp₂ b₀ + sp₂.k : Nat) + sp₂.Δ - 1 := by
  have hg := (Compose.coverLabel_gates (sp := sp₂) hb₀).2
  have hts : sp₂.ts (Compose.coverLabel sp₂ b₀ + sp₂.k : Nat) =
      sp₂.ts (Compose.coverLabel sp₂ b₀ : Nat) + 16 := by
    rw [ts_eq, ts_eq]; push_cast; ring
  rw [hts]
  change b₁ - b₀ ≤ ((4 * 2 - 5 : Nat) : Int) * 2 at hb
  change b₀ < sp₂.ts (Compose.coverLabel sp₂ b₀ : Nat) + 6 * 2 at hg
  norm_num at hb
  change b₁ ≤ sp₂.ts (Compose.coverLabel sp₂ b₀ : Nat) + 16 + 2 - 1
  have hint : b₀ + 1 ≤ sp₂.ts (Compose.coverLabel sp₂ b₀ : Nat) + 6 * 2 :=
    Int.add_one_le_iff.mpr hg
  linarith

end Consensus.Goldilocks.BudgetTightness

end
