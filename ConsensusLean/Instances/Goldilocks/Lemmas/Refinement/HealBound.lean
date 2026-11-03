module
public import ConsensusLean.Spec.Blocks.Progress

public section

/-! # Goldilocks Refinement: the sufficient heal bound of the final route (#136)

consensus-lean#136, workbench `heal_bound.md`. Pure integer arithmetic. The chain is
ready → frame window (pigeonhole, `exists_const_window`: `a_f + len ≤ lo + 6(len + λ)`) →
drain (`L_drain` slots, a parameter) → warm proposal `u` → rise (`rise_reset`:
`a ≤ ts(u + 2ρ + 1) + 2Δ`, `ρ = δt + X − 1`) → seed (`u_min ≤ slot a + 2k + 5`) → placement
(`(P)`, the (H3) inequality of `final_reset_premises`).

Time unit: `D` (the SA `Δ`), `ts s = 4D·s`. All quantities are in `ℤ`; a consumer casts its
slots. No coefficient is defined here: `heal` is any time with `ready + T_heal ≤ heal`.

Note: the seed premise is the paper form `u_min ≤ slot a + 2k + 5`. The landed
`finalSeedMin` adds `(ḡ + 4Δ).toNat` slots, which no coefficient bound covers uniformly in the
GST (workbench `heal_bound.md` §5). -/

namespace Consensus.Goldilocks.Refinement

/-- The heal coefficient part of `T_heal`, in units of `D` (without the `6λ − 2` term). -/
def healBoundCoeff (k δt X Ld : ℤ) : ℤ := 24 * Ld + 8 * k + 52 * δt + 52 * X + 32

/-- **Sufficient heal bound (arithmetic).** If `ready + healBoundCoeff·D + 6λ − 2 ≤ heal ≤ q`,
then: the slot-aligned frame `[ts s₀, ts N + 2D]` fits the pigeonhole window; the reset has
`a ≤ ready + (24 L_drain + 48ρ + 64)·D + 6λ − 1`; the rise deadline `ts N + 2D ≤ heal` holds;
and the placement (H3) holds for every `u_min ≤ slot a + 2k + 5`. -/
theorem heal_bound_sufficient {D ready heal q lo af len lam a : ℤ}
    {k δt X Ld s₀ u sa uMin : ℤ}
    (hD : 0 < D) (hready : 0 ≤ ready) (hlam : 0 ≤ lam)
    (hk : 0 ≤ k) (hδ : 1 ≤ δt) (hX : 1 ≤ X) (hLd : 0 ≤ Ld)
    (hlo : lo ≤ ready + 4 * D)
    (hlen : len = 4 * D * (Ld + 2 * (δt + X - 1) + 2) + 2 * D)
    (hwin : af + len ≤ lo + 6 * (len + lam))
    (hs₀ : 4 * D * s₀ < af + 4 * D)
    (hu : u ≤ s₀ + Ld)
    (hrise : a ≤ 4 * D * (u + 2 * (δt + X - 1) + 1) + 2 * D)
    (hsa : 4 * D * sa ≤ a) (huMin : uMin ≤ sa + 2 * k + 5)
    (hheal : ready + healBoundCoeff k δt X Ld * D + 6 * lam - 2 ≤ heal) (hq : heal ≤ q) :
    4 * D * (s₀ + Ld + 2 * (δt + X - 1) + 1) + 2 * D < af + len ∧
      a ≤ ready + (24 * Ld + 48 * (δt + X - 1) + 64) * D + 6 * lam - 1 ∧
      4 * D * (s₀ + Ld + 2 * (δt + X - 1) + 1) + 2 * D ≤ heal ∧
      max (max ready 0) (4 * D * uMin - 1) + (X + δt) * (4 * D) ≤ q + 4 * D := by
  unfold healBoundCoeff at hheal
  have hu' : 4 * D * u ≤ 4 * D * (s₀ + Ld) := mul_le_mul_of_nonneg_left hu (by linarith)
  have hm' : 4 * D * uMin ≤ 4 * D * (sa + 2 * k + 5) :=
    mul_le_mul_of_nonneg_left huMin (by linarith)
  have hfit : 4 * D * (s₀ + Ld + 2 * (δt + X - 1) + 1) + 2 * D < af + len := by
    rw [hlen]; linarith
  have hfrm : 4 * D * (s₀ + Ld + 2 * (δt + X - 1) + 1) + 2 * D ≤
      ready + (24 * Ld + 48 * (δt + X - 1) + 64) * D + 6 * lam - 1 := by
    rw [hlen] at hwin hfit; linarith
  have hDk : 0 ≤ D * k := mul_nonneg hD.le hk
  have hDδ : D ≤ D * δt := by nlinarith
  have hDX : D ≤ D * X := by nlinarith
  have hDL : 0 ≤ D * Ld := mul_nonneg hD.le hLd
  refine ⟨hfit, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · have hr : max ready 0 = ready := max_eq_left hready
    rw [hr]
    apply add_le_of_le_sub_right
    apply max_le
    · linarith
    · linarith

/-- The heal coefficient for the 5-window pigeonhole (`exists_const_window5`), in units of `D`
(without the `5λ − 2` term). At `λ = 2D`: `T_heal = (20L + 8k + 44δt + 44X + 40)·D − 2`. -/
def healBoundCoeff5 (k δt X Ld : ℤ) : ℤ := 20 * Ld + 8 * k + 44 * δt + 44 * X + 30

/-- **Sufficient heal bound, 5 windows (arithmetic).** `heal_bound_sufficient` with
`a_f + len ≤ lo + 5(len + λ)` and `healBoundCoeff5`. -/
theorem heal_bound_sufficient5 {D ready heal q lo af len lam a : ℤ}
    {k δt X Ld s₀ u sa uMin : ℤ}
    (hD : 0 < D) (hready : 0 ≤ ready) (hlam : 0 ≤ lam)
    (hk : 0 ≤ k) (hδ : 1 ≤ δt) (hX : 1 ≤ X) (hLd : 0 ≤ Ld)
    (hlo : lo ≤ ready + 4 * D)
    (hlen : len = 4 * D * (Ld + 2 * (δt + X - 1) + 2) + 2 * D)
    (hwin : af + len ≤ lo + 5 * (len + lam))
    (hs₀ : 4 * D * s₀ < af + 4 * D)
    (hu : u ≤ s₀ + Ld)
    (hrise : a ≤ 4 * D * (u + 2 * (δt + X - 1) + 1) + 2 * D)
    (hsa : 4 * D * sa ≤ a) (huMin : uMin ≤ sa + 2 * k + 5)
    (hheal : ready + healBoundCoeff5 k δt X Ld * D + 5 * lam - 2 ≤ heal) (hq : heal ≤ q) :
    4 * D * (s₀ + Ld + 2 * (δt + X - 1) + 1) + 2 * D < af + len ∧
      a ≤ ready + (20 * Ld + 40 * (δt + X - 1) + 54) * D + 5 * lam - 1 ∧
      4 * D * (s₀ + Ld + 2 * (δt + X - 1) + 1) + 2 * D ≤ heal ∧
      max (max ready 0) (4 * D * uMin - 1) + (X + δt) * (4 * D) ≤ q + 4 * D := by
  unfold healBoundCoeff5 at hheal
  have hu' : 4 * D * u ≤ 4 * D * (s₀ + Ld) := mul_le_mul_of_nonneg_left hu (by linarith)
  have hm' : 4 * D * uMin ≤ 4 * D * (sa + 2 * k + 5) :=
    mul_le_mul_of_nonneg_left huMin (by linarith)
  have hfit : 4 * D * (s₀ + Ld + 2 * (δt + X - 1) + 1) + 2 * D < af + len := by
    rw [hlen]; linarith
  have hfrm : 4 * D * (s₀ + Ld + 2 * (δt + X - 1) + 1) + 2 * D ≤
      ready + (20 * Ld + 40 * (δt + X - 1) + 54) * D + 5 * lam - 1 := by
    rw [hlen] at hwin hfit; linarith
  have hDk : 0 ≤ D * k := mul_nonneg hD.le hk
  have hDδ : D ≤ D * δt := by nlinarith
  have hDX : D ≤ D * X := by nlinarith
  have hDL : 0 ≤ D * Ld := mul_nonneg hD.le hLd
  refine ⟨hfit, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · have hr : max ready 0 = ready := max_eq_left hready
    rw [hr]
    apply add_le_of_le_sub_right
    apply max_le
    · linarith
    · linarith

/-- At `λ = 2D` the 5-window bound is `T_heal = (20L + 8k + 44δt + 44X + 40)·D − 2`. -/
theorem healBoundCoeff5_at_two (k δt X Ld D : ℤ) :
    healBoundCoeff5 k δt X Ld * D + 5 * (2 * D) - 2 =
      (20 * Ld + 8 * k + 44 * δt + 44 * X + 40) * D - 2 := by
  unfold healBoundCoeff5
  ring

end Consensus.Goldilocks.Refinement
