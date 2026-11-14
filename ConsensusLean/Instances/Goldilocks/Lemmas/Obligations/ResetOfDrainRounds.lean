module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.CallLag
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameLag
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.RiseWindow
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Rise
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Obligations: the reset bound of the key-dependent rise route

`resetBoundRounds r Δ λ δ_t G L_drain = r + (20 L_drain + 24ρ + 54)·Δ + 5λ`, the reset bound of
the five-window drain reset with the key-dependent window of `Healing.M1.RiseWindow`
(`ρ = δ_t + G − 1`), with its closed form `resetBoundRounds_eq`, and the slot alignment
`exists_slot_align`. -/

namespace Consensus.Goldilocks.Obligations

open SA (gbar)
open Healing

/-- The reset bound of the key-dependent rise route: `lo + 5(4D(L_drain + 2) + 2D + λ) + 6·4Dρ`
at `lo = r + 4D`, `ρ = δ_t + X − 1`. -/
def resetBoundRounds (r D lam δt X Ld : ℤ) : ℤ :=
  r + (20 * Ld + 24 * (δt + X - 1) + 54) * D + 5 * lam

/-- Unfolding equation of `resetBoundRounds`. -/
theorem resetBoundRounds_eq (r D lam δt X Ld : ℤ) :
    resetBoundRounds r D lam δt X Ld = r + (20 * Ld + 24 * (δt + X - 1) + 54) * D + 5 * lam := by
  unfold resetBoundRounds
  rfl

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Slot alignment: `s₀ = ⌈a_f / 4D⌉` has `a_f ≤ t_{s₀} < a_f + 4D`. -/
theorem exists_slot_align (sp : SA.SAParams) {af : Time} (haf : 0 ≤ af) :
    ∃ s₀ : Nat, af ≤ sp.ts s₀ ∧ 4 * sp.Δ * (s₀ : ℤ) < af + 4 * sp.Δ := by
  have h4D : 0 < 4 * sp.Δ := by linarith only [sp.toParams.hΔ]
  set s₀Z : ℤ := (af + 4 * sp.Δ - 1) / (4 * sp.Δ) with hs₀Z
  have hs₀lo := Int.ediv_mul_le (af + 4 * sp.Δ - 1) h4D.ne'
  have hs₀hi := Int.lt_ediv_add_one_mul_self (af + 4 * sp.Δ - 1) h4D
  rw [← hs₀Z] at hs₀lo hs₀hi
  have hs₀nn : 0 ≤ s₀Z := Int.ediv_nonneg (by linarith only [haf, h4D]) h4D.le
  have hs₀c : ((s₀Z.toNat : Nat) : ℤ) = s₀Z := Int.toNat_of_nonneg hs₀nn
  refine ⟨s₀Z.toNat, ?_, ?_⟩
  · change af ≤ 4 * sp.Δ * ((s₀Z.toNat : Nat) : ℤ)
    rw [hs₀c]; linarith only [hs₀hi]
  · rw [hs₀c]; linarith only [hs₀lo]

end Consensus.Goldilocks.Obligations

end
