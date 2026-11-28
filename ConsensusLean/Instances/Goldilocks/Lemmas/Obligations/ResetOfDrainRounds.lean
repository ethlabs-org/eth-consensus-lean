module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.CallLag
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameLag
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Rise

public section

/-! # Goldilocks Obligations: the reset bound of the key-dependent rise route

`resetBoundRounds r Δ λ δ_t G L_drain = r + (20 L_drain + 24ρ + 54)·Δ + 5λ`, the reset bound of
the five-window drain reset with the key-dependent window of `Healing.M1.RiseWindow`
(`ρ = δ_t + G − 1`), with its closed form `resetBoundRounds_eq`. -/

namespace Consensus.Goldilocks.Obligations

open AC (gbar)
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

end Consensus.Goldilocks.Obligations

end
