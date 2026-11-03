module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Warm
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealComposeDefs

public section

/-! # Goldilocks Refinement: the drain outputs from finite service (#136, P5)

`drainOutputs_of_service` supplies `DrainOutputs … G Ld b`, the input of `exists_reset_of_drain`,
from the run premises up to the service horizon `b` alone: reset service, wakefulness on
`[ḡ, b]`, `f < n/3`, Catch with `κ = 2Δ`, and no restart after `ḡ`. The warm proposal is
`FrameWindow.exists_warm_proposal` at `a = s₀ + 2k`, which builds the snapshot and its call at
the actual cast from wakefulness. The frame's NoAdvance premise is not used.

The one quantitative premise is `hLd : 2k + G ≤ L_drain + 1`. It places the gap window
`[s₀ + 2k, s₀ + 2k + G)` inside `[s₀, N]` and its slot below `s₀ + L_drain`. It constrains
the caller's choice of `L_drain` and is not a property of the run. -/

namespace Consensus.Goldilocks.Refinement

open SA (gbar)
open Healing

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- **The drain outputs from finite service.** Reset service and wakefulness up to `b`,
`3f ≤ n − 1`, Catch with `κ = 2Δ` and no restart after `ḡ` give `DrainOutputs` at horizon `b`
for every `L_drain` with `2k + G ≤ L_drain + 1`. -/
theorem drainOutputs_of_service (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) {G Ld : Nat} (hLd : 2 * sp.k + G ≤ Ld + 1) :
    DrainOutputs tr proposer H g G Ld b where
  warm hframe hm hN hb _ hgp := by
    obtain ⟨u, hlu, hhu, z, hz, hdes, kP, P, hP, hPs, hlow⟩ :=
      hframe.exists_warm_proposal hrun hnc hsvc hawake hf hcatch hnr hm (G := G) (by omega) hb
        (hgp _ (by omega) (by omega))
    exact ⟨u, hlu, by omega, z, hz, hdes, kP, P, hP, hPs, hlow⟩

end Consensus.Goldilocks.Refinement
