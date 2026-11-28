module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.FrameWindowExists
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ResetDrain
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The growing drain kernel's steps

The warm proposals, forwarded to their proof (the `KernelProof` form in `Shadow/PU/ResetDrain`),
on `Generic.FrameWindow` windows; with the P-U window search they give the finite reset record with
the reset bound `exists_reset_of_drain_rounds_awake_at` of `Shadow/PU/ResetDrain`. The finite reset
lower bound is proved in `Kernel/ResetSource`. No deadline is lengthened here.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
variable {hold : Time}

/-- Step 3: service gives warm proposals without any reset lower-bound premise. -/
theorem drainOutputs_of_service_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {G Ld : Nat} (hLd : 2 * sp.k + G ≤ Ld + 1) :
    Shadow.DrainOutputs tr proposer H g G Ld b := by
  exact KernelProof.drainOutputs_of_service_at hrun hnc hsvc hawake hf hcatch hLd

/-- Step 4 packaging: a bounded reset and a snapshot supply the finite reset record at a
committee `cm` whose faults obey the fraction `βK ≤ ½`; the per-slot timeout delay is the scalar
delay on the four-`Δ` slot grid. -/
theorem resetPremisesUpTo_of_reset_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot (Generic.dictOfTime sp cm)))
    (hnc : Compose.NoCollRun dg tr) {g ΔF a b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hreset : IsReset tr H g a) (hab : a ≤ b)
    (hsnapshot : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g) ∧ tr.time k ≤ b)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartUpTo tr H (gbar g) b)
    (hΔF : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time)) (hH : (H b).Nonempty)
    (hfacts : Compose.Growing.CommitteeFacts tr H (Generic.dictOfTime sp cm))
    (hβ : βK ≤ 1 / 2) (hpos : 0 < sp.committeeSize)
    (hcf : Generic.CommitteeFaultsUpTo βK cm H g b)
    (hdeep : ∀ D, sp.deepDepth = some D →
      b ≤ cutZ sp.toParams g + 4 * D * sp.Δ ∨ HighSourceCover tr H g a b) :
    ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold := by
  refine ⟨hβ, hrun, hpos, hfacts, hcf, hnc, hsvc, hawake, hf, hreset, hab,
    hsnapshot, hcatch, noRestartUpTo_iff.mp hnr, fun s => ?_, hH, hdeep⟩
  have hδ : (sp.toParams.δt : Time) = sp.toParams.fg.δt := rfl
  rw [sp.slotTime_eq, sp.slotTime_eq]
  push_cast
  rw [hδ, mul_add]
  linarith

end Consensus.Goldilocks.Healing.Growing

end
