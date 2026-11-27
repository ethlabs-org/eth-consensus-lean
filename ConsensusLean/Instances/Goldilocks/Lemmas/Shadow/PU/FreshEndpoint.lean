module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.SignedTick
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Driven
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshUpdate
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Fresh update calls over the shadow run -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}

/-- Wakefulness supplies the actual update tick, independently of its signing bit. -/
theorem update_call_of_awake_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g b : Time}
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hnr : NoRestartAfter tr H (gbar g)) {u : Nat}
    (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H (sp.ts (u + 1 : Nat) + 2 * sp.Δ)) :
    ∃ k ell, AC.UpdateAt tr.projAC y k u ell := by
  let T := sp.ts (u + 1 : Nat) + 2 * sp.Δ
  have hT : T = sp.ts u + 6 * sp.Δ := by
    dsimp only [T, ACParams.ts]; push_cast; ring
  have hΔ := sp.toParams.hΔ
  have ht0 : 0 ≤ T := by
    have hu0 : 0 ≤ sp.ts u := by simp only [ACParams.ts]; positivity
    rw [hT]; linarith
  obtain ⟨k, hk⟩ := hrun.tick_of_awake y T hy ht0
    ⟨4 * (u : Int) + 6, by rw [hT]; simp only [ACParams.ts]; ring⟩
    (hawake y T hy (by rw [hT]; linarith) hTb)
  obtain ⟨x, fgDue, hg⟩ := (RunTrace.tickAt_iff ..).1 hk
  obtain ⟨hc, ht⟩ := Healing.tick_first_cut hg
  have hj := Core.joined_of_restart_le_at hrun.toCore hnc hy
    (by rw [hT]; linarith : sp.ts u + 4 * sp.Δ ≤ T)
    (fun r _ hyr hrs => (hnr y r hyr hrs).trans (by linarith)) ht
  simp only [Node.acCall_eq] at hc
  exact ⟨k, _, Compose.projAC_callAt.2 hc, rfl, ht.trans hT, hj⟩

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
