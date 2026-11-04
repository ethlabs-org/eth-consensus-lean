module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Interface
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Acquisition
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.OldEntryCrossing
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.StretchCoverage
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Timing
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.TwoWindow

public section

/-! # Goldilocks Recovery: bounded high coverage under the uniform pattern

Choose the post-drain pattern stretch, acquire a high proposal P, cross its old entry to U,
then serve U and its actual successor. The resulting carrier finalizes U and hence P before
the stretch ends. C5 propagates that actual acceptance to honest caches at the exact public
deadline. The report and outcome suppliers are proof inputs; this module does not import
their Obligations-dependent implementation. -/

namespace Consensus.Goldilocks.Healing.Recovery

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF Gp : Time} {W M cF kF : Nat}

/-- C0–C5 supply bounded high coverage under precisely the public pattern premises. -/
theorem pattern_coverage_supply (houtcome : Compose.OutcomeService)
    (hreports : ∀ a, ReadyProposalReportSupply tr H proposer dg g ΔF a) :
    PatternCoverageSupply tr H proposer dg g ΔF Gp W M cF kF := by
  refine ⟨fun hrun hpat t ht => ?_⟩
  obtain ⟨a, hp, hab, -⟩ := pattern_reset hrun hpat
  obtain ⟨v, htv, hvt, hv, hwindow⟩ :=
    pattern_stretch_after_reset hrun hpat hp.reset hab ht
  obtain ⟨s, p, kP, iP, P, hvs, hs, hP, hacc, hhigh⟩ := fresh_high_proposal hp hpat
    (fun u hu hu' => by
      obtain ⟨k, B, hB, -⟩ := hwindow u hu hu'
      exact ⟨k, B, hB⟩) hv
  have hafter : drainTime sp a ≤ sp.ts s :=
    hv.trans ((SA.ts_le_iff sp).2 (by exact_mod_cast hvs))
  have hroom := (recovery_slot_budget hpat.long hs
    (show s + oldSlots sp ΔF Gp ≤ s + oldSlots sp ΔF Gp from le_rfl)).1
  obtain ⟨q, kU, iU, U, hU, hentry, hPU, hsU, hUbound, hheight⟩ :=
    old_entry_crossing hp hpat (hreports a) hwindow hvs hroom hP hacc hhigh hafter
  have hUhigh : HZ tr H g + 2 ≤ ((tr.post iU).fg.σ U.root).h := by omega
  have hUR : drainTime sp a ≤ sp.ts U.slot :=
    hafter.trans ((SA.ts_le_iff sp).2 (by exact_mod_cast hsU.le))
  obtain ⟨x, hx, kX, X, hX, hgX, hXD, Fx, hFx, hroot, hUF⟩ :=
    two_window_finalization houtcome hp hpat hwindow hU hentry hUhigh (hvs.trans hsU.le)
      hUR (recovery_slot_budget hpat.long hs hUbound).2
  have hPs : P.slot = s := hP.2.2.2.2.1
  exact high_coverage_of_stretch_carrier hp ⟨htv, hvt⟩
    (by simpa only [hPs] using hP) hacc hhigh (by simpa only [hPs] using hvs)
    (by rw [hPs]; omega) hx hX hFx hroot (hPU.trans hUF) hgX hXD

end Consensus.Goldilocks.Healing.Recovery

end
