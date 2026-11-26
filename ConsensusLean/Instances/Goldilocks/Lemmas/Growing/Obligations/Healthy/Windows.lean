module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The reset's service windows under growing faults

The AC catch-up window at the reset on the prefix through a read time
(`catch_window_at_reset_at`) and the reset's windows (`ResetPremisesUpTo.windows_at_reset_at`).
The finite reset service on the prefix (`ResetService.upTo_ac_at`), the synchrony and catch windows
it gives (`sync_window_at_reset_at`, `catch_window_at_gbar_at`) and the healthy AC base
(`healthy_base_of_reset_catch_before_at`) are proved in `Healthy/PrefixBase`, re-exported here.
The restart bound reads each node's honesty at its own time (`restart_le_before_at`). -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}
variable {hold : Time}

/-- **Catch at the reset on the prefix through `t`**: an acceptance before the reset `a` by a
validator honest at `t` is accepted before `a + 2Δ` by every validator honest at `t` whose
finalized block it extends, as observed at a call in `[a + 2Δ, t]`. Before `ḡ` this is the run's
catch-up (at the first cut from `ḡ + 2Δ ≤ t`); after `ḡ`, the prefix's acceptance relay, with the
restarts no later than the reset. -/
private theorem catch_window_at_reset_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {b : Time} (hs : ResetService tr H g ΔF b hold) (hc : CatchRun tr H g (2 * sp.Δ))
    {t : Time} (ht0 : 0 ≤ t) (hca : cutZ sp.toParams g < a)
    (hrestart : ∀ y k, y ∈ H (tr.time k) → tr.RestartAt y k → tr.time k ≤ t →
      tr.time k ≤ sp.ts (sp.slot (gbar g) + 1 : Nat)) :
    CatchACWindowBefore (tr.projAC.upTo t) (H t) ((tr.upTo t).HonestBlocks (H t)) a
      (2 * sp.Δ) t := by
  have hm := hrun.time_mono
  have hpre := hrun.upTo ht0
  have hss := hs.upTo_ac_at hrun (d := t)
  have hΔ := sp.toParams.hΔ
  have hga : gbar g < a := by linarith [lt_cutZ sp g]
  have hra : sp.ts (sp.slot (gbar g) + 1 : Nat) ≤ a := by
    apply le_trans _ hca.le
    rw [cutZ_eq]
    exact (AC.ts_le_iff sp).mpr (by omega)
  rw [← RunTrace.upTo_projAC]
  constructor
  intro x hx i B ha hi y hy j ell hj ht hjt hF
  change a + 2 * sp.Δ ≤ tr.time j at ht
  change tr.time j ≤ t at hjt
  have hF' : Anc ((tr.upTo t).HonestBlocks (H t)) ((tr.upTo t).state y j).fg.F B := by
    rw [Compose.frame_of_projAC hpre hy hj] at hF
    exact hF
  obtain ⟨i', rfl, ha', hti⟩ := fg_accept_before hpre.toLocalRun hx ha
  change tr.time (i' + 1) < a at hi
  change tr.time i' = tr.time (i' + 1) at hti
  by_cases hgi : tr.time (i' + 1) < gbar g
  · have hcatch := catch_window_at_gbar_at hrun hc ht0
    rw [← RunTrace.upTo_projAC] at hcatch
    obtain ⟨k, hkj, hak, hkt⟩ := hcatch.relay x hx (i' + 1) B ha hgi y hy j ell hj
      (by change gbar g + 2 * sp.Δ ≤ tr.time j; linarith) hjt hF
    exact ⟨k, hkj, hak, by change tr.time k < _; change tr.time k < _ at hkt; linarith⟩
  · have hia : tr.time i' < a := by simpa only [hti] using hi
    have hgg : g ≤ tr.time i' :=
      (AC.le_gbar g).trans (by simpa only [hti] using le_of_not_gt hgi)
    have hmax : max ((tr.upTo t).time i') g = (tr.upTo t).time i' := max_eq_left hgg
    have hdeadline : ∀ k ≤ j, (tr.upTo t).deadline y k (tr.time i') sp.Δ ≤ a + sp.Δ := by
      intro k hkj
      apply le_trans (Compose.deadline_le_of_restarts (a := a) (fun r hr hrest => by
        obtain ⟨hrt, hrest⟩ := (RunTrace.upTo_restartAt (tr := tr)).mp hrest
        have hrj : tr.time r ≤ t := (hm (hr.trans hkj)).trans hjt
        exact (hrestart y r (hrun.antitone hrj hy) hrest hrj).trans hra) _ _)
      rw [max_eq_right hia.le]
    have hrelay := hss.relay x hx i' B ha' hgg y hy j
      ⟨_, Compose.projAC_callAt.mp hj⟩ (by
        rw [hmax]
        exact (hdeadline j le_rfl).trans (by change a + sp.Δ ≤ tr.time j; linarith)) hF'
    rw [hmax] at hrelay
    obtain ⟨k, hk, hak, hkt⟩ := Compose.acRelay_of_acceptNext hj hrelay
      (fun _ _ => Compose.accept_next hpre.toLocalRun hy)
    rw [Compose.projAC_deadline] at hkt
    exact ⟨k, hk, hak, hkt.trans_le ((hdeadline k hk).trans (by linarith))⟩

/-- The reset's service windows on the prefix through a read time `t ≤ b`, from the finite reset
premises. -/
theorem ResetPremisesUpTo.windows_at_reset_at {b : Time}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {t : Time} (ht0 : 0 ≤ t) (htb : t ≤ b) :
    SyncACWindowBefore (H t) ((tr.upTo t).HonestBlocks (H t)) a t (tr.projAC.upTo t) ∧
      CatchACWindowBefore (tr.projAC.upTo t) (H t) ((tr.upTo t).HonestBlocks (H t)) a
        (2 * sp.Δ) t := by
  have hca := hp.cutZ_lt_reset_at
  have hga : g ≤ a := by linarith [AC.le_gbar g, lt_cutZ sp g, sp.toParams.hΔ]
  exact ⟨sync_window_at_reset_at hp.run hp.sync.toAC hga ht0,
    catch_window_at_reset_at hp.run hp.sync hp.catchUp ht0 hca
      fun y k hy hk hkt => restart_le_before_at hp hy hk (hkt.trans htb)⟩

end Consensus.Goldilocks.Healing.Growing

end
