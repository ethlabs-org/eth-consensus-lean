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

On the prefix through a read time `t ≤ b`, the static AC catch-up window from the reset
(`catch_window_at_reset_at`) and both windows from the finite reset premises
(`ResetPremisesUpTo.windows_at_reset_at`), from the prefix service of `PrefixBase`, with the
restart bound `ResetPremisesUpTo.restart_le_before_at`. The late fault bound reads each node's
honesty at its own time (`fault_bound_late_before_at`). -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-- **The late fault bound**: from the cut on, the faults at any `d ∈ [t, b]` are fewer than the
validators honest at `d` that are awake and joined at `t`. -/
theorem fault_bound_late_before_at {b : Time} (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {t d : Time} (ht : cutZ sp.toParams g ≤ t) (htd : t ≤ d) (hdb : d ≤ b) :
    tr.FaultBoundAt H t d := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hgt : gbar g ≤ t := by have := lt_cutZ sp g; linarith
  have ht0 : 0 ≤ t := (SA.gbar_nonneg g).trans hgt
  have hs : sp.slot (gbar g) + 3 ≤ sp.slot t := by
    have h := (SA.ts_le_iff_le_slot sp ht0 ((sp.slot (gbar g) + 3 : Nat) : Int)).mp
      ((cutZ_eq sp g) ▸ ht)
    exact_mod_cast h
  have hsub : H d ⊆ {y | y ∈ H d ∧ tr.awake y t ∧ tr.JoinedAt y t} := by
    intro y hy
    have hyt := hp.run.antitone htd hy
    refine ⟨hy, hp.awake y t hyt hgt (htd.trans hdb), fun k hk hkt => ?_⟩
    change 0 < sp.slot t ∧ tr.time k ≤ sp.toParams.slotTime (sp.slot t - 1)
    have he : sp.toParams.slotTime (sp.slot t - 1) = sp.ts ((sp.slot t - 1 : Nat) : Int) :=
      sp.slotTime_eq _
    refine ⟨by omega, (hp.restart_le_before_at (hp.run.antitone hkt hyt) hk
      (hkt.trans (htd.trans hdb))).trans ?_⟩
    rw [he]
    exact (SA.ts_le_iff sp).mpr (by omega)
  have hle := Set.ncard_le_ncard hsub
  have hn : (H d).ncard + (H d)ᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h3 := hp.faults d (ht0.trans htd) hdb
  have hpos := sp.toParams.hn
  have hn' : sp.n = sp.toParams.n := rfl
  unfold RunTrace.FaultBoundAt
  refine lt_of_lt_of_le ?_ hle
  omega

/-- **Catch at the reset on the prefix through `t`**: an acceptance before the reset `a` by a
validator honest at `t` is accepted before `a + 2Δ` by every validator honest at `t` whose
finalized block it extends, as observed at a call in `[a + 2Δ, t]`. Before `ḡ` this is the run's
catch-up (at the first cut from `ḡ + 2Δ ≤ t`); after `ḡ`, the prefix's acceptance relay, with the
restarts no later than the reset. -/
theorem catch_window_at_reset_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {b : Time} (hs : ResetService tr H g ΔF b) (hc : CatchRun tr H g (2 * sp.Δ))
    {t : Time} (ht0 : 0 ≤ t) (hca : cutZ sp.toParams g < a)
    (hrestart : ∀ y k, y ∈ H (tr.time k) → tr.RestartAt y k → tr.time k ≤ t →
      tr.time k ≤ sp.ts (sp.slot (gbar g) + 1 : Nat)) :
    CatchACWindowBefore (tr.projAC.upTo t) (H t) ((tr.upTo t).HonestBlocks (H t)) a
      (2 * sp.Δ) t := by
  have hm := hrun.time_mono
  have hpre := hrun.upTo ht0
  have hss := hs.upTo_at hrun (d := t)
  have hΔ := sp.toParams.hΔ
  have hga : gbar g < a := by linarith [lt_cutZ sp g]
  have hra : sp.ts (sp.slot (gbar g) + 1 : Nat) ≤ a := by
    apply le_trans _ hca.le
    rw [cutZ_eq]
    exact (SA.ts_le_iff sp).mpr (by omega)
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
  obtain ⟨hid, ha''⟩ := (RunTrace.upTo_acceptAt (tr := tr)).mp ha'
  by_cases hgi : tr.time (i' + 1) < gbar g
  · have hex : ∃ k, gbar g + 2 * sp.Δ ≤ tr.time k := ⟨j, by linarith⟩
    have hj₀ : tr.FirstCutFrom (Nat.find hex) (gbar g + 2 * sp.Δ) :=
      ⟨Nat.find_spec hex, fun k hk => not_le.1 (Nat.find_min hex hk)⟩
    have hj₀j : Nat.find hex ≤ j := Nat.find_min' hex (by linarith)
    have hj₀t : tr.time (Nat.find hex) ≤ t := (hm hj₀j).trans hjt
    have hanc₀ := (run_F_mono hpre.toLocalRun hy hj₀j).trans hF'
    rw [RunTrace.upTo_state_of_le hm hj₀t] at hanc₀
    obtain ⟨k, hk, hak⟩ := hc x i' B (hrun.antitone hid hx) ha''
      (by rw [hti]; exact hgi) y _
      (hrun.antitone (hj₀.1.trans hj₀t) hy) hj₀
      (Anc.mono (RunTrace.honestBlocks_upTo_subset hm ht0) hanc₀)
    have hkt : tr.time k ≤ t := (hm hk.le).trans hj₀t
    obtain ⟨hak', htk, -⟩ :=
      ac_block_after hpre.toLocalRun hy ((RunTrace.upTo_acceptAt (tr := tr)).mpr ⟨hkt, hak⟩)
    refine ⟨k + 1, by omega, hak', ?_⟩
    change tr.time (k + 1) < a + 2 * sp.Δ
    change tr.time (k + 1) = tr.time k at htk
    rw [htk]
    linarith [hj₀.2 k hk]
  · have hia : tr.time i' < a := by simpa only [hti] using hi
    have hgg : g ≤ tr.time i' :=
      (SA.le_gbar g).trans (by simpa only [hti] using le_of_not_gt hgi)
    have hmax : max ((tr.upTo t).time i') g = (tr.upTo t).time i' := max_eq_left hgg
    have hdeadline : ∀ k ≤ j, (tr.upTo t).deadline y k (tr.time i') sp.Δ ≤ a + sp.Δ := by
      intro k hkj
      apply le_trans (Compose.deadline_le_of_restarts (a := a) (fun r hr hrest => by
        obtain ⟨hrt, hrest⟩ := (RunTrace.upTo_restartAt (tr := tr)).mp hrest
        have hrj : tr.time r ≤ t := (hm (hr.trans hkj)).trans hjt
        exact (hrestart y r (hrun.antitone hrj hy) hrest hrj).trans hra) _ _)
      rw [max_eq_right hia.le]
    obtain ⟨k, hk, hak, hkt⟩ := hss.relay x hx i' B ha' hgg y hy j
      ⟨_, Compose.projAC_callAt.mp hj⟩ (by
        rw [hmax]
        exact (hdeadline j le_rfl).trans (by change a + sp.Δ ≤ tr.time j; linarith)) hF'
    obtain ⟨hak', htk, -⟩ := ac_block_after hpre.toLocalRun hy hak
    have hkj : k < j := by
      rcases hk.lt_or_eq with hk | rfl
      · exact hk
      · exact absurd (hak.2.symm.trans (Compose.projAC_callAt.mp hj).2) (by simp)
    refine ⟨k + 1, hkj, hak', ?_⟩
    change tr.time (k + 1) < a + 2 * sp.Δ
    change tr.time (k + 1) = tr.time k at htk
    rw [htk]
    rw [hmax] at hkt
    exact lt_of_lt_of_le hkt ((hdeadline k hk).trans (by linarith))

/-- The reset's service windows on the prefix through a read time `t ≤ b`, from the finite reset
premises. -/
theorem ResetPremisesUpTo.windows_at_reset_at {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {t : Time} (ht0 : 0 ≤ t) (htb : t ≤ b) :
    SyncACWindowBefore (H t) ((tr.upTo t).HonestBlocks (H t)) a t (tr.projAC.upTo t) ∧
      CatchACWindowBefore (tr.projAC.upTo t) (H t) ((tr.upTo t).HonestBlocks (H t)) a
        (2 * sp.Δ) t := by
  have hca := hp.cutZ_lt_reset_at
  have hga : g ≤ a := by linarith [SA.le_gbar g, lt_cutZ sp g, sp.toParams.hΔ]
  exact ⟨sync_window_at_reset_at hp.run hp.sync hga ht0,
    catch_window_at_reset_at hp.run hp.sync hc ht0 hca
      fun y k hy hk hkt => hp.restart_le_before_at hy hk (hkt.trans htb)⟩

end Consensus.Goldilocks.Healing.Growing

end
