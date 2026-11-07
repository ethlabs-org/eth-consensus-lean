module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Pending
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

The finite reset service, read on the prefix through a read time `d`, is the static service of
the validators honest at `d` (`ResetService.upTo_at`: every sender and recipient of the prefix is
honest at its own cut). From it, the static AC synchrony window at the reset on that prefix
(`sync_window_at_reset_at`), the input of the served head of a reader at `d`. The restart bound
and the late fault bound read each node's honesty at its own time (`restart_le_before_at`,
`fault_bound_late_before_at`). -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-- **The service on a prefix**: the finite reset service, read on the prefix through `d ≥ 0`, is
the static reset service of the validators honest at `d`. -/
theorem ResetService.upTo_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {b : Time} (hs : ResetService tr H g ΔF b) {d : Time} :
    Healing.ResetService (tr.upTo d) (H d) g ΔF b := by
  have hm := hrun.time_mono
  refine ⟨hs.deltaF, ?_, ?_, ?_, ?_⟩
  · intro x hx i m hsa y hy j hj hdl
    obtain ⟨hid, hsa⟩ := (RunTrace.upTo_sendOrAdmitAt hm).mp hsa
    obtain ⟨hjd, hj⟩ := (RunTrace.upTo_isCall (tr := tr)).mp hj
    rw [RunTrace.upTo_deadline hm hjd] at hdl
    obtain ⟨k, hkj, hτ, hpk, hkd⟩ :=
      hs.message x i m (hrun.antitone hid hx) hsa y j (hrun.antitone hjd hy) hj hdl
    have hk : tr.time k ≤ d := (hm hkj).trans hjd
    exact ⟨k, hkj, hτ, (RunTrace.upTo_processMsgAt (tr := tr)).mpr ⟨hk, hpk⟩,
      by rw [RunTrace.upTo_deadline hm hk]; exact hkd⟩
  · intro x hx i B hB y hy j hj hdl
    have hB' : (tr.time i ≤ d) ∧ (tr.AcceptAt x i B ∨ tr.OwnBlockAt x i B) := by
      rcases hB with hB | hB
      · obtain ⟨h, hB⟩ := (RunTrace.upTo_acceptAt (tr := tr)).mp hB
        exact ⟨h, Or.inl hB⟩
      · obtain ⟨h, hB⟩ := (RunTrace.upTo_ownBlockAt (tr := tr)).mp hB
        exact ⟨h, Or.inr hB⟩
    obtain ⟨hid, hB⟩ := hB'
    obtain ⟨hjd, hj⟩ := (RunTrace.upTo_isCall (tr := tr)).mp hj
    rw [RunTrace.upTo_deadline hm hjd] at hdl
    obtain ⟨k, hkj, hτ, hpk, hkd⟩ :=
      hs.block x i B (hrun.antitone hid hx) hB y j (hrun.antitone hjd hy) hj hdl
    have hk : tr.time k ≤ d := (hm hkj).trans hjd
    exact ⟨k, hkj, hτ, (RunTrace.upTo_blockCallAt (tr := tr)).mpr ⟨hk, hpk⟩,
      by rw [RunTrace.upTo_deadline hm hk]; exact hkd⟩
  · intro x hx i B hB hgi y hy j hj hdl hF
    obtain ⟨hid, hB⟩ := (RunTrace.upTo_acceptAt (tr := tr)).mp hB
    obtain ⟨hjd, hj⟩ := (RunTrace.upTo_isCall (tr := tr)).mp hj
    rw [RunTrace.upTo_deadline hm hjd] at hdl
    have hd0 : 0 ≤ d := (hrun.time_nonneg j).trans hjd
    rw [RunTrace.upTo_state_of_le hm hjd] at hF
    obtain ⟨k, hkj, hak, hkd⟩ := hs.relay x i B (hrun.antitone hid hx) hB hgi y j
      (hrun.antitone hjd hy) hj hdl (hF.mono (RunTrace.honestBlocks_upTo_subset hm hd0))
    have hk : tr.time k ≤ d := (hm hkj).trans hjd
    exact ⟨k, hkj, (RunTrace.upTo_acceptAt (tr := tr)).mpr ⟨hk, hak⟩,
      by rw [RunTrace.upTo_deadline hm hk]; exact hkd⟩
  · intro x hx i att hsg y hy j hj hjb hdl
    obtain ⟨hid, hsg⟩ := (RunTrace.upTo_signAt (tr := tr)).mp hsg
    obtain ⟨hjd, hj⟩ := (RunTrace.upTo_isCall (tr := tr)).mp hj
    rw [RunTrace.upTo_deadline hm hjd] at hdl
    obtain ⟨k, hkj, hpk, hkd⟩ :=
      hs.signedRow x i att (hrun.antitone hid hx) hsg y j (hrun.antitone hjd hy) hj hjb hdl
    have hk : tr.time k ≤ d := (hm hkj).trans hjd
    exact ⟨k, hkj, (RunTrace.upTo_processAttAt (tr := tr)).mpr ⟨hk, hpk⟩,
      by rw [RunTrace.upTo_deadline hm hk]; exact hkd⟩

/-- **AC synchrony from the reset on the prefix through `t`**: for the validators honest at `t`,
over the blocks they hold on that prefix, from any source time `a ≥ g` through `t`. -/
theorem sync_window_at_reset_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {b : Time} (hs : ResetService tr H g ΔF b) {t : Time} (hga : g ≤ a) (ht0 : 0 ≤ t) :
    SyncACWindowBefore (H t) ((tr.upTo t).HonestBlocks (H t)) a t (tr.projAC.upTo t) := by
  have hsy := (hs.upTo_at hrun (d := t)).syncAC (hi := t) (hrun.upTo ht0) hga
  rw [RunTrace.upTo_projAC] at hsy
  have hsource : ∀ y j (u : Time),
      u ≤ ACTrace.deadline (A := goldilocksNode sp ro) (tr.projAC.upTo t) y j u := by
    intro y j u
    unfold ACTrace.deadline
    have hΔ : 0 < sp.Δ := sp.toParams.hΔ
    cases ACTrace.lastWake (A := goldilocksNode sp ro) (tr.projAC.upTo t) y j with
    | bot => change u ≤ u + sp.Δ; linarith
    | coe w =>
      change u ≤ max u w + sp.Δ
      have := le_max_left u w
      linarith
  constructor
  · intro x hx i m hm hi y hy j ell hj ht hd
    exact hsy.1 x hx i m hm hi ((hsource y j _).trans ht) y hy j ell hj hd
  · intro x hx i B hB hi y hy j ell hj ht hd hF
    exact hsy.2 x hx i B hB hi ((hsource y j _).trans ht) y hy j ell hj hd hF

/-- **A restart of a node honest at it is no later than the slot after `ḡ`**: the node is awake
from `ḡ` on while honest, and ticks at the public time `t_{slot(ḡ)+1}`. -/
theorem restart_le_before_at {b : Time} (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    (hk : tr.RestartAt y k) (hkb : tr.time k ≤ b) :
    tr.time k ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
  by_contra hlt
  obtain ⟨u, -, huk, hu, hprev⟩ := hp.run.sleep_of_restart y k hy hk
  have hp₀ : gbar g ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
    have h := (SA.ts_le_iff_le_slot sp (SA.gbar_nonneg g)
      ((sp.slot (gbar g) + 1 : Nat) : Int)).not.mpr (by push_cast; omega)
    exact (not_le.mp h).le
  by_cases hgu : gbar g ≤ u
  · exact hu (hp.awake y u (hp.run.antitone huk.le hy) hgu (huk.le.trans hkb))
  · have hlt' := (lt_of_not_ge hlt).le
    obtain ⟨j, _x, hne, hcs, -⟩ := hp.run.tick_of_awake y _ (hp.run.antitone hlt' hy)
      ((SA.gbar_nonneg g).trans hp₀)
      ⟨4 * ((sp.slot (gbar g) + 1 : Nat) : Int), by simp only [SAParams.ts]; ring⟩
      (hp.awake y _ (hp.run.antitone hlt' hy) hp₀ (hlt'.trans hkb))
    obtain ⟨hn, ht, -, -, hl⟩ := hcs 0 (List.length_pos_of_ne_nil hne)
    simp only [Nat.add_zero] at hn ht hl
    have hjk : j < k := by
      by_contra h
      have := hp.run.time_mono (not_lt.mp h)
      exact hlt (ht ▸ this)
    have := hprev j hjk ⟨_, hn, hl⟩
    exact hgu (by linarith)

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
    refine ⟨by omega, (restart_le_before_at hp (hp.run.antitone hkt hyt) hk
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
premises of a healthy run. -/
theorem ResetPremisesUpTo.windows_at_reset_at {b ΔF' : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    (hh : tr.HealthyRunAt H ΔF' g) {t : Time} (ht0 : 0 ≤ t) (htb : t ≤ b) :
    SyncACWindowBefore (H t) ((tr.upTo t).HonestBlocks (H t)) a t (tr.projAC.upTo t) ∧
      CatchACWindowBefore (tr.projAC.upTo t) (H t) ((tr.upTo t).HonestBlocks (H t)) a
        (2 * sp.Δ) t := by
  have hca := cutZ_lt_reset_at hp.run hp.noColl hh hp.reset
  have hga : g ≤ a := by linarith [SA.le_gbar g, lt_cutZ sp g, sp.toParams.hΔ]
  exact ⟨sync_window_at_reset_at hp.run hp.sync hga ht0,
    catch_window_at_reset_at hp.run hp.sync hc ht0 hca
      fun y k hy hk hkt => restart_le_before_at hp hy hk (hkt.trans htb)⟩

/-- **Catch from `ḡ` on the prefix through `d`**: an acceptance before `ḡ` by a validator honest
at `d` is accepted before `ḡ + 2Δ` by every validator honest at `d` whose finalized block it
extends, as observed at a call in `[ḡ + 2Δ, d]` (the run's catch-up at the first cut from
`ḡ + 2Δ ≤ d`, with each node honest at its own cut by antitonicity). -/
theorem catch_window_at_gbar_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hc : CatchRun tr H g (2 * sp.Δ)) {d : Time} (hd0 : 0 ≤ d) :
    CatchACWindowBefore (tr.projAC.upTo d) (H d) ((tr.upTo d).HonestBlocks (H d)) (gbar g)
      (2 * sp.Δ) d := by
  have hm := hrun.time_mono
  have hpre := hrun.upTo hd0
  rw [← RunTrace.upTo_projAC]
  constructor
  intro x hx i B ha hi y hy j ell hj ht hjd hF
  change gbar g + 2 * sp.Δ ≤ tr.time j at ht
  change tr.time j ≤ d at hjd
  have hF' : Anc ((tr.upTo d).HonestBlocks (H d)) ((tr.upTo d).state y j).fg.F B := by
    rw [Compose.frame_of_projAC hpre hy hj] at hF
    exact hF
  obtain ⟨i', rfl, ha', hti⟩ := fg_accept_before hpre.toLocalRun hx ha
  change tr.time (i' + 1) < gbar g at hi
  change tr.time i' = tr.time (i' + 1) at hti
  obtain ⟨hid, ha''⟩ := (RunTrace.upTo_acceptAt (tr := tr)).mp ha'
  have hex : ∃ k, gbar g + 2 * sp.Δ ≤ tr.time k := ⟨j, ht⟩
  have hj₀ : tr.FirstCutFrom (Nat.find hex) (gbar g + 2 * sp.Δ) :=
    ⟨Nat.find_spec hex, fun k hk => not_le.1 (Nat.find_min hex hk)⟩
  have hj₀j : Nat.find hex ≤ j := Nat.find_min' hex ht
  have hj₀d : tr.time (Nat.find hex) ≤ d := (hm hj₀j).trans hjd
  have hanc₀ := (run_F_mono hpre.toLocalRun hy hj₀j).trans hF'
  rw [RunTrace.upTo_state_of_le hm hj₀d] at hanc₀
  obtain ⟨k, hk, hak⟩ := hc x i' B (hrun.antitone hid hx) ha'' (by rw [hti]; exact hi) y _
    (hrun.antitone (hj₀.1.trans hj₀d) hy) hj₀
    (Anc.mono (RunTrace.honestBlocks_upTo_subset hm hd0) hanc₀)
  have hkd : tr.time k ≤ d := (hm hk.le).trans hj₀d
  obtain ⟨hak', htk, -⟩ :=
    ac_block_after hpre.toLocalRun hy ((RunTrace.upTo_acceptAt (tr := tr)).mpr ⟨hkd, hak⟩)
  refine ⟨k + 1, by omega, hak', ?_⟩
  change tr.time (k + 1) < gbar g + 2 * sp.Δ
  change tr.time (k + 1) = tr.time k at htk
  rw [htk]
  exact hj₀.2 k hk

/-- **The healthy AC premises on a read prefix**: finite reset health and catch-up give the
static healthy AC base of the validators honest at a read time `d ∈ [0, b]`, on the prefix
through `d`, over the blocks they hold there. -/
theorem healthy_base_of_reset_catch_before_at {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {d : Time} (hd0 : 0 ≤ d) (hdb : d ≤ b) :
    SA.HealthyBaseUpTo (tr.projAC.upTo d) (H d) ((tr.upTo d).HonestBlocks (H d)) proposer g d := by
  have hpre := hp.run.upTo hd0
  have hncp := hp.noColl.upTo d
  have hr := Compose.goldilocks_ac_projection sp ro dg (H d) (tr.upTo d) proposer hpre hncp
  have hdr := projection_driven_of_run hpre hncp hpre.genesis_root_ok
  rw [RunTrace.upTo_projAC] at hr hdr
  refine ⟨hr, hdr, sync_window_at_reset_at hp.run hp.sync (SA.le_gbar g) hd0,
    catch_window_at_gbar_at hp.run hc hd0, ?_, hp.faults d hd0 hdb⟩
  intro y hy t hgt htd
  exact (Trace.upTo_awake _ y t).mpr
    ⟨hp.awake y t (hp.run.antitone htd hy) hgt (htd.trans hdb), htd⟩

end Consensus.Goldilocks.Healing.Growing

end
