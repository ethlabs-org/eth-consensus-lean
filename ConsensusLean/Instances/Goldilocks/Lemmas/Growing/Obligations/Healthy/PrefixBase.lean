module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The static healthy AC base on a read prefix under growing faults

The finite reset service, read on the prefix through a read time `d`, is the static service of
the validators honest at `d` (`ResetService.upTo_at`: every sender and recipient of the prefix is
honest at its own cut). From it, the static AC synchrony window on that prefix
(`sync_window_at_reset_at`), the catch-up window from `ḡ` (`catch_window_at_gbar_at`), and the
static healthy AC base of the validators honest at `d` at the slot committees of a committee
half bound (`CommitteeHalfUpTo`, `CommitteeHalfUpTo.healthy_base_before_at`), at the stock
committee (`healthy_base_of_service_catch_before_at`) and from finite reset premises
(`healthy_base_of_reset_catch_before_at`). No reset is used. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-- **The service on a prefix**: the finite reset service, read on the prefix through `d ≥ 0`, is
the static reset service of the validators honest at `d`. -/
theorem ResetService.upTo_at {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
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
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
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

/-- **Catch from `ḡ` on the prefix through `d`**: an acceptance before `ḡ` by a validator honest
at `d` is accepted before `ḡ + 2Δ` by every validator honest at `d` whose finalized block it
extends, as observed at a call in `[ḡ + 2Δ, d]` (the run's catch-up at the first cut from
`ḡ + 2Δ ≤ d`, with each node honest at its own cut by antitonicity). -/
theorem catch_window_at_gbar_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
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

/-- **The committee half bound through `b`** for the slot dictionary `K`: the run's committee
facts at `K`, and fewer than half of each slot committee from `ḡ` by `b` faulty at every read time
`d ∈ [0, b]`. The stock committee is `K = full` (`CommitteeHalfUpTo.of_full`). Finite reset premises
give their slot committees (`ResetPremisesUpTo.committeeHalf`). -/
structure CommitteeHalfUpTo (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (K : SA.CommitteeDict sp.n) (g b : Time) : Prop where
  facts : Compose.Growing.CommitteeFacts tr H K
  cs2 : ∀ s : Nat, gbar g ≤ sp.ts s → sp.ts s ≤ b → ∀ d, 0 ≤ d → d ≤ b →
    2 * (K.committee s ∩ (H d)ᶜ).ncard < sp.committeeSize

/-- **The stock committee half bound**: at `K = full` with `committeeSize = n`, the stock committee
facts (`CommitteeFacts.of_full`) and CS2 from the per-time fault bound `3 f ≤ n − 1`. -/
theorem CommitteeHalfUpTo.of_full
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {b : Time}
    (hfaults : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hstock : sp.committeeSize = sp.n) :
    CommitteeHalfUpTo tr H (SA.CommitteeDict.full sp.n) g b := by
  refine ⟨Compose.Growing.CommitteeFacts.of_full hrun hnc hstock, fun _ _ _ d hd0 hdb => ?_⟩
  have hf := hfaults d hd0 hdb
  have hn : 0 < sp.n := sp.toParams.hn
  exact SA.cs2_full hstock (by omega)

/-- **The committee half bound of finite reset premises**, at their slot committees
(`committee_cs2_at`). -/
theorem ResetPremisesUpTo.committeeHalf {b : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK) :
    CommitteeHalfUpTo tr H (Generic.dictOfTime sp cm) g b :=
  ⟨hp.committeeFacts, fun _ hgs hsb _ hd0 hdb => hp.committee_cs2_at hgs hsb hd0 hdb⟩

/-- **The healthy AC premises on a read prefix, from the service and the committee half bound**:
the finite reset service, awake honest nodes from `ḡ`, the per-time fault bound and catch-up give
the static healthy AC base of the validators honest at a read time `d ∈ [0, b]`, on the prefix
through `d`, over the blocks they hold there, at the slot committees `K` of a run from `K`'s
committee start. Their facts restrict to the prefix, and the committee half bound gives CS2 from
`ḡ` through `d`. No reset is used. -/
theorem CommitteeHalfUpTo.healthy_base_before_at {K : SA.CommitteeDict sp.n} {b : Time}
    (hK : CommitteeHalfUpTo tr H K g b)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (SA.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hs : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hfaults : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hc : CatchRun tr H g (2 * sp.Δ)) {d : Time} (hd0 : 0 ≤ d) (hdb : d ≤ b) :
    SA.HealthyBaseUpTo K (tr.projAC.upTo d) (H d)
      ((tr.upTo d).HonestBlocks (H d)) proposer g d := by
  have hpre := hrun.upTo hd0
  have hncp := hnc.upTo d
  have hr := Compose.goldilocks_ac_projection_from hpre hncp
  have hdr := projection_driven_of_run hpre hncp hpre.genesis_root_ok
  rw [RunTrace.upTo_projAC] at hr hdr
  refine ⟨hr, hdr, sync_window_at_reset_at hrun hs (SA.le_gbar g) hd0,
    catch_window_at_gbar_at hrun hc hd0, ?_, hfaults d hd0 hdb, hK.facts.hsize,
    SA.CommitteePAt.upTo hrun.time_mono hrun.antitone hK.facts.hP d,
    SA.CommitteeTAt.upTo hrun.antitone (hK.facts.committeeTAt hrun hnc) d,
    fun s hgs hsd => hK.cs2 s hgs (hsd.trans hdb) d hd0 hdb⟩
  intro y hy t hgt htd
  exact (Trace.upTo_awake _ y t).mpr
    ⟨hawake y t (hrun.antitone htd hy) hgt (htd.trans hdb), htd⟩

/-- **The healthy AC premises on a read prefix, from the service alone**, at the stock committee:
`CommitteeHalfUpTo.healthy_base_before_at` at `K = full` (`CommitteeHalfUpTo.of_full`). -/
theorem healthy_base_of_service_catch_before_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {b : Time} (hs : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hfaults : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hc : CatchRun tr H g (2 * sp.Δ)) {d : Time} (hd0 : 0 ≤ d) (hdb : d ≤ b)
    (hstock : sp.committeeSize = sp.n) :
    SA.HealthyBaseUpTo (SA.CommitteeDict.full sp.n) (tr.projAC.upTo d) (H d)
      ((tr.upTo d).HonestBlocks (H d)) proposer g d :=
  (CommitteeHalfUpTo.of_full hrun hnc hfaults hstock).healthy_base_before_at
    (by rw [SA.committeeStart_full]; exact hrun) hnc hs hawake hfaults hc hd0 hdb

/-- **The healthy AC premises on a read prefix**: finite reset health and catch-up give the
static healthy AC base of the validators honest at a read time `d ∈ [0, b]`, on the prefix
through `d`, over the blocks they hold there, at the run's slot committees
(`CommitteeHalfUpTo.healthy_base_before_at` at `ResetPremisesUpTo.committeeHalf`). -/
theorem healthy_base_of_reset_catch_before_at {b : Time}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {d : Time} (hd0 : 0 ≤ d) (hdb : d ≤ b) :
    SA.HealthyBaseUpTo (Generic.dictOfTime sp cm) (tr.projAC.upTo d) (H d)
      ((tr.upTo d).HonestBlocks (H d)) proposer g d :=
  hp.committeeHalf.healthy_base_before_at hp.run hp.noColl hp.sync hp.awake hp.faults hp.catchUp
    hd0 hdb

end Consensus.Goldilocks.Healing.Growing

end
