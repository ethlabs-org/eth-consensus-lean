module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGStore.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Committee
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Compat
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: post-reset source and transport foundations

The objects of the post-reset argument (with HS.2)
after the reset `a = a_z`, stated over the run, for every consumer
(C1.2 here, H.3 (c)'s `Inv` half), not specialized to C1.2's entries.
With `b = slot(a) + 3` (`cleanLabel`) and `R = t_{b+2k+2}` (`drainTime`, the `R_z` of C1.2):

* **RN, stored ancestry is irreversible**: every lock stored at a later cut sits below a
  stored lock of its slot at an earlier cut, or below a fresh write between them
  (`stored_lock_below`, `AC.lock_provenance_fromU` on the AC projection). **RU** is
  `AC.unlock_compatible`: unlocking against a view with at least `n/2` validators whose slot-`s`
  support votes extend `B`, or that equivocate, moves every lock of a slot below `s` to a block
  compatible with `B`.
* **The drain** (HS.2 (3)): from `R` on, every live lock has a label at least `b + k + 2`, so
  every lock with a label before `b` or a slow window straddling `b` has expired
  (`drain_live_locks`).
* **Clean fast transfer** (`clean_fast_transfer`, HS.2 (1)): the stored block of a fast lock of
  label `≥ b` written by an honest joined node is extended by every honest vote of a later slot,
  and is in the voter's viable voter block tree or at or below its `fc_root` there (HR.4 (R3)
  when it is high; inherited from a high seed when it is a low ancestor of one).

`Outcome.Pivot` consumes these source facts. The downstream `Outcome.Supplier` retains
`ready_unanimous` and the report-cover suppliers; this separation lets
those suppliers use the pivot without an import cycle. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams ReplayOrder Payload Vote)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}

/-- The first clean evidence label `b = slot(a) + 3` after the reset `a`. -/
def cleanLabel (sp : ACParams) (a : Time) : Nat := sp.slot a + 3

/-- The drain time `R = t_{b+2k+2} = t_{slot(a)+2k+5}` (C1.2's `R_z`). -/
def drainTime (sp : ACParams) (a : Time) : Time := sp.ts (sp.slot a + 2 * sp.k + 5 : Nat)

theorem cleanLabel_eq (a : Time) : cleanLabel sp a = sp.slot a + 3 := by rfl

theorem drainTime_eq (a : Time) : drainTime sp a = sp.ts (sp.slot a + 2 * sp.k + 5 : Nat) := by
  rfl

/-- A time `a ≥ 0` is before its drain time. -/
theorem lt_drainTime {a : Time} (ha0 : 0 ≤ a) : a < drainTime sp a := by
  have ha : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
    have := (AC.ts_le_iff_le_slot sp ha0 _).1 h
    omega
  have hle : sp.ts ((sp.slot a : Int) + 1) ≤ drainTime sp a :=
    (AC.ts_le_iff sp).2 (by push_cast; omega)
  exact ha.trans_le hle

/-- A slot that starts at or after the drain time of a reset after `c_z` is after the slot of
`ḡ`. -/
theorem slot_gbar_lt_of_drainTime_le {g a : Time} {u : Nat} (hca : cutZ sp.toParams g < a)
    (hR : drainTime sp a ≤ sp.ts u) : sp.slot (AC.gbar g) + 1 ≤ u := by
  have ha0 : 0 ≤ a := by linarith [lt_cutZ (sp := sp) g, AC.gbar_nonneg g, sp.toParams.hΔ]
  exact slot_gbar_lt_of_cutZ_le (by linarith [lt_drainTime (sp := sp) ha0])

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {K : AC.CommitteeDict sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State} {g ΔF a : Time}

/-- **The drain** (HS.2 (3)): at a time `t ≥ R`, every live lock of an honest node has a
label at least `b + k + 2`; every lock of a label before `b`, and every slow lock whose window
straddles `b`, has expired. The locks are those of a run (`LocksWF`: every expiry is at most
`k` slots after the label), as every honest node's are (`AC.locksWF_state`). -/
theorem drain_live_locks {Φ : AC.Frm sp.n (List (FG.Att sp.n))} {L : Set AC.Lock} {t : Time}
    (hwf : AC.LocksWF sp L) (ht : drainTime sp a ≤ t) :
    ∀ l ∈ AC.liveLocks sp L Φ t, cleanLabel sp a + sp.k + 2 ≤ l.slot := by
  intro l hl
  have hk := hwf.slot_le_of_live hl
  have h0 : 0 ≤ t := le_trans (by
    rw [drainTime_eq]
    simp only [ACParams.ts]
    exact mul_nonneg (by linarith [sp.toParams.hΔ]) (Int.natCast_nonneg _)) ht
  rw [drainTime_eq] at ht
  have hs := (AC.ts_le_iff_le_slot sp h0 _).1 ht
  rw [cleanLabel_eq]
  omega

/-- A stored lock that is live by time after the drain has a clean label. This requires
neither normalized `liveLocks` membership nor a later `addLocks` call. -/
theorem drain_stored_lock_label {l : AC.Lock} {t : Time}
    (ht : drainTime sp a ≤ t) (hlive : sp.slot t ≤ l.slot + sp.k) :
    cleanLabel sp a + sp.k + 2 ≤ l.slot := by
  have h0 : 0 ≤ t := le_trans (by
    rw [drainTime_eq]
    simp only [ACParams.ts]
    exact mul_nonneg (by linarith [sp.toParams.hΔ]) (Int.natCast_nonneg _)) ht
  rw [drainTime_eq] at ht
  have hs := (AC.ts_le_iff_le_slot sp h0 _).1 ht
  rw [cleanLabel_eq]
  omega

/-! ### The clean fast transfer -/

/-- The reset supplies an actual bounded high-origin seed, not merely an eventual origin. -/
theorem ResetPremisesUpTo.reset_seed {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b) :
    ∃ v r l O, HighOrigin tr H g v r l O ∧ tr.time r ≤ a ∧ l ≤ sp.slot a := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  obtain ⟨⟨y, hy, k, att, hs, hh, hka⟩, -⟩ := hp.reset
  obtain ⟨r, hrk, l, O, ho, -⟩ := hp.high_row_source hy hs hh.ge
  obtain ⟨-, D, CV, -, hfl, -⟩ := hp.highOrigin_mem ho
  have htime : sp.ts l ≤ tr.time r := by
    have hΔ := sp.toParams.hΔ
    rcases hfl with ⟨ell, C, ⟨-, -, ht, -⟩, -⟩ | ⟨ell, A, -, hsl, -⟩
    · have ht' : tr.time r = sp.ts l + 6 * sp.Δ := ht
      rw [ht']; linarith only [hΔ]
    · exact (AC.ts_le_iff_le_slot sp (hr.time_nonneg r) l).mpr (by clear * - hsl; omega)
  have hra : tr.time r ≤ a := (hr.time_mono hrk.le).trans hka.le
  refine ⟨y, r, l, O, ho, hra, ?_⟩
  have ha0 : 0 ≤ a := hka ▸ hr.time_nonneg k
  exact_mod_cast (AC.ts_le_iff_le_slot sp ha0 l).mp (htime.trans hra)

/-! ### The clean slow transfer -/

/-- **`Sync` from `ḡ`** over the AC projection, from finite reset service (message processing
and acceptance relay from `ḡ` on, observed by `b`). -/
theorem sync_window_of_service {b : Time} (hrun : GoldilocksRun proposer dg H tr ini)
    (hsync : ResetService tr H g ΔF b) :
    SyncACWindowBefore H (tr.HonestBlocks H) (AC.gbar g) b tr.projAC := by
  have h := hrun.toLocalRun
  constructor
  · intro x hx i m hsa hi y hy j ℓ hcj _ hdl
    have hsa' : tr.SendOrAdmitAt x i m := by
      obtain ⟨ℓ, hc, hm⟩ := hsa
      refine ⟨ℓ, Compose.projAC_callAt.1 hc, ?_⟩
      rwa [Compose.projAC_state h hx] at hm
    have he : max (tr.time i) g = tr.time i := max_eq_left ((AC.le_gbar g).trans hi)
    rw [Compose.projAC_deadline] at hdl
    obtain ⟨k, hk, h1, h2, h3⟩ := hsync.message x hx i m hsa' y hy j
      ⟨_, Compose.projAC_callAt.1 hcj⟩ (by rw [he]; exact hdl)
    refine ⟨k, hk, h1, ?_, ?_⟩
    · rcases h2 with ⟨ℓ', hc', hm'⟩ | ⟨ℓ', hc', e, he', hem⟩
      · exact ⟨ℓ', Compose.projAC_callAt.2 hc', Or.inl hm'⟩
      · exact ⟨ℓ', Compose.projAC_callAt.2 hc', Or.inr ⟨e, he', hem⟩⟩
    · rw [Compose.projAC_deadline]
      change tr.time k < tr.deadline y k (tr.time i) sp.Δ
      simpa only [he] using h3
  · intro x hx i B ha hi y hy j ℓ hcj _ hdl hanc
    obtain ⟨i', rfl, ha', hti⟩ := fg_accept_before h hx ha
    have hgi : g ≤ tr.time i' := hti ▸ (AC.le_gbar g).trans hi
    have hmax : max (tr.time i') g = tr.time (i' + 1) := (max_eq_left hgi).trans hti
    apply Compose.acRelay_of_acceptNext (σ := tr.time (i' + 1)) hcj ?_
      (fun _ _ => Compose.accept_next h hy)
    simpa only [hmax] using hsync.relay x hx i' B ha' hgi y hy j
      ⟨_, Compose.projAC_callAt.1 hcj⟩ (by rw [hmax, ← Compose.projAC_deadline]; exact hdl)
      (by rwa [Compose.frame_of_projAC hrun hy hcj] at hanc)

/-- **Catch from `ḡ`** over the AC projection, from `Catch(2Δ)` of the run. -/
theorem catch_window_of_run {b : Time} (hrun : GoldilocksRun proposer dg H tr ini)
    (hc : CatchRun tr H g (2 * sp.Δ)) :
    CatchACWindowBefore tr.projAC H (tr.HonestBlocks H) (AC.gbar g) (2 * sp.Δ) b :=
  ⟨fun x hx i B ha hi y hy j ell hj ht _ hF =>
    projection_catch_of_run hrun hc x hx i B ha hi y hy j ell hj ht hF⟩

/-- **The AC base from the first slot start after `ḡ`**: finite service, awake honest validators,
Catch, the committee facts of `K` and CS2 after the slot of `ḡ` supply the AC base at
`g' = t_{slot(ḡ)+1}`, with every honest restart within the horizon at or before `g'`. Its CS2
guard `gbar g' ≤ t_s` is `slot(ḡ) + 1 ≤ s`; Sync and awake hold from the earlier `ḡ`, and Catch by
`g' + 2Δ` from Catch by `ḡ + 2Δ` and the relay of the acceptances in `[ḡ, g')`. No reset is used. -/
theorem healthy_base_of_service_catch_before {b : Time}
    (hrun : GoldilocksRun proposer dg H tr (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr)
    (hsync : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, AC.gbar g ≤ t → t ≤ b → tr.awake y t)
    (hfaults : 3 * Hᶜ.ncard ≤ sp.n - 1)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hK : Compose.Growing.CommitteeFacts tr (fun _ => H) K)
    (htwo : ∀ s : Nat, sp.slot (AC.gbar g) + 1 ≤ s →
      2 * (K.committee s ∩ Hᶜ).ncard < (K.committee s).ncard)
    (hrest : ∀ y ∈ H, ∀ k, tr.RestartAt y k → tr.time k ≤ b →
      tr.time k ≤ sp.ts (sp.slot (AC.gbar g) + 1 : Nat)) :
    AC.HealthyBaseUpTo K tr.projAC H (tr.HonestBlocks H) proposer
      (sp.ts (sp.slot (AC.gbar g) + 1 : Nat)) b := by
  have hsync0 := sync_window_of_service hrun hsync
  have hlt := gbar_lt_slotAfter (sp := sp) g
  have hΔ := sp.toParams.hΔ
  refine ⟨Compose.goldilocks_ac_projection_from hrun hnc,
    projection_driven_of_run hrun hnc hrun.genesis_root_ok, ?_, ?_,
    fun y hy t ht htb => hawake y hy t (by rw [gbar_slotAfter] at ht; linarith) htb, hfaults,
    hK.hsize, committeeP_of_facts hK hrun, committeeT_of_facts hK hrun hnc,
    fun s hgs _ => cs2_of_twoK hK htwo
      (slot_gbar_lt_of_slotAfter_le (by rwa [gbar_slotAfter] at hgs))⟩
  · rw [gbar_slotAfter]
    exact hsync0.mono hlt.le
  · rw [gbar_slotAfter]
    exact (catch_window_of_run hrun hc).shift hsync0 hlt.le (fun hkc => hrun.time_mono hkc)
      (fun y hy k hk hkb => hrest y hy k (Compose.projAC_restartAt.mp hk) hkb) (by linarith)

/-- Finite reset health supplies the AC base from the first slot start after `ḡ` without
extending awake obligations past the horizon. Synchrony and Catch retain their actual deadline
semantics. -/
theorem healthy_base_of_reset_catch_before {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) :
    AC.HealthyBaseUpTo K tr.projAC H (tr.HonestBlocks H) proposer
      (sp.ts (sp.slot (AC.gbar g) + 1 : Nat)) b :=
  healthy_base_of_service_catch_before hp.run hp.noColl hp.sync hp.awake hp.faults hc hp.committee
    hp.twoK fun _ hy _ hk hkb => restart_le_before hp hy hk hkb

/-- An actual result within the healthy horizon has an actual earlier honest supporter. -/
theorem ResetPremisesUpTo.result_supporter {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b) {x : Fin sp.n} (hx : x ∈ H) {r s : Nat}
    {B C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : AC.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocks H) B C)
    (hrb : tr.time r ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts s) :
    ∃ z ∈ H, ∃ q < r, ∃ e, AC.VoteAt tr.projAC z q e ∧ e.msg ∈ CV ∧
      e.msg.slot = s ∧ AC.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hΔ := sp.toParams.hΔ
  obtain ⟨ell, hu, hconf, hCV⟩ := hres
  have ht : tr.time r = sp.ts s + 6 * sp.Δ := hu.2.2.1
  have hsb : sp.ts s + sp.Δ ≤ b := by linarith
  have hgs : AC.gbar g ≤ sp.ts s := by have := lt_cutZ sp g; linarith
  have hsl : sp.slot (sp.ts s + sp.Δ) = s :=
    AC.slot_of_mem sp s (by linarith) (by simp only [ACParams.ts]; push_cast; linarith)
  have hs3 : sp.slot (AC.gbar g) + 3 ≤ s := by
    have h := (AC.ts_le_iff sp).mp ((cutZ_eq sp g) ▸ hts)
    exact_mod_cast h
  have hready : ∀ y ∈ H, tr.awake y (sp.ts s + sp.Δ) ∧
      tr.JoinedAt y (sp.ts s + sp.Δ) := by
    intro y hy
    refine ⟨hp.awake y hy _ (by linarith only [hΔ, hgs]) hsb, fun k hk hkt => ?_⟩
    change 0 < sp.slot (sp.ts s + sp.Δ) ∧
      tr.time k ≤ sp.toParams.slotTime (sp.slot (sp.ts s + sp.Δ) - 1)
    rw [hsl, sp.slotTime_eq]
    exact ⟨by omega, (restart_le_before hp hy hk (hkt.trans hsb)).trans
      ((AC.ts_le_iff sp).mpr (by
        exact_mod_cast (show sp.slot (AC.gbar g) + 1 ≤ s - 1 by clear * - hs3; omega)))⟩
  have hparts := Compose.honest_participants_window_before hp.run hp.noColl (K := K)
    (AC.serviceWindowBefore_of_sync (sync_window_of_service hp.run hp.sync)) hgs hx hu hrb
    hready (fun y hy hyK i => (hp.mayVote_iff hy i s).2 hyK)
    (fun v hv => hp.hP.1 x hx r s v hv)
    (by rw [hp.hsize s]; exact hp.cs2 (by clear * - hs3; omega))
  exact AC.result_honest_supporter_of_participants sp
    (Compose.goldilocks_ac_projection_from hp.run hp.noColl) hx ⟨ell, hu, hconf, hCV⟩
    hBC hparts.le

/-- Finite raw-prefix domain from actual bounded source and cast witnesses. -/
theorem ResetPremisesUpTo.result_prefix_vote_domain_before {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r s i : Nat}
    {B C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : AC.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocks H) B C)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hcast : AC.CastAt tr.projAC y i ell e) (hsi : s < e.msg.slot) (hib : tr.time i ≤ b)
    (hprior : ∀ z ∈ H, ∀ q < i, ∀ e', AC.VoteAt tr.projAC z q e' →
      s < e'.msg.slot → AC.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    Anc (tr.HonestBlocks H) B ell.frame.fcRoot ∨
      B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  have hac := Compose.goldilocks_ac_projection_from hp.run hp.noColl
  have hr := hac.localRun
  have hsync := sync_window_of_service hp.run hp.sync
  have hΔ := sp.toParams.hΔ
  obtain ⟨v, d, m, S, hseed, hda, hm⟩ := hp.reset_seed
  have hdb := hda.trans hp.reset_le
  have hms : m < s := by rw [cleanLabel_eq] at hs; (clear * - hs hm; omega)
  have hts : cutZ sp.toParams g ≤ sp.ts s :=
    (hp.cutZ_le_ts_of_highOrigin hseed).trans ((AC.ts_le_iff sp).mpr (by clear * - hms; omega))
  have hgs : AC.gbar g ≤ sp.ts s := by have := lt_cutZ sp g; linarith only [hΔ, hts, this]
  obtain ⟨z, hz, q, hqr, ev, hv, _, hvs, hVB⟩ :=
    hp.result_supporter hx hres hBC hrb hts
  have hqb := (hp.run.time_mono hqr.le).trans hrb
  obtain ⟨ellX, hupd, hconf, -⟩ := hres
  have hCx := hp.frame_tree_subset hx hupd.1 (AC.deepest_mem hconf).1.1
  have hBx := hp.mem_tree_of_anc hx hBC hCx
  have hreset : ∀ w ∈ H, ∀ c, tr.time c ≤ b → tr.projAC.RestartAt w c →
      tr.time c ≤ sp.ts s := by
    intro w hw c hcb hrestart
    apply (restart_le_before hp hw (Compose.projAC_restartAt.mp hrestart) hcb).trans
    have hh := (AC.ts_le_iff sp).mp ((cutZ_eq sp g) ▸ hts)
    exact (AC.ts_le_iff sp).mpr (by clear * - hh; omega)
  apply hp.held_target_vote_domain_before hx hy hBx hcast ?_ hseed (by clear * - hsi hms; omega)
    (hp.target_compatible_older_origin hseed hdb hz hv hqb hvs hms hVB) ?_ ?_ ?_
  · intro hF
    exact raw_writer_voterBlockTree_window_before hp.committee_pos hr hp.run.vstart hsync
      (catch_window_of_run hp.run hc) hx hy
      (Or.inl ⟨ellX, hupd, hconf, rfl⟩) hBC hcast (by clear * - hsi; omega) hib
      (by
        have := (AC.ts_le_iff sp).mpr (show (s : Int) ≤ e.msg.slot - 1 by clear * - hsi; omega)
        linarith only [hΔ, hgs, this]) hF
  · intro w c n O hci ho
    have hcb := (hp.run.time_mono hci.le).trans hib
    rcases lt_trichotomy n s with hn | rfl | hn
    · exact hp.target_compatible_older_origin ho hcb hz hv hqb hvs hn hVB
    · obtain ⟨CV', hst⟩ := ho.2.2.1
      obtain ⟨_, D, hfl, hOD⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
      have hcomp : Compatible (tr.HonestBlocks H) C D := by
        rcases hfl with ⟨ellD, R, huD, hR, hfast, _⟩ | hop
        · have hDR := ((AC.deepest_mem hfast).1.1.2.2).mono
            (AC.frameIn_of_callAt hr ho.1 huD.1).2
          have hRR := AC.result_result_compatible_window_before hac hsync hgs
            hx ho.1 ⟨ellX, hupd, hconf, rfl⟩ ⟨ellD, huD, hR, rfl⟩ hrb hcb
            (fun w hw c' hle hrest => hreset w hw c'
              ((hp.run.time_mono hle).trans (by
                rcases le_total r c with h | h
                · simpa only [max_eq_right h] using hcb
                · simpa only [max_eq_left h] using hrb)) hrest)
          rcases hRR with h | h
          · exact AC.anc_total hr.coherent h hDR
          · exact Or.inr (hDR.trans h)
        · exact AC.result_optimistic_compatible_window_before_of_voters hac hsync hgs
            hx ho.1 ⟨ellX, hupd, hconf, rfl⟩ hop hrb
            (fun c' hle hrest => hreset x hx c' ((hp.run.time_mono hle).trans hrb) hrest)
            ((Set.ncard_le_ncard (t := K.committee _) (by
                rintro _ ⟨v, hv, rfl⟩; exact hp.hP.1 x hx r _ v hv)).trans (hp.hsize _).le)
      rcases hcomp with h | h
      · exact AC.anc_total hr.coherent (hBC.trans h) hOD
      · exact AC.anc_total hr.coherent hBC (hOD.trans h)
    · exact hp.target_compatible_later_origin_before ho hci hn hprior
  · intro w c n O hci ho
    exact hp.origins_compatible hseed hdb ho ((hp.run.time_mono hci.le).trans hib)
  · intro w c n O hci ho w' c' n' O' hci' ho'
    exact hp.origins_compatible ho ((hp.run.time_mono hci.le).trans hib)
      ho' ((hp.run.time_mono hci'.le).trans hib)

/-- Finite recent-result induction. Current vote domains and first-successor stored-lock
comparisons are the explicit inputs `hdomain` and `hstored`, rather than whole-history
invariants. -/
theorem ResetPremisesUpTo.late_result_prefix_votes_before {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x : Fin sp.n} (hx : x ∈ H) {r s : Nat}
    {B C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : AC.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocks H) B C)
    (hrb : tr.time r ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts s)
    (hdomain : ∀ y ∈ H, ∀ i ell e, AC.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → s < e.msg.slot →
      (∀ z ∈ H, ∀ q < i, ∀ e', AC.VoteAt tr.projAC z q e' →
        s < e'.msg.slot → AC.VoteExtends (tr.HonestBlocks H) e'.msg B) →
      Anc (tr.HonestBlocks H) B ell.frame.fcRoot ∨
        B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
    (hstored : ∀ y ∈ H, ∀ i ell e, AC.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → e.msg.slot = s + 1 → ∀ l ∈ (tr.projAC.state y i).locks,
        sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
        ∀ Y ∈ tr.HonestBlocks H, Y.root = l.block → Compatible (tr.HonestBlocks H) Y B) :
    ∀ i, tr.time i ≤ b → ∀ y ∈ H, ∀ ell e, AC.CastAt tr.projAC y i ell e →
      s < e.msg.slot → AC.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hac := Compose.goldilocks_ac_projection_from hp.run hp.noColl
  have hr := hac.localRun
  have hsync := sync_window_of_service hp.run hp.sync
  have hcatch := catch_window_of_run (b := b) hp.run hc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hgs : AC.gbar g ≤ sp.ts s := by have := lt_cutZ sp g; linarith
  have hs1 := slot_gbar_lt_of_cutZ_le hts
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hib y hy ell e hcast hsi
    have hprior : ∀ z ∈ H, ∀ q < i, ∀ e', AC.VoteAt tr.projAC z q e' →
        s < e'.msg.slot → AC.VoteExtends (tr.HonestBlocks H) e'.msg B := by
      rintro z hz q hqi e' ⟨ell', hc'⟩ hse
      exact ih q hqi ((hp.run.time_mono hqi.le).trans hib) z hz ell' e' hc' hse
    obtain ⟨hΦ, hΦU⟩ := AC.frameIn_of_callAt hr hy hcast.1
    rcases hdomain y hy i ell e hcast hib hsi hprior with hBF | hv
    · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := Compose.cast_head_fcRoot hr
        hp.run.vstart hy hcast
      exact ⟨Hd, hΦU hHd, hHdr, hBF.trans (hfHd.mono hΦU)⟩
    have hFB := (hΦ.rooted.2 B hv.1.1).mono hΦU
    by_cases hfirst : e.msg.slot = s + 1
    · have carry : AC.CarryAt tr.projAC (tr.HonestBlocks H) y i e s CV := by
        apply Compose.carryAt_of_writer_window_before hr hp.run.vstart
          (AC.serviceWindowBefore_of_sync hsync) hgs hcatch (by linarith only [hΔ, hgs]) hx hy
          hcast hfirst hib
        intro v hv
        obtain ⟨hvs, hw, D, hD, hDr, hCD, ha⟩ := Compose.result_writer hr
          hp.run.vstart hx hres v hv
        exact ⟨hvs, hw, D, hD, hDr, hFB.trans (hBC.trans hCD), ha⟩
      refine AC.result_prefix_vote_extends_of_stored hac K hp.hP hx hy
        (hp.cs2 (by clear * - hs1; omega)) hres hBC hcast
        hfirst carry ?_ (hstored y hy i ell e hcast hib hfirst)
        (fun z hz q hq e' he hslot => hprior z hz q hq e' he (by clear * - hslot; omega)) ?_
      · rw [← hfirst]; exact Or.inl hv
      · obtain ⟨ellX, hupd, -⟩ := hres
        exact AC.writer_merged_window_before hac (AC.serviceWindowBefore_of_sync hsync)
          hx hgs hupd hrb hy hcast hfirst
    · obtain ⟨m, hm⟩ : ∃ m, e.msg.slot = m + 1 := ⟨e.msg.slot - 1, by omega⟩
      have hsm : s < m := by omega
      have hone : ∀ v ∈ Compose.honestVotes tr H m,
          AC.CarryAt tr.projAC (tr.HonestBlocks H) y i e m {v} := by
        rintro v ⟨z, hz, q, e', ⟨ell', hc'⟩, rfl, hslot⟩
        have hqi : q < i := by
          by_contra hn
          have := AC.slot_mono sp (hr.time_nonneg i) (hr.time_mono (Nat.le_of_not_gt hn))
          have := (AC.castAt_specU hr.toU hz hc').2.1
          have := (AC.castAt_specU hr.toU hy hcast).2.1
          omega
        obtain ⟨Hv, hHv, hHvr, hBHv⟩ := hprior z hz q hqi e' ⟨ell', hc'⟩ (by
            clear * - hsm hslot; omega)
        obtain ⟨⟨Hd, hHd, hHdr, -⟩, hqt⟩ := Compose.cast_head_fcRoot hr
            hp.run.vstart hz hc'
        obtain rfl : Hd = Hv := hr.coherent.1 ((AC.frameIn_of_callAt hr hz hc'.1).2 hHd)
          hHv (hHdr.trans hHvr.symm)
        have hgm := hgs.trans ((AC.ts_le_iff sp).mpr (show (s : Int) ≤ m by clear * - hsm; omega))
        apply Compose.carryAt_of_writer_window_before hr hp.run.vstart
          (AC.serviceWindowBefore_of_sync hsync) hgm hcatch (by linarith only [hΔ, hgm]) hz hy
          hcast hm hib
        rintro v rfl
        have ht : tr.projAC.time q < sp.ts m + 2 * sp.Δ := by
          rw [hslot] at hqt; linarith only [hΔ, hqt]
        refine ⟨hslot, ⟨q, ⟨ell', hc'.1, Or.inl ⟨e', hc'.2, rfl⟩⟩,
          (AC.ts_le_iff_le_slot sp (hr.time_nonneg q) m).mpr
            (by rw [← (AC.castAt_specU hr.toU hz hc').2.1, hslot]), ht⟩,
          Hd, hHv, hHvr, hFB.trans hBHv, ?_⟩
        rcases Compose.frame_anc_acceptedU hr.toU hz q ell' hc'.1 Hd hHd Hd .refl
            with hg | ⟨k, hk, ha⟩
        · exact Or.inl hg
        · exact Or.inr ⟨k, ha, (hr.time_mono hk).trans_lt ht⟩
      have hslot := (AC.castAt_specU hr.toU hy hcast).2.1
      have htime : sp.ts (m + 1 : Nat) ≤ tr.time i :=
        (AC.ts_le_iff_le_slot sp (hr.time_nonneg i) _).mpr (by rw [← hslot, hm])
      have hmt : sp.ts m + sp.Δ ≤ b := by
        simp only [AC.ACParams.ts] at htime ⊢; push_cast at htime; linarith only [hΔ, hib, htime]
      have hcut : cutZ sp.toParams g ≤ tr.time i := hts.trans
        (((AC.ts_le_iff sp).mpr (by clear * - hsm; omega)).trans htime)
      refine AC.next_vote_extends_before hac K hp.hP hp.hT hp.hsize hy hcast hm
        (fun z hz q hq e' he hslot => hprior z hz q hq e' he (by
            rcases hslot with h | h <;> (clear * - hsm h; omega)))
        (hp.half_committee (hts.trans ((AC.ts_le_iff sp).mpr (by clear * - hsm; omega))) hmt)
        ⟨hr.awake_of_call y hy i ell hcast.1, (AC.castAt_specU hr.toU hy hcast).2.2.1,
          fun v hv => (hone v hv).heads v rfl, fun v hv => (hone v hv).holds v rfl⟩
        (hp.faultBoundK_late (by clear * - hs1 hsm; omega) hcut hib)
        (hp.cs2 (by clear * - hs1 hsm; omega))
        (hp.sync.syncAC hp.run ((AC.le_gbar g).trans
          (hgs.trans ((AC.ts_le_iff sp).mpr (by clear * - hsm; omega))))) ?_
      rw [← hm]
      exact Or.inl hv

/-- A raw writer's target is frame-held at a later slot start once finalization is below it.
Old acceptances use Catch; fresh acceptances use Sync and the healthy restart bound. -/
theorem raw_writer_held_at_slot_start
    (hp : ResetPremises tr H K proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r s i u : Nat}
    {B C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (hwriter : AC.ResultAt tr.projAC x r s C CV ∨ AC.FastLockAt tr.projAC x r s C CV)
    (hBC : Anc (tr.HonestBlocks H) B C) (hs : AC.gbar g + 4 * sp.Δ ≤ sp.ts s)
    (hsu : s < u) {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hti : tr.time i = sp.ts u)
    (hFB : Anc (tr.HonestBlocks H) ell.frame.F B) : B ∈ ell.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hstep : sp.ts s + 4 * sp.Δ ≤ tr.time i := by
    rw [hti]
    have ht := (AC.ts_le_iff sp).mpr (show (s : Int) + 1 ≤ u by clear * - hsu; omega)
    simp only [AC.ACParams.ts] at ht ⊢
    linarith
  obtain ⟨v, _, D, hD, hDr, hBD, hg | ⟨q, hq, hqt⟩⟩ :=
    raw_writer_relay_source hp.committee_pos hr hp.run.vstart hx hwriter hBC
  all_goals obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hpH hci
  · obtain ⟨G, hG, hGr, hGp⟩ := AC.genesis_mem_of_callU sp hr.toU hpH _ _ hci
    have hDG : D = G := hr.coherent.1 hD hG (hg.trans hGr.symm)
    subst D
    have hGD : G ∈ ell.frame.tree := by
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp (hFB.trans hBD) with he | ⟨c, _, hpar⟩
      · exact he ▸ hPhi.rooted.1
      · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
    exact AC.frame_mem_of_between sp hr.coherent hPhi hPhiU hGD hBD hFB
  · have hFD := hFB.trans hBD
    have hDt : D ∈ ell.frame.tree := by
      by_cases hg : AC.gbar g ≤ tr.time q
      · have hdl : ∀ k ≤ i, tr.projAC.deadline p k (tr.time q) < sp.ts s + 3 * sp.Δ := by
          intro k hk
          have hd := Compose.ac_deadline_le_of_restarts
            (T := tr.projAC) (c := k)
            (fun k' _ hr' => restart_le hp hpH (Compose.projAC_restartAt.mp hr')) (tr.time q)
          have ht : max (tr.time q) (sp.ts (sp.slot (AC.gbar g) + 1 : Nat)) <
              sp.ts s + 2 * sp.Δ := by
            apply max_lt hqt
            linarith only [hs, hΔ, slotAfter_le (sp := sp) g]
          change _ ≤ max (tr.time q) (sp.ts (sp.slot (AC.gbar g) + 1 : Nat)) + sp.Δ at hd
          linarith only [ht, hd]
        obtain ⟨k, hki, hak, _⟩ := ((ResetService.of_gst tr H hp.healthy.1 (b := 0)).syncAC
          hp.run (hi := tr.time q) (AC.le_gbar g)).2 x hx q D hq hg le_rfl
          p hpH i ell hci (by
            have := hdl i le_rfl
            change tr.projAC.deadline p i (tr.time q) ≤ tr.time i
            linarith only [hstep, this, hΔ]) hFD
        exact AC.mem_tree_of_acceptAtU sp hr.toU hpH hak hki hci hFD
      · obtain ⟨k, hki, hak, _⟩ := projection_catch_of_run hp.run hc x hx q D hq (not_le.mp hg)
          p hpH i ell hci
          (by change _ ≤ tr.time i; linarith only [hs, hΔ, hstep]) hFD
        exact AC.mem_tree_of_acceptAtU sp hr.toU hpH hak hki hci hFD
    exact AC.frame_mem_of_between sp hr.coherent hPhi hPhiU hDt hBD hFB

/-- Guarded receipt of an actual acceptance: old sources use Catch, newer ones use Sync.
The receiver's finalization bound is required; archival heldness alone is not frame membership. -/
theorem reset_accept_frame
    (hp : ResetPremises tr H K proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {q j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (ha : tr.projAC.AcceptAt x q B)
    {ell : ACLabel (goldilocksNode sp ro)} (hcall : tr.projAC.CallAt y j ell)
    (hg : AC.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoin : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocks H) ell.frame.F B) : B ∈ ell.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  by_cases hnew : AC.gbar g ≤ tr.time q
  · have hd := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := j)
      (fun k _ hk => restart_le hp hy (Compose.projAC_restartAt.mp hk)) (tr.time q)
    have hdl : tr.projAC.deadline y j (tr.time q) ≤ tr.time j := by
      apply hd.trans
      change max (tr.time q) (sp.ts (sp.slot (AC.gbar g) + 1 : Nat)) + sp.Δ ≤ tr.time j
      rw [← max_add_add_right]
      exact max_le hq hjoin
    obtain ⟨k, hkj, hak, _⟩ := ((ResetService.of_gst tr H hp.healthy.1 (b := 0)).syncAC
      hp.run (hi := tr.time q) (AC.le_gbar g)).2 x hx q B ha hnew le_rfl
      y hy j ell hcall hdl hF
    exact AC.mem_tree_of_acceptAtU sp hr.toU hy hak hkj hcall hF
  · obtain ⟨k, hkj, hak, _⟩ := projection_catch_of_run hp.run hc x hx q B ha (not_le.mp hnew)
      y hy j ell hcall hg hF
    exact AC.mem_tree_of_acceptAtU sp hr.toU hy hak hkj hcall hF

/-- A frame-held block reaches a later frame only under that receiver's finalization guard. -/
theorem reset_frame_relay
    (hp : ResetPremises tr H K proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {q j : Nat}
    {ellx elly : ACLabel (goldilocksNode sp ro)}
    (hcx : tr.projAC.CallAt x q ellx) (hcy : tr.projAC.CallAt y j elly)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ellx.frame.tree)
    (hg : AC.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoin : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocks H) elly.frame.F B) : B ∈ elly.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  rcases Compose.frame_anc_acceptedU hr.toU hx q ellx hcx B hB B .refl with hgen | ⟨k, hk, ha⟩
  · obtain ⟨G, hGU, hGr, hGp⟩ := AC.genesis_mem_of_callU sp hr.toU hy j elly hcy
    obtain rfl : B = G := hr.coherent.1 ((AC.frameIn_of_callAt hr hx hcx).2 hB)
      hGU (hgen.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hF with he | ⟨c, _, hpar⟩
    · exact he ▸ (AC.frameIn_of_callAt hr hy hcy).1.rooted.1
    · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
  · exact reset_accept_frame hp hc hx hy ha hcy hg hjoin
      (by have := hp.run.time_mono hk; change tr.time k ≤ tr.time q at this; linarith) hF

end Consensus.Goldilocks.Healing

end
