module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGStore.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Inclusion
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: post-reset source and transport foundations

The objects of the post-reset argument (with HS.2)
after the reset `a = a_z`, stated over the run, for every consumer
(C1.2 here, H.3 (c)'s `Inv` half), not specialized to C1.2's entries.
With `b = slot(a) + 3` (`cleanLabel`) and `R = t_{b+2k+2}` (`drainTime`, the `R_z` of C1.2):

* **RN, stored ancestry is irreversible**: every lock stored at a later cut sits below a
  stored lock of its slot at an earlier cut, or below a fresh write between them
  (`stored_lock_below`, `SA.lock_provenance_from` on the AC projection). **RU** is
  `SA.unlock_compatible`: unlocking against a view with at least `n/2` validators whose slot-`s`
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
`ready_unanimous`, `ready_update_selection` and the report-cover suppliers; this separation lets
those suppliers use the pivot without an import cycle. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}

/-- The first clean evidence label `b = slot(a) + 3` after the reset `a`. -/
def cleanLabel (sp : SAParams) (a : Time) : Nat := sp.slot a + 3

/-- The drain time `R = t_{b+2k+2} = t_{slot(a)+2k+5}` (C1.2's `R_z`). -/
def drainTime (sp : SAParams) (a : Time) : Time := sp.ts (sp.slot a + 2 * sp.k + 5 : Nat)

theorem cleanLabel_eq (a : Time) : cleanLabel sp a = sp.slot a + 3 := by rfl

theorem drainTime_eq (a : Time) : drainTime sp a = sp.ts (sp.slot a + 2 * sp.k + 5 : Nat) := by
  rfl

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- **The drain** (HS.2 (3)): at a time `t ≥ R`, every live lock of an honest node has a
label at least `b + k + 2`; every lock of a label before `b`, and every slow lock whose window
straddles `b`, has expired. The locks are those of a run (`LocksWF`: every expiry is at most
`k` slots after the label), as every honest node's are (`SA.locksWF_state`). -/
theorem drain_live_locks {Φ : SA.Frm sp.n (List (FG.Att sp.n))} {L : Set SA.Lock} {t : Time}
    (hwf : SA.LocksWF sp L) (ht : drainTime sp a ≤ t) :
    ∀ l ∈ SA.liveLocks sp L Φ t, cleanLabel sp a + sp.k + 2 ≤ l.slot := by
  intro l hl
  have hk := hwf.slot_le_of_live hl
  have h0 : 0 ≤ t := le_trans (by
    rw [drainTime_eq]
    simp only [SAParams.ts]
    exact mul_nonneg (by linarith [sp.toParams.hΔ]) (Int.natCast_nonneg _)) ht
  rw [drainTime_eq] at ht
  have hs := (SA.ts_le_iff_le_slot sp h0 _).1 ht
  rw [cleanLabel_eq]
  omega

/-- A stored lock that is live by time after the drain has a clean label. This requires
neither normalized `liveLocks` membership nor a later `addLocks` call. -/
theorem drain_stored_lock_label {l : SA.Lock} {t : Time}
    (ht : drainTime sp a ≤ t) (hlive : sp.slot t ≤ l.slot + sp.k) :
    cleanLabel sp a + sp.k + 2 ≤ l.slot := by
  have h0 : 0 ≤ t := le_trans (by
    rw [drainTime_eq]
    simp only [SAParams.ts]
    exact mul_nonneg (by linarith [sp.toParams.hΔ]) (Int.natCast_nonneg _)) ht
  rw [drainTime_eq] at ht
  have hs := (SA.ts_le_iff_le_slot sp h0 _).1 ht
  rw [cleanLabel_eq]
  omega

/-! ### The clean fast transfer -/

/-- `f < n/2` under `Healthy(g)`. -/
private theorem faulty_lt_half (hp : ResetPremises tr H proposer dg g ΔF a) (x : Fin sp.n) :
    2 * Hᶜ.ncard < sp.n := by
  have := hp.healthy.2.2
  have := Fin.pos x
  have hn : sp.n = sp.toParams.n := rfl
  omega

/-- A fast lock of label `s` is written at or after `t_s` (the update of `s` runs at `t_s + 6Δ`,
an optimistic confirmation of `s` in slot `s`). -/
private theorem ts_le_of_fastLock (hp : ResetPremises tr H proposer dg g ΔF a) {x : Fin sp.n}
    {i s : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC x i s D CV) : sp.ts s ≤ tr.time i := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hΔ := sp.toParams.hΔ
  rcases hfl with ⟨ℓ, C, ⟨-, -, ht, -⟩, -⟩ | ⟨ℓ, A, -, hsl, -⟩
  · have ht' : tr.time i = sp.ts s + 6 * sp.Δ := ht
    rw [ht']
    linarith
  · have hsl' : sp.slot (tr.time i) = s := hsl
    exact (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) s).2 (by clear * - hsl; omega)

/-- **The reset seed**: a high origin `(O, l)` with `l ≤ slot(a)`. An honest
attestation of height `H_z + 1` is signed at `a` (`IsReset`); its source is below a high origin
written by the signer before the attestation (`high_row_source`), and a fast lock written by `a` has
a label `≤ slot(a)`. -/
private theorem reset_seed (hp : ResetPremises tr H proposer dg g ΔF a) :
    ∃ v r l O, HighOrigin tr H g v r l O ∧ l ≤ sp.slot a := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨⟨y, hy, k, att, hs, hh, rfl⟩, -⟩ := hp.reset
  obtain ⟨r, hrk, l, O, ho, -⟩ := high_row_source hp hy hs hh.ge
  obtain ⟨-, D, CV, -, hfl, -⟩ := highOrigin_mem hp ho
  have h₁ : sp.ts l ≤ tr.time k := (ts_le_of_fastLock hp hfl).trans (hr.time_mono hrk.le)
  exact ⟨y, r, l, O, ho, by exact_mod_cast (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) l).1 h₁⟩

/-- The reset supplies an actual bounded high-origin seed, not merely an eventual origin. -/
theorem ResetPremisesUpTo.reset_seed {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) :
    ∃ v r l O, HighOrigin tr H g v r l O ∧ tr.time r ≤ a ∧ l ≤ sp.slot a := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨⟨y, hy, k, att, hs, hh, hka⟩, -⟩ := hp.reset
  obtain ⟨r, hrk, l, O, ho, -⟩ := hp.high_row_source hy hs hh.ge
  obtain ⟨-, D, CV, -, hfl, -⟩ := hp.highOrigin_mem ho
  have htime : sp.ts l ≤ tr.time r := by
    have hΔ := sp.toParams.hΔ
    rcases hfl with ⟨ell, C, ⟨-, -, ht, -⟩, -⟩ | ⟨ell, A, -, hsl, -⟩
    · have ht' : tr.time r = sp.ts l + 6 * sp.Δ := ht
      rw [ht']; linarith only [hΔ]
    · exact (SA.ts_le_iff_le_slot sp (hr.time_nonneg r) l).mpr (by clear * - hsl; omega)
  have hra : tr.time r ≤ a := (hr.time_mono hrk.le).trans hka.le
  refine ⟨y, r, l, O, ho, hra, ?_⟩
  have ha0 : 0 ≤ a := hka ▸ hr.time_nonneg k
  exact_mod_cast (SA.ts_le_iff_le_slot sp ha0 l).mp (htime.trans hra)

/-! ### The clean slow transfer -/

/-- The existing node premises supply all four fields of the healthy AC projection. -/
theorem healthy_base_of_reset_catch (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) :
    SA.HealthyBase tr.projAC H (tr.HonestBlocks H) proposer g :=
  ⟨Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl,
    projection_driven hp.run hp.noColl hp.run.genesis_root_ok hp.healthy,
    projection_healthy hp.run hp.noColl hp.healthy,
    projection_catch hp.run hp.noColl hp.healthy hc, hp.stock⟩

/-- Finite service and Catch supply the AC base without any reset or snapshot premise. -/
theorem healthy_base_of_service_catch_before {b : Time}
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsync : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, SA.gbar g ≤ t → t ≤ b → tr.awake y t)
    (hfaults : 3 * Hᶜ.ncard ≤ sp.n - 1)
    (hc : CatchRun tr H g (2 * sp.Δ)) :
    SA.HealthyBaseUpTo tr.projAC H (tr.HonestBlocks H) proposer g b := by
  refine ⟨Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc,
    projection_driven_of_run hrun hnc hrun.genesis_root_ok, ?_,
    ⟨fun x hx i B ha hi y hy j ell hj ht _ hF =>
      projection_catch_of_run hrun hc x hx i B ha hi y hy j ell hj ht hF⟩,
    hawake, hfaults, hrun.stock⟩
  have h := hrun.toLocalRun
  constructor
  · intro x hx i m hsa hi y hy j ℓ hcj _ hdl
    have hsa' : tr.SendOrAdmitAt x i m := by
      obtain ⟨ℓ, hc, hm⟩ := hsa
      refine ⟨ℓ, Compose.projAC_callAt.1 hc, ?_⟩
      rwa [Compose.projAC_state h hx] at hm
    have he : max (tr.time i) g = tr.time i := max_eq_left ((SA.le_gbar g).trans hi)
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
    have hmax : max (tr.time i') g = tr.projAC.time (i' + 1) := by
      rw [show tr.projAC.time (i' + 1) = tr.time (i' + 1) from rfl, hti]
      exact max_eq_left ((SA.le_gbar g).trans hi)
    rw [Compose.projAC_deadline] at hdl
    obtain ⟨k, hk, hak, hkt⟩ := hsync.relay x hx i' B ha'
      (by rw [hti]; exact (SA.le_gbar g).trans hi) y hy j
      ⟨_, Compose.projAC_callAt.1 hcj⟩ (by rw [hmax]; exact hdl)
      (by rwa [Compose.frame_of_projAC hrun hy hcj] at hanc)
    obtain ⟨hak', htk, hnr⟩ := ac_block_after h hy hak
    have hkj : k < j := by
      rcases hk.lt_or_eq with hk | rfl
      · exact hk
      · exact absurd (hak.2.symm.trans (Compose.projAC_callAt.1 hcj).2) (by simp)
    refine ⟨k + 1, hkj, hak', ?_⟩
    have htk' : tr.projAC.time (k + 1) = tr.time k := htk
    rw [Compose.projAC_deadline, htk', ← hmax]
    simpa only [RunTrace.deadline, RunTrace.lastWake, hnr, ite_false] using hkt

/-- Finite reset health supplies the AC base without extending awake obligations
past the horizon. Synchrony and Catch retain their actual deadline semantics. -/
theorem healthy_base_of_reset_catch_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) :
    SA.HealthyBaseUpTo tr.projAC H (tr.HonestBlocks H) proposer g b :=
  healthy_base_of_service_catch_before hp.run hp.noColl hp.sync hp.awake hp.faults hc

/-- An actual result within the healthy horizon has an actual earlier honest supporter. -/
theorem ResetPremisesUpTo.result_supporter {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x : Fin sp.n} (hx : x ∈ H) {r s : Nat}
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocks H) B C)
    (hrb : tr.time r ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts s) :
    ∃ z ∈ H, ∃ q < r, ∃ e, SA.VoteAt tr.projAC z q e ∧ e.msg ∈ CV ∧
      e.msg.slot = s ∧ SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hS := healthy_base_of_reset_catch_before hp hc
  have hΔ := sp.toParams.hΔ
  obtain ⟨ell, hu, hconf, hCV⟩ := hres
  have ht : tr.time r = sp.ts s + 6 * sp.Δ := hu.2.2.1
  have hsb : sp.ts s + sp.Δ ≤ b := by linarith
  have hgs : SA.gbar g ≤ sp.ts s := by have := lt_cutZ sp g; linarith
  have hsl : sp.slot (sp.ts s + sp.Δ) = s :=
    SA.slot_of_mem sp s (by linarith) (by simp only [SAParams.ts]; push_cast; linarith)
  have hs3 : sp.slot (SA.gbar g) + 3 ≤ s := by
    have h := (SA.ts_le_iff sp).mp ((cutZ_eq sp g) ▸ hts)
    exact_mod_cast h
  have hready : ∀ y ∈ H, tr.awake y (sp.ts s + sp.Δ) ∧
      tr.JoinedAt y (sp.ts s + sp.Δ) := by
    intro y hy
    refine ⟨hp.awake y hy _ (by linarith only [hΔ, hgs]) hsb, fun k hk hkt => ?_⟩
    change 0 < sp.slot (sp.ts s + sp.Δ) ∧
      tr.time k ≤ sp.toParams.slotTime (sp.slot (sp.ts s + sp.Δ) - 1)
    rw [hsl, sp.slotTime_eq]
    exact ⟨by omega, (restart_le_before hp hy hk (hkt.trans hsb)).trans
      ((SA.ts_le_iff sp).mpr (by
        exact_mod_cast (show sp.slot (SA.gbar g) + 1 ≤ s - 1 by clear * - hs3; omega)))⟩
  have hf : 3 * Hᶜ.ncard < sp.n := by
    have := hp.faults
    have := Fin.pos x
    have hn : sp.n = sp.toParams.n := rfl
    omega
  have hparts := Compose.honest_participants_window_before hp.run hp.noColl
    (SA.serviceWindowBefore_of_sync hS.sync) hgs hx hu hrb hready hf
  exact SA.result_honest_supporter_of_participants sp hS.run hx ⟨ell, hu, hconf, hCV⟩
    hBC hparts.le

/-- Catch uses its actual source boundary `gbar g`, not the later high-origin cut. -/
theorem catch_window_of_reset_catch (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) (Q : Time) :
    CatchACWindowBefore tr.projAC H (tr.HonestBlocks H) (SA.gbar g) (2 * sp.Δ) Q :=
  ⟨fun x hx i B ha hi y hy j ell hj ht _ hF =>
    projection_catch hp.run hp.noColl hp.healthy hc x hx i B ha hi y hy j ell hj ht hF⟩

/-- The raw-target service window starts at the same boundary as Catch. -/
theorem reset_raw_sync_window_before (hp : ResetPremises tr H proposer dg g ΔF a) (Q : Time) :
    SyncACWindowBefore H (tr.HonestBlocks H) (SA.gbar g) Q tr.projAC := by
  have hs := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr proposer ΔF (SA.gbar g) Q hp.run.toLocalRun
    (syncRun_of_gst hp.healthy.1 (SA.le_gbar g))
  have hsource : ∀ y j (t : Time), t ≤ tr.projAC.deadline y j t := by
    intro y j t
    unfold ACTrace.deadline
    have hΔ : 0 < sp.Δ := sp.toParams.hΔ
    cases tr.projAC.lastWake y j with
    | bot => change t ≤ t + sp.Δ; linarith
    | coe w =>
      change t ≤ max t w + sp.Δ
      have := le_max_left t w
      linarith
  constructor
  · intro x hx i m hm hi y hy j ell hj hQ hd
    exact hs.1 x hx i m hm hi ((hsource y j _).trans hQ) y hy j ell hj hd
  · intro x hx i B hB hi y hy j ell hj hQ hd hF
    exact hs.2 x hx i B hB hi ((hsource y j _).trans hQ) y hy j ell hj hd hF

/-- Clean labels start after the high seed and leave the whole slow window after GST. -/
private theorem clean_source_timing (hp : ResetPremises tr H proposer dg g ΔF a)
    {s : Nat} (hs : cleanLabel sp a + sp.k + 2 ≤ s) :
    cutZ sp.toParams g ≤ sp.ts s ∧
      SA.gbar g + 4 * sp.Δ ≤ sp.ts ((s : Int) - sp.k + 1) := by
  obtain ⟨v, r, l, O, ho, hl⟩ := reset_seed hp
  have ht := cutZ_le_ts_of_highOrigin hp ho
  have hz := lt_cutZ sp g
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  rw [cleanLabel_eq] at hs
  constructor
  · exact ht.trans ((SA.ts_le_iff sp).mpr (by omega))
  · have hle : sp.ts ((l : Int) + 1) ≤ sp.ts ((s : Int) - sp.k + 1) :=
      (SA.ts_le_iff sp).mpr (by omega)
    have he : sp.ts ((l : Int) + 1) = sp.ts l + 4 * sp.Δ := SA.ts_succ l
    rw [he] at hle
    linarith

/-- Current raw-target keep/root/floor step. Actual source heldness and honest counted
support feed the domain reduction; earlier support is strictly cut-bounded. -/
private theorem clean_source_vote_domain_step
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    (Q : Time) {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H)
    {r s i : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (horig : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrQ : tr.time r ≤ Q)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y i ell e) (hsi : s < e.msg.slot) (hiQ : tr.time i ≤ Q)
    (hprior : ∀ z ∈ H, ∀ q < i, ∀ e', SA.VoteAt tr.projAC z q e' →
      s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    Compatible (tr.HonestBlocks H) ell.frame.fcRoot B ∧
      ((∃ W ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
        Anc (tr.HonestBlocks H) B W ∧ (tr.state y i).fg.IsViable W) ∨
        Anc (tr.HonestBlocks H) B ell.frame.fcRoot) := by
  rcases horig with hfast | hslow
  · obtain ⟨CV, hfast⟩ := hfast
    have hS := healthy_base_of_reset_catch hp hc
    have hr := hS.run.localRun
    have hf := faulty_lt_half hp x
    have hΔ : 0 < sp.Δ := sp.toParams.hΔ
    have hgs : SA.gbar g ≤ sp.ts s := by
      have := (clean_source_timing hp hs).1
      have := lt_cutZ sp g
      linarith
    have evidence : B ∈ (tr.state x r).fg.tree ∧
        ∃ z ∈ H, ∃ q e', SA.VoteAt tr.projAC z q e' ∧ e'.msg.slot = s ∧
          SA.VoteExtends (tr.HonestBlocks H) e'.msg B := by
      rcases hfast with ⟨ellX, C, ⟨hcall, -⟩, -, hD, -⟩ |
          ⟨ellX, A, hpt, hslot, hsel, -⟩
      · have hΦU := (SA.frameIn_of_callAt hr hx hcall).2
        refine ⟨frame_tree_subset hp hx hcall (SA.deepest_mem hD).1.1.1, ?_⟩
        have htest := (SA.deepest_mem hD).1.2.2
        unfold SA.FastTest SA.confirmationScore at htest
        dsimp only at htest
        rw [hp.stock] at htest
        have hlt := Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le hf htest)
        obtain ⟨z, ⟨-, v, ⟨hvp, -⟩, rfl, -, R, hR, hRr, hBR⟩, hz⟩ :=
          Set.exists_mem_notMem_of_ncard_lt_ncard hlt
        obtain ⟨q, _, e', hv, rfl⟩ := hS.run.honest.pool_vote x hx r s _ hvp (not_not.mp hz)
        exact ⟨_, not_not.mp hz, q, e', hv, SA.state_pool_slot sp hr hx r s _ hvp,
          R, hΦU hR, hRr, hBR.mono hΦU⟩
      · have hΦU := (SA.frameIn_of_callAt hr hx hpt.1).2
        unfold SA.optimisticSelect at hsel
        dsimp only at hsel
        split_ifs at hsel
        refine ⟨frame_tree_subset hp hx hpt.1 (SA.deepest_mem hsel).1.1, ?_⟩
        have h34 := (SA.deepest_mem hsel).1.2.1
        rw [hp.stock] at h34
        obtain ⟨z, ⟨v, hv, rfl, R, hR, hRr, hBR⟩, hz⟩ :=
          Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
            (t := SA.optimisticVoters sp A ellX.frame (sp.slot (tr.projAC.time r)) B) (by
                clear * - hf h34; omega)
        obtain ⟨hvs, q, _, e', he, rfl⟩ :=
          SA.optimisticPoint_pool_vote hS.run hx hpt hv (not_not.mp hz)
        exact ⟨_, not_not.mp hz, q, e', he, hvs.trans hslot,
          R, hΦU hR, hRr, hBR.mono hΦU⟩
    obtain ⟨hBx, z, hz, q, e', hv, hvs, hVB⟩ := evidence
    refine held_target_vote_domain_before hp hx hy hBx hcast ?_ ?_ ?_
    · intro hF
      exact raw_writer_voterBlockTree_window_before (by rw [hp.stock]; exact sp.toParams.hn)
        hr (reset_raw_sync_window_before hp Q)
        (catch_window_of_reset_catch hp hc Q) hx hy (Or.inr hfast) .refl hcast (by
            clear * - hsi; omega) hiQ
        (by
          have hm := (SA.ts_le_iff sp).mpr (show (s : Int) ≤ e.msg.slot - 1 by clear * - hsi; omega)
          linarith only [hΔ, hgs, hm]) hF
    · obtain ⟨v, r₀, m, S, hS, hm⟩ := reset_seed hp
      have hms : m < s := by rw [cleanLabel_eq] at hs; (clear * - hs hm; omega)
      exact ⟨v, r₀, m, S, hS, by clear * - hsi hms; omega,
        target_compatible_older_origin hp hS hz hv hvs hms hVB⟩
    · intro v r₀ m O hri ho
      rcases lt_trichotomy m s with hm | rfl | hm
      · exact target_compatible_older_origin hp ho hz hv hvs hm hVB
      · obtain ⟨CV', hst⟩ := ho.2.2.1
        obtain ⟨_, D, hfl, hOD⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
        rcases SA.fastLock_fastLock_compatible hS hx hfast ho.1 hfl hgs with h | h
        · exact SA.anc_total hr.coherent h hOD
        · exact Or.inr (hOD.trans h)
      · exact target_compatible_later_origin_before hp ho hri hm hprior
  have hS := healthy_base_of_reset_catch hp hc
  have hr := hS.run.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hts, hwindow⟩ := clean_source_timing hp hs
  have hgs4 : SA.gbar g + 4 * sp.Δ ≤ sp.ts s := by
    have := lt_cutZ sp g
    linarith only [hΔ, hts, this]
  have hgs : SA.gbar g ≤ sp.ts s := by linarith only [hgs4, hΔ]
  obtain ⟨ellX, C, hupd, hconf, hdeep⟩ := id hslow
  have hBC := ((SA.deepest_mem hdeep).1.1.2.2).mono (SA.frameIn_of_callAt hr hx hupd.1).2
  have hres : SA.ResultAt tr.projAC x r s C
      (SA.fastCounted sp (tr.projAC.state x r) ellX.frame s C) := ⟨ellX, hupd, hconf, rfl⟩
  have hslot : sp.slot (sp.ts s + sp.Δ) = s := SA.slot_of_mem sp s (by linarith only [hΔ])
    (by simp only [SA.SAParams.ts]; push_cast; linarith only [hΔ])
  have hprev : SA.gbar g ≤ sp.ts ((s : Int) - 1) := by
    have he : sp.ts ((s : Int) - 1) = sp.ts s - 4 * sp.Δ := SA.ts_sub_one sp s
    rw [he]; linarith only [hgs4]
  have hparts := Compose.honest_participants_window_before hp.run hp.noColl
    (SA.serviceWindowBefore_of_sync (reset_raw_sync_window_before hp Q)) hgs hx hupd hrQ
    (fun z hz => ⟨hp.healthy.2.1 z hz _ (by
        change SA.gbar g ≤ sp.ts s + sp.Δ; linarith only [hΔ, hgs4]),
      (Compose.joined_projection sp ro dg H tr proposer hp.run z hz _).1.mpr
        (hS.joinedAt hz (by rw [hslot]; exact hprev))⟩)
    (by have := hp.healthy.2.2; have := Fin.pos x
        have hn : sp.n = sp.toParams.n := rfl
        omega)
  obtain ⟨z, hz, q, _, e', hv, _, hvs, hVB⟩ :=
    SA.result_honest_supporter_of_participants sp hS.run hx hres hBC hparts.le
  have hjoined : SA.JoinedAt tr.projAC x (tr.time r) := by
    have ht : tr.time r = sp.ts s + 6 * sp.Δ := hupd.2.2.1
    have hsr : sp.slot (tr.time r) = s + 1 := by
      rw [ht]
      apply SA.slot_of_mem sp (s + 1) <;>
        simp only [SA.SAParams.ts] <;> push_cast <;> linarith only [hΔ]
    exact hS.joinedAt hx (by rw [hsr]; convert hgs using 1; congr 1; (clear * -; omega))
  refine slow_target_vote_domain_of_support_before hp hc Q hx hy hslow hjoined
    ((SA.ts_le_iff sp).mpr (by rw [cleanLabel_eq] at hs; (clear * - hs; omega))) hrQ
    hcast hsi hiQ ?_ ?_ ⟨z, hz, q, e', hv, hvs, hVB⟩ ?_ hprior
  · intro hF
    exact raw_writer_voterBlockTree_window_before (by rw [hp.stock]; exact sp.toParams.hn)
      hr (reset_raw_sync_window_before hp Q)
      (catch_window_of_reset_catch hp hc Q) hx hy (Or.inl hres) hBC hcast (by
          clear * - hsi; omega) hiQ
      (by
        have hm := (SA.ts_le_iff sp).mpr (show (s : Int) ≤ e.msg.slot - 1 by clear * - hsi; omega)
        linarith only [hΔ, hgs4, hm]) hF
  · obtain ⟨v, q, m, S, hS, hm⟩ := reset_seed hp
    exact ⟨v, q, m, S, hS, by rw [cleanLabel_eq] at hs; (clear * - hs hm; omega)⟩
  · intro v q O _ ho
    obtain ⟨CV, hst⟩ := ho.2.2.1
    obtain ⟨_, D, hfl, hOD⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
    have hCD : Compatible (tr.HonestBlocks H) C D := by
      rcases hfl with ⟨ellD, R, huD, hR, hfast, _⟩ | hop
      · have hDR := ((SA.deepest_mem hfast).1.1.2.2).mono
          (SA.frameIn_of_callAt hr ho.1 huD.1).2
        have hRR := SA.result_result_compatible hS hx hres ho.1 ⟨ellD, huD, hR, rfl⟩ hgs4
        rcases hRR with h | h
        · exact SA.anc_total hr.coherent h hDR
        · exact Or.inr (hDR.trans h)
      · exact SA.result_optimistic_compatible hS hx hres ho.1 hop hgs4
    rcases hCD with h | h
    · exact SA.anc_total hr.coherent (hBC.trans h) hOD
    · exact SA.anc_total hr.coherent hBC (hOD.trans h)

/-- Prospective clean-source support: strong induction is on the receiving cut, never
on the source gate. Current domain, transfer and service use only strictly earlier support. -/
theorem clean_source_votes_before
    (hp : ResetPremises tr H proposer dg g ΔF a) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (Q : Time) {x : Fin sp.n} (hx : x ∈ H) {r s : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (horig : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrQ : tr.time r ≤ Q) :
    ∀ i, tr.time i ≤ Q → ∀ y ∈ H, ∀ ell e, SA.CastAt tr.projAC y i ell e →
      s < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hS := healthy_base_of_reset_catch hp hcatch
  have hr := hS.run.localRun
  have hsync := reset_raw_sync_window_before hp Q
  have hcatch' := catch_window_of_reset_catch hp hcatch Q
  obtain ⟨hts, hwindow⟩ := clean_source_timing hp hs
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hgs : SA.gbar g ≤ sp.ts s := by have := lt_cutZ sp g; linarith
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hiQ y hy ell e hcast hsi
    have hprior : ∀ z ∈ H, ∀ q < i, ∀ e', SA.VoteAt tr.projAC z q e' →
        s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e'.msg B := by
      rintro z hz q hqi e' ⟨ell', hc'⟩ hse
      exact ih q hqi ((hp.run.time_mono hqi.le).trans hiQ) z hz ell' e' hc' hse
    obtain ⟨hroot, hkeep⟩ := clean_source_vote_domain_step hp hcatch Q hx hy horig hs hrQ
      hcast hsi hiQ hprior
    have hvi := vote_viable_of_root hp.run hp.noColl hy hcast hroot hkeep
    obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcast.1
    by_cases hBF : Anc (tr.HonestBlocks H) B ell.frame.fcRoot
    · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := Compose.cast_head_fcRoot hr hy hcast
      exact ⟨Hd, hΦU hHd, hHdr, hBF.trans (hfHd.mono hΦU)⟩
    have hv := hvi.resolve_right hBF
    have hFB := (hΦ.rooted.2 B hv.1.1).mono hΦU
    have htsRead : sp.ts e.msg.slot ≤ tr.time i :=
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).mpr
        (by rw [(SA.castAt_spec hr hy hcast).2.1])
    have hfault : SA.FaultBound tr.projAC H (tr.time i) := hS.faultBound (hr.time_nonneg i)
      (hgs.trans ((SA.ts_le_iff sp).mpr (by
        have hslot : e.msg.slot = sp.slot (tr.time i) := (SA.castAt_spec hr hy hcast).2.1
        omega)))
    have sync : ∀ m, s ≤ m → SyncAC (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)
        H (tr.HonestBlocks H) (sp.ts m) (tr.time i) tr.projAC := by
      intro m hm
      exact Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
        tr proposer ΔF (sp.ts m) (tr.time i) hp.run.toLocalRun
        (syncRun_of_gst hp.healthy.1 ((SA.le_gbar g).trans
          (hgs.trans ((SA.ts_le_iff sp).mpr (by clear * - hm; omega)))))
    by_cases hfirst : e.msg.slot = s + 1
    · have carry : ∀ CV, (∀ v ∈ CV, v.slot = s ∧
          (∃ k, tr.projAC.SendOrAdmit x k v ∧ sp.ts s ≤ tr.projAC.time k ∧
            tr.projAC.time k < sp.ts s + 2 * sp.Δ) ∧
          ∃ Hv ∈ tr.HonestBlocks H, Hv.root = v.head ∧ Anc (tr.HonestBlocks H) B Hv ∧
            (Hv.root = sp.genesisRoot ∨ ∃ k, tr.projAC.AcceptAt x k Hv ∧
              tr.projAC.time k < sp.ts s + 2 * sp.Δ)) →
          SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s CV := by
        intro CV hW
        apply Compose.carryAt_of_writer_window_before hr (SA.serviceWindowBefore_of_sync hsync)
          hgs hcatch' (by linarith only [sp.toParams.hΔ, hgs]) hx hy hcast hfirst hiQ
        intro v hv
        obtain ⟨hvs, hw, H, hH, hHr, hBH, ha⟩ := hW v hv
        exact ⟨hvs, hw, H, hH, hHr, hFB.trans hBH, ha⟩
      have earlier : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (s + 1) B :=
        fun z hz q hq e' he hslot => hprior z hz q hq e' he (by clear * - hslot; omega)
      have viab : SA.ViableAtVote ell e (s + 1) B := by rw [← hfirst]; exact Or.inl hv
      rcases horig with ⟨CV, hfast⟩ | hslow
      · exact SA.first_transfer_stored sp hS.run _ SA.CommitteeP.full SA.CommitteeT.full
          (SA.size_binding_full hp.stock) hx hfast .refl hy hcast hfirst
          (sync s le_rfl) (carry CV (fastLock_writer hr hx hfast))
          ((SA.faultBoundK_full_iff _ _).2 hfault) (SA.cs2_full_of_faultBound sp hp.stock hfault)
          viab earlier
      · obtain ⟨ellX, C, hupd, hconf, hdeep⟩ := id hslow
        have hBC := ((SA.deepest_mem hdeep).1.1.2.2).mono
          (SA.frameIn_of_callAt hr hx hupd.1).2
        have hres : SA.ResultAt tr.projAC x r s C
            (SA.fastCounted sp (tr.projAC.state x r) ellX.frame s C) :=
          ⟨ellX, hupd, hconf, rfl⟩
        refine SA.result_prefix_vote_extends_of_stored hS.run (faulty_lt_half hp x)
          hx hy hres hBC hcast hfirst (carry _ ?_) viab
          (SA.slow_stored_locks hS hx hslow hwindow hy (by
            rw [← (SA.castAt_spec hr hy hcast).2.1, hfirst])) earlier
          (SA.writer_merged_window_before hS.run (SA.serviceWindowBefore_of_sync hsync)
            hx hgs hupd hrQ hy hcast hfirst)
        intro v hv
        obtain ⟨hvs, hw, H, hH, hHr, hCH, ha⟩ := Compose.result_writer hr hx hres v hv
        exact ⟨hvs, hw, H, hH, hHr, hBC.trans hCH, ha⟩
    · obtain ⟨m, hm⟩ : ∃ m, e.msg.slot = m + 1 := ⟨e.msg.slot - 1, by omega⟩
      have hsm : s < m := by omega
      have hone : ∀ v ∈ Compose.honestVotes tr H m,
          SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e m {v} := by
        rintro v ⟨z, hz, q, e', ⟨ell', hc'⟩, rfl, hslot⟩
        have hqi : q < i := by
          by_contra hn
          have := SA.slot_mono sp (hr.time_nonneg i) (hr.time_mono (Nat.le_of_not_gt hn))
          have := (SA.castAt_spec hr hz hc').2.1
          have := (SA.castAt_spec hr hy hcast).2.1
          omega
        obtain ⟨Hv, hHv, hHvr, hBHv⟩ := hprior z hz q hqi e' ⟨ell', hc'⟩ (by
            clear * - hsm hslot; omega)
        obtain ⟨⟨Hd, hHd, hHdr, -⟩, hqt⟩ := Compose.cast_head_fcRoot hr hz hc'
        obtain rfl : Hd = Hv := hr.coherent.1 ((SA.frameIn_of_callAt hr hz hc'.1).2 hHd)
          hHv (hHdr.trans hHvr.symm)
        have hgm := hgs.trans ((SA.ts_le_iff sp).mpr (show (s : Int) ≤ m by clear * - hsm; omega))
        apply Compose.carryAt_of_writer_window_before hr (SA.serviceWindowBefore_of_sync hsync)
          hgm hcatch' (by linarith only [sp.toParams.hΔ, hgm]) hz hy hcast hm hiQ
        rintro v rfl
        have ht : tr.projAC.time q < sp.ts m + 2 * sp.Δ := by
          rw [hslot] at hqt
          linarith only [sp.toParams.hΔ, hqt]
        refine ⟨hslot, ⟨q, ⟨ell', hc'.1, Or.inl ⟨e', hc'.2, rfl⟩⟩,
          (SA.ts_le_iff_le_slot sp (hr.time_nonneg q) m).mpr
            (by rw [← (SA.castAt_spec hr hz hc').2.1, hslot]), ht⟩,
          Hd, hHv, hHvr, hFB.trans hBHv, ?_⟩
        rcases Compose.frame_anc_accepted hr hz q ell' hc'.1 Hd hHd Hd .refl with hg | ⟨k, hk, ha⟩
        · exact Or.inl hg
        · exact Or.inr ⟨k, ha, (hr.time_mono hk).trans_lt ht⟩
      refine SA.next_vote_extends_before hS.run hy hcast hm
        (fun z hz q hq e' he hslot => hprior z hz q hq e' he (by
            rcases hslot with h | h <;> (clear * - hsm h; omega)))
        (half_committee hp (hts.trans ((SA.ts_le_iff sp).mpr (by clear * - hsm; omega))))
        ⟨hr.awake_of_call y hy i ell hcast.1, (SA.castAt_spec hr hy hcast).2.2.1,
          fun v hv => (hone v hv).heads v rfl, fun v hv => (hone v hv).holds v rfl⟩
        hfault (sync m hsm.le) ?_ hp.stock
      rw [← hm]
      exact Or.inl hv

/-- A raw result prefix has a prospective frozen vote domain. Only support at strictly
earlier receiving cuts is assumed; the result writer need not precede the cast. -/
theorem result_prefix_vote_domain_before
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    (Q : Time) {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r s i : Nat}
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocks H) B C)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y i ell e) (hsi : s < e.msg.slot) (hiQ : tr.time i ≤ Q)
    (hprior : ∀ z ∈ H, ∀ q < i, ∀ e', SA.VoteAt tr.projAC z q e' →
      s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    Compatible (tr.HonestBlocks H) ell.frame.fcRoot B ∧
      ((∃ W ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
        Anc (tr.HonestBlocks H) B W ∧ (tr.state y i).fg.IsViable W) ∨
        Anc (tr.HonestBlocks H) B ell.frame.fcRoot) := by
  have hS := healthy_base_of_reset_catch hp hc
  have hr := hS.run.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hgs4 : SA.gbar g + 4 * sp.Δ ≤ sp.ts s := by
    have := (clean_source_timing hp hs).2
    exact this.trans ((SA.ts_le_iff sp).mpr (by have := sp.two_le_k; (clear * - this; omega)))
  obtain ⟨ellX, hupd, hconf, -⟩ := id hres
  have hCx := frame_tree_subset hp hx hupd.1 (SA.deepest_mem hconf).1.1
  have hBx := mem_tree_of_anc hp hx hBC hCx
  obtain ⟨z, hz, q, e', hv, hvs, D, hD, hDr, hCD⟩ :=
    SA.result_extended hS hgs4 hx hupd.1
      (by rw [hupd.2.2.1]; linarith only [hΔ]) hconf
  have hVB : SA.VoteExtends (tr.HonestBlocks H) e'.msg B :=
    ⟨D, hD, hDr, hBC.trans hCD⟩
  refine held_target_vote_domain_before hp hx hy hBx hcast ?_ ?_ ?_
  · intro hF
    exact raw_writer_voterBlockTree_window_before (by rw [hp.stock]; exact sp.toParams.hn)
      hr (reset_raw_sync_window_before hp Q)
      (catch_window_of_reset_catch hp hc Q) hx hy (Or.inl hres) hBC hcast (by
          clear * - hsi; omega) hiQ
      (by
        have := (SA.ts_le_iff sp).mpr (show (s : Int) ≤ e.msg.slot - 1 by clear * - hsi; omega)
        linarith only [hΔ, hgs4, this]) hF
  · obtain ⟨v, r₀, m, S, hseed, hm⟩ := reset_seed hp
    have hms : m < s := by rw [cleanLabel_eq] at hs; (clear * - hs hm; omega)
    exact ⟨v, r₀, m, S, hseed, by clear * - hsi hms; omega,
      target_compatible_older_origin hp hseed hz hv hvs hms hVB⟩
  · intro v r₀ m O hri ho
    rcases lt_trichotomy m s with hm | rfl | hm
    · exact target_compatible_older_origin hp ho hz hv hvs hm hVB
    · obtain ⟨CV', hst⟩ := ho.2.2.1
      obtain ⟨_, D, hfl, hOD⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
      have hcomp : Compatible (tr.HonestBlocks H) C D := by
        rcases hfl with ⟨ellD, R, huD, hR, hfast, _⟩ | hop
        · have hDR := ((SA.deepest_mem hfast).1.1.2.2).mono
            (SA.frameIn_of_callAt hr ho.1 huD.1).2
          rcases SA.result_result_compatible hS hx hres ho.1 ⟨ellD, huD, hR, rfl⟩ hgs4
            with h | h
          · exact SA.anc_total hr.coherent h hDR
          · exact Or.inr (hDR.trans h)
        · exact SA.result_optimistic_compatible hS hx hres ho.1 hop hgs4
      rcases hcomp with h | h
      · exact SA.anc_total hr.coherent (hBC.trans h) hOD
      · exact SA.anc_total hr.coherent hBC (hOD.trans h)
    · exact target_compatible_later_origin_before hp ho hri hm hprior

/-- Finite raw-prefix domain from actual bounded source and cast witnesses. -/
theorem ResetPremisesUpTo.result_prefix_vote_domain_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r s i : Nat}
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocks H) B C)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y i ell e) (hsi : s < e.msg.slot) (hib : tr.time i ≤ b)
    (hprior : ∀ z ∈ H, ∀ q < i, ∀ e', SA.VoteAt tr.projAC z q e' →
      s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    Anc (tr.HonestBlocks H) B ell.frame.fcRoot ∨
      B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  have hS := healthy_base_of_reset_catch_before hp hc
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  obtain ⟨v, d, m, S, hseed, hda, hm⟩ := hp.reset_seed
  have hdb := hda.trans hp.reset_le
  have hms : m < s := by rw [cleanLabel_eq] at hs; (clear * - hs hm; omega)
  have hts : cutZ sp.toParams g ≤ sp.ts s :=
    (hp.cutZ_le_ts_of_highOrigin hseed).trans ((SA.ts_le_iff sp).mpr (by clear * - hms; omega))
  have hgs : SA.gbar g ≤ sp.ts s := by have := lt_cutZ sp g; linarith only [hΔ, hts, this]
  obtain ⟨z, hz, q, hqr, ev, hv, _, hvs, hVB⟩ :=
    hp.result_supporter hc hx hres hBC hrb hts
  have hqb := (hp.run.time_mono hqr.le).trans hrb
  obtain ⟨ellX, hupd, hconf, -⟩ := hres
  have hCx := hp.frame_tree_subset hx hupd.1 (SA.deepest_mem hconf).1.1
  have hBx := hp.mem_tree_of_anc hx hBC hCx
  have hreset : ∀ w ∈ H, ∀ c, tr.time c ≤ b → tr.projAC.RestartAt w c →
      tr.time c ≤ sp.ts s := by
    intro w hw c hcb hrestart
    apply (restart_le_before hp hw (Compose.projAC_restartAt.mp hrestart) hcb).trans
    have hh := (SA.ts_le_iff sp).mp ((cutZ_eq sp g) ▸ hts)
    exact (SA.ts_le_iff sp).mpr (by clear * - hh; omega)
  apply hp.held_target_vote_domain_before hx hy hBx hcast ?_ hseed (by clear * - hsi hms; omega)
    (hp.target_compatible_older_origin hseed hdb hz hv hqb hvs hms hVB) ?_ ?_ ?_
  · intro hF
    exact raw_writer_voterBlockTree_window_before (by rw [hp.stock]; exact sp.toParams.hn)
      hr hS.sync hS.catchUp hx hy
      (Or.inl ⟨ellX, hupd, hconf, rfl⟩) hBC hcast (by clear * - hsi; omega) hib
      (by
        have := (SA.ts_le_iff sp).mpr (show (s : Int) ≤ e.msg.slot - 1 by clear * - hsi; omega)
        linarith only [hΔ, hgs, this]) hF
  · intro w c n O hci ho
    have hcb := (hp.run.time_mono hci.le).trans hib
    rcases lt_trichotomy n s with hn | rfl | hn
    · exact hp.target_compatible_older_origin ho hcb hz hv hqb hvs hn hVB
    · obtain ⟨CV', hst⟩ := ho.2.2.1
      obtain ⟨_, D, hfl, hOD⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
      have hcomp : Compatible (tr.HonestBlocks H) C D := by
        rcases hfl with ⟨ellD, R, huD, hR, hfast, _⟩ | hop
        · have hDR := ((SA.deepest_mem hfast).1.1.2.2).mono
            (SA.frameIn_of_callAt hr ho.1 huD.1).2
          have hRR := SA.result_result_compatible_window_before hS.run hS.sync hgs
            hx ho.1 ⟨ellX, hupd, hconf, rfl⟩ ⟨ellD, huD, hR, rfl⟩ hrb hcb
            (fun w hw c' hle hrest => hreset w hw c'
              ((hp.run.time_mono hle).trans (by
                rcases le_total r c with h | h
                · simpa only [max_eq_right h] using hcb
                · simpa only [max_eq_left h] using hrb)) hrest)
          rcases hRR with h | h
          · exact SA.anc_total hr.coherent h hDR
          · exact Or.inr (hDR.trans h)
        · exact SA.result_optimistic_compatible_window_before hS.run hS.sync hgs
            hx ho.1 ⟨ellX, hupd, hconf, rfl⟩ hop hrb hcb
            (fun c' hle hrest => hreset x hx c' ((hp.run.time_mono hle).trans hrb) hrest)
      rcases hcomp with h | h
      · exact SA.anc_total hr.coherent (hBC.trans h) hOD
      · exact SA.anc_total hr.coherent hBC (hOD.trans h)
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
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x : Fin sp.n} (hx : x ∈ H) {r s : Nat}
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocks H) B C)
    (hrb : tr.time r ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts s)
    (hdomain : ∀ y ∈ H, ∀ i ell e, SA.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → s < e.msg.slot →
      (∀ z ∈ H, ∀ q < i, ∀ e', SA.VoteAt tr.projAC z q e' →
        s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e'.msg B) →
      Anc (tr.HonestBlocks H) B ell.frame.fcRoot ∨
        B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
    (hstored : ∀ y ∈ H, ∀ i ell e, SA.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → e.msg.slot = s + 1 → ∀ l ∈ (tr.projAC.state y i).locks,
        sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
        ∀ Y ∈ tr.HonestBlocks H, Y.root = l.block → Compatible (tr.HonestBlocks H) Y B) :
    ∀ i, tr.time i ≤ b → ∀ y ∈ H, ∀ ell e, SA.CastAt tr.projAC y i ell e →
      s < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hS := healthy_base_of_reset_catch_before hp hc
  have hr := hS.run.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hgs : SA.gbar g ≤ sp.ts s := by have := lt_cutZ sp g; linarith
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have := hp.faults
    have := Fin.pos x
    have hn : sp.n = sp.toParams.n := rfl
    omega
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hib y hy ell e hcast hsi
    have hprior : ∀ z ∈ H, ∀ q < i, ∀ e', SA.VoteAt tr.projAC z q e' →
        s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e'.msg B := by
      rintro z hz q hqi e' ⟨ell', hc'⟩ hse
      exact ih q hqi ((hp.run.time_mono hqi.le).trans hib) z hz ell' e' hc' hse
    obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcast.1
    rcases hdomain y hy i ell e hcast hib hsi hprior with hBF | hv
    · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := Compose.cast_head_fcRoot hr hy hcast
      exact ⟨Hd, hΦU hHd, hHdr, hBF.trans (hfHd.mono hΦU)⟩
    have hFB := (hΦ.rooted.2 B hv.1.1).mono hΦU
    by_cases hfirst : e.msg.slot = s + 1
    · have carry : SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s CV := by
        apply Compose.carryAt_of_writer_window_before hr (SA.serviceWindowBefore_of_sync hS.sync)
          hgs hS.catchUp (by linarith only [hΔ, hgs]) hx hy hcast hfirst hib
        intro v hv
        obtain ⟨hvs, hw, D, hD, hDr, hCD, ha⟩ := Compose.result_writer hr hx hres v hv
        exact ⟨hvs, hw, D, hD, hDr, hFB.trans (hBC.trans hCD), ha⟩
      refine SA.result_prefix_vote_extends_of_stored hS.run hf hx hy hres hBC hcast
        hfirst carry ?_ (hstored y hy i ell e hcast hib hfirst)
        (fun z hz q hq e' he hslot => hprior z hz q hq e' he (by clear * - hslot; omega)) ?_
      · rw [← hfirst]; exact Or.inl hv
      · obtain ⟨ellX, hupd, -⟩ := hres
        exact SA.writer_merged_window_before hS.run (SA.serviceWindowBefore_of_sync hS.sync)
          hx hgs hupd hrb hy hcast hfirst
    · obtain ⟨m, hm⟩ : ∃ m, e.msg.slot = m + 1 := ⟨e.msg.slot - 1, by omega⟩
      have hsm : s < m := by omega
      have hone : ∀ v ∈ Compose.honestVotes tr H m,
          SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e m {v} := by
        rintro v ⟨z, hz, q, e', ⟨ell', hc'⟩, rfl, hslot⟩
        have hqi : q < i := by
          by_contra hn
          have := SA.slot_mono sp (hr.time_nonneg i) (hr.time_mono (Nat.le_of_not_gt hn))
          have := (SA.castAt_spec hr hz hc').2.1
          have := (SA.castAt_spec hr hy hcast).2.1
          omega
        obtain ⟨Hv, hHv, hHvr, hBHv⟩ := hprior z hz q hqi e' ⟨ell', hc'⟩ (by
            clear * - hsm hslot; omega)
        obtain ⟨⟨Hd, hHd, hHdr, -⟩, hqt⟩ := Compose.cast_head_fcRoot hr hz hc'
        obtain rfl : Hd = Hv := hr.coherent.1 ((SA.frameIn_of_callAt hr hz hc'.1).2 hHd)
          hHv (hHdr.trans hHvr.symm)
        have hgm := hgs.trans ((SA.ts_le_iff sp).mpr (show (s : Int) ≤ m by clear * - hsm; omega))
        apply Compose.carryAt_of_writer_window_before hr (SA.serviceWindowBefore_of_sync hS.sync)
          hgm hS.catchUp (by linarith only [hΔ, hgm]) hz hy hcast hm hib
        rintro v rfl
        have ht : tr.projAC.time q < sp.ts m + 2 * sp.Δ := by
          rw [hslot] at hqt; linarith only [hΔ, hqt]
        refine ⟨hslot, ⟨q, ⟨ell', hc'.1, Or.inl ⟨e', hc'.2, rfl⟩⟩,
          (SA.ts_le_iff_le_slot sp (hr.time_nonneg q) m).mpr
            (by rw [← (SA.castAt_spec hr hz hc').2.1, hslot]), ht⟩,
          Hd, hHv, hHvr, hFB.trans hBHv, ?_⟩
        rcases Compose.frame_anc_accepted hr hz q ell' hc'.1 Hd hHd Hd .refl with hg | ⟨k, hk, ha⟩
        · exact Or.inl hg
        · exact Or.inr ⟨k, ha, (hr.time_mono hk).trans_lt ht⟩
      have hslot := (SA.castAt_spec hr hy hcast).2.1
      have htime : sp.ts (m + 1 : Nat) ≤ tr.time i :=
        (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).mpr (by rw [← hslot, hm])
      have hmt : sp.ts m + sp.Δ ≤ b := by
        simp only [SA.SAParams.ts] at htime ⊢; push_cast at htime; linarith only [hΔ, hib, htime]
      have hcut : cutZ sp.toParams g ≤ tr.time i := hts.trans
        (((SA.ts_le_iff sp).mpr (by clear * - hsm; omega)).trans htime)
      have hfault : SA.FaultBound tr.projAC H (tr.time i) := by
        have h := fault_bound_late_before hp hcut hib
        unfold RunTrace.FaultBound RunTrace.honestAwakeJoined at h
        unfold SA.FaultBound SA.honestAwakeJoined
        convert h using 1
        congr 1
        ext z
        exact and_congr_right fun hz => and_congr_right fun _ =>
          (Compose.joined_projection sp ro dg H tr proposer hp.run z hz (tr.time i)).1.symm
      refine SA.next_vote_extends_before hS.run hy hcast hm
        (fun z hz q hq e' he hslot => hprior z hz q hq e' he (by
            rcases hslot with h | h <;> (clear * - hsm h; omega)))
        (hp.half_committee (hts.trans ((SA.ts_le_iff sp).mpr (by clear * - hsm; omega))) hmt)
        ⟨hr.awake_of_call y hy i ell hcast.1, (SA.castAt_spec hr hy hcast).2.2.1,
          fun v hv => (hone v hv).heads v rfl, fun v hv => (hone v hv).holds v rfl⟩
        hfault
        (hp.sync.syncAC hp.run ((SA.le_gbar g).trans
          (hgs.trans ((SA.ts_le_iff sp).mpr (by clear * - hsm; omega))))) ?_ hp.stock
      rw [← hm]
      exact Or.inl hv

/-- Restrict the finite result induction to one later view label, including every
vote at that clock. The actual raw witness need not be the record's last setter. -/
theorem ResetPremisesUpTo.latest_votes_of_recent_result {b t : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x : Fin sp.n} (hx : x ∈ H) {r s L : Nat}
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocks H) B C)
    (hrb : tr.time r ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts s)
    (hdomain : ∀ y ∈ H, ∀ i ell e, SA.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → s < e.msg.slot →
      (∀ z ∈ H, ∀ q < i, ∀ e', SA.VoteAt tr.projAC z q e' →
        s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e'.msg B) →
      Anc (tr.HonestBlocks H) B ell.frame.fcRoot ∨
        B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
    (hstored : ∀ y ∈ H, ∀ i ell e, SA.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → e.msg.slot = s + 1 → ∀ l ∈ (tr.projAC.state y i).locks,
        sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
        ∀ Y ∈ tr.HonestBlocks H, Y.root = l.block → Compatible (tr.HonestBlocks H) Y B)
    (htb : t ≤ b) (hsL : s < L) :
    ∀ z ∈ H, ∀ q, tr.time q ≤ t → ∀ e, SA.VoteAt tr.projAC z q e →
      e.msg.slot = L → SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  rintro z hz q hqt e ⟨ell, hcast⟩ he
  exact hp.late_result_prefix_votes_before hc hx hres hBC hrb hts hdomain hstored
    q (hqt.trans htb) z hz ell e hcast (he ▸ hsL)

/-- A clean raw source and any high origin share a later honest vote head. This uses
the already proved clean-source transfer, rather than assuming support at a source gate. -/
theorem clean_source_compatible_high_origin
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} (hx : x ∈ H) {r s : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsource : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s)
    {v : Fin sp.n} {q m : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g v q m O) : Compatible (tr.HonestBlocks H) B O := by
  have hS := healthy_base_of_reset_catch hp hc
  have hr := hS.run.localRun
  let n := max s m + 1
  have htime : SA.gbar g + 4 * sp.Δ ≤ sp.ts n := by
    have ht := (clean_source_timing hp hs).2
    exact ht.trans ((SA.ts_le_iff sp).mpr (by dsimp [n]; (clear * -; omega)))
  obtain ⟨j, e, hv, hes⟩ := SA.honest_votes_in_slot hS htime x hx
  obtain ⟨ell, hcast⟩ := hv
  have hB := clean_source_votes_before hp hc (max (tr.time r) (tr.time j)) hx hsource hs
    (le_max_left _ _) j (le_max_right _ _) x hx ell e hcast (by
        dsimp [n] at hes; (clear * - hes; omega))
  exact target_compatible_older_origin hp ho hx ⟨ell, hcast⟩ hes
    (by dsimp [n]; (clear * -; omega)) hB

/-- A raw writer's target is frame-held at a later slot start once finalization is below it.
Old acceptances use Catch; fresh acceptances use Sync and the healthy restart bound. -/
theorem raw_writer_held_at_slot_start
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r s i u : Nat}
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hwriter : SA.ResultAt tr.projAC x r s C CV ∨ SA.FastLockAt tr.projAC x r s C CV)
    (hBC : Anc (tr.HonestBlocks H) B C) (hs : SA.gbar g + 4 * sp.Δ ≤ sp.ts s)
    (hsu : s < u) {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hti : tr.time i = sp.ts u)
    (hFB : Anc (tr.HonestBlocks H) ell.frame.F B) : B ∈ ell.frame.tree := by
  have hS := healthy_base_of_reset_catch hp hc
  have hr := hS.run.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hstep : sp.ts s + 4 * sp.Δ ≤ tr.time i := by
    rw [hti]
    have ht := (SA.ts_le_iff sp).mpr (show (s : Int) + 1 ≤ u by clear * - hsu; omega)
    simp only [SA.SAParams.ts] at ht ⊢
    linarith
  obtain ⟨v, _, D, hD, hDr, hBD, hg | ⟨q, hq, hqt⟩⟩ :=
    raw_writer_relay_source (by rw [hp.stock]; exact sp.toParams.hn) hr hx hwriter hBC
  all_goals obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  · obtain ⟨G, hG, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hpH _ _ hci
    have hDG : D = G := hr.coherent.1 hD hG (hg.trans hGr.symm)
    subst D
    have hGD : G ∈ ell.frame.tree := by
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp (hFB.trans hBD) with he | ⟨c, _, hpar⟩
      · exact he ▸ hPhi.rooted.1
      · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
    exact SA.frame_mem_of_between sp hr.coherent hPhi hPhiU hGD hBD hFB
  · have hFD := hFB.trans hBD
    have hDt : D ∈ ell.frame.tree := by
      by_cases hg : SA.gbar g ≤ tr.time q
      · have hdl : ∀ k ≤ i, tr.projAC.deadline p k (tr.time q) < sp.ts s + 3 * sp.Δ := by
          intro k hk
          have hd := Compose.ac_deadline_le_of_restarts
            (T := tr.projAC) (c := k) (fun k' _ hr' => hS.restart_le hpH hr') (tr.time q)
          have ht : max (tr.time q) (SA.gbar g) < sp.ts s + 2 * sp.Δ := by
            apply max_lt hqt
            linarith only [hs, hΔ]
          change _ ≤ max (tr.time q) (SA.gbar g) + sp.Δ at hd
          linarith only [ht, hd]
        obtain ⟨k, hki, hak, _⟩ := (hS.syncAC le_rfl (tr.time q)).2 x hx q D hq hg le_rfl
          p hpH i ell hci (by
            have := hdl i le_rfl
            change tr.projAC.deadline p i (tr.time q) ≤ tr.time i
            linarith only [hstep, this, hΔ]) hFD
        exact SA.mem_tree_of_acceptAt sp hr hpH hak hki hci hFD
      · obtain ⟨k, hki, hak, _⟩ := hS.catchUp x hx q D hq (not_le.mp hg) p hpH i ell hci
          (by change _ ≤ tr.time i; linarith only [hs, hΔ, hstep]) hFD
        exact SA.mem_tree_of_acceptAt sp hr hpH hak hki hci hFD
    exact SA.frame_mem_of_between sp hr.coherent hPhi hPhiU hDt hBD hFB

/-- Guarded receipt of an actual acceptance: old sources use Catch, newer ones use Sync.
The receiver's finalization bound is required; archival heldness alone is not frame membership. -/
theorem reset_accept_frame
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {q j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ha : tr.projAC.AcceptAt x q B)
    {ell : ACLabel (goldilocksNode sp ro)} (hcall : tr.projAC.CallAt y j ell)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocks H) ell.frame.F B) : B ∈ ell.frame.tree := by
  have hS := healthy_base_of_reset_catch hp hc
  have hr := hS.run.localRun
  by_cases hnew : SA.gbar g ≤ tr.time q
  · have hd := Compose.ac_deadline_le_of_restarts
      (T := tr.projAC) (c := j) (fun k _ hk => hS.restart_le hy hk) (tr.time q)
    have hdl : tr.projAC.deadline y j (tr.time q) ≤ tr.time j := by
      change _ ≤ max (tr.time q) (SA.gbar g) + sp.Δ at hd
      rw [max_eq_left hnew] at hd
      exact hd.trans hq
    obtain ⟨k, hkj, hak, _⟩ := (hS.syncAC le_rfl (tr.time q)).2 x hx q B ha hnew le_rfl
      y hy j ell hcall hdl hF
    exact SA.mem_tree_of_acceptAt sp hr hy hak hkj hcall hF
  · obtain ⟨k, hkj, hak, _⟩ := hS.catchUp x hx q B ha (not_le.mp hnew)
      y hy j ell hcall hg hF
    exact SA.mem_tree_of_acceptAt sp hr hy hak hkj hcall hF

/-- A frame-held block reaches a later frame only under that receiver's finalization guard. -/
theorem reset_frame_relay
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {q j : Nat}
    {ellx elly : ACLabel (goldilocksNode sp ro)}
    (hcx : tr.projAC.CallAt x q ellx) (hcy : tr.projAC.CallAt y j elly)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ellx.frame.tree)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocks H) elly.frame.F B) : B ∈ elly.frame.tree := by
  have hr := (healthy_base_of_reset_catch hp hc).run.localRun
  rcases Compose.frame_anc_accepted hr hx q ellx hcx B hB B .refl with hgen | ⟨k, hk, ha⟩
  · obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hy j elly hcy
    obtain rfl : B = G := hr.coherent.1 ((SA.frameIn_of_callAt hr hx hcx).2 hB)
      hGU (hgen.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hF with he | ⟨c, _, hpar⟩
    · exact he ▸ (SA.frameIn_of_callAt hr hy hcy).1.rooted.1
    · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
  · exact reset_accept_frame hp hc hx hy ha hcy hg
      (by have := hp.run.time_mono hk; change tr.time k ≤ tr.time q at this; linarith) hF

end Consensus.Goldilocks.Healing

end
