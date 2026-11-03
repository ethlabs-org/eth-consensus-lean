module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Inclusion

public section

/-! # Goldilocks Healing: post-reset source and transport foundations

The objects of fradamt-agent/workbench `producer-reset-continuation.md` §22–§23 and
`phase-service.md` §10 (HS.2) after the reset `a = a_z`, stated over the run, for every consumer
(C1.2 here, H.3 (c)'s `Inv` half through workbench#21), not specialized to C1.2's entries.
With `b = slot(a) + 3` (`cleanLabel`) and `R = t_{b+2k+2}` (`drainTime`, the `R_z` of C1.2):

* **RN, stored ancestry is irreversible** (§22): every lock stored at a later cut sits below a
  stored lock of its slot at an earlier cut, or below a fresh write between them
  (`stored_lock_below`, `SA.lock_provenance_from` on the AC projection). **RU** (§22) is
  `SA.unlock_compatible`: unlocking against a view with at least `n/2` validators whose slot-`s`
  support votes extend `B`, or that equivocate, moves every lock of a slot below `s` to a block
  compatible with `B`.
* **The drain** (§23, HS.2 (3)): from `R` on, every live lock has a label at least `b + k + 2`, so
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

/-- **The drain** (§23, HS.2 (3)): at a time `t ≥ R`, every live lock of an honest node has a
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
    exact (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) s).2 (by omega)

/-- **The reset seed** (workbench#29 §9): a high origin `(O, l)` with `l ≤ slot(a)`. An honest
row of height `H_z + 1` is signed at `a` (`IsReset`); its source is below a high origin written
by the signer before the row (`high_row_source`), and a fast lock written by `a` has a label
`≤ slot(a)`. -/
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
      rw [ht']; linarith
    · exact (SA.ts_le_iff_le_slot sp (hr.time_nonneg r) l).mpr (by omega)
  have hra : tr.time r ≤ a := (hr.time_mono hrk.le).trans hka.le
  refine ⟨y, r, l, O, ho, hra, ?_⟩
  have ha0 : 0 ≤ a := hka ▸ hr.time_nonneg k
  exact_mod_cast (SA.ts_le_iff_le_slot sp ha0 l).mp (htime.trans hra)

/-! ### The clean slow transfer -/

/-- A deepest block of a set is the one `deepest` returns. -/
private theorem deepest_eq_of_isDeepest {Φ : SA.Frm sp.n (List (FG.Att sp.n))}
    {S : Set (SA.Blk sp.n (List (FG.Att sp.n)))} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : SA.IsDeepest Φ S D) : SA.deepest Φ S = some D := by
  have hex : ∃ B, SA.IsDeepest Φ S B := ⟨D, h⟩
  cases hd : SA.deepest Φ S with
  | none =>
    unfold SA.deepest at hd
    simp only [hex, ↓reduceDIte, reduceCtorEq] at hd
  | some D' =>
    have h' := SA.deepest_mem hd
    by_contra hne
    have hne' : D' ≠ D := fun h => hne (congrArg some h)
    rcases h.2 D' h'.1 hne' with h₁ | ⟨h₁, h₂⟩ <;>
      rcases h'.2 D h.1 (Ne.symm hne') with h₃ | ⟨h₃, h₄⟩ <;> omega

/-- An honest validator is not an equivocator in an honest node's pool of a slot. -/
private theorem honest_not_equivocator_pool (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n}
    (hy : y ∈ H) (c s : Nat) {u : Fin sp.n} (hu : u ∈ H) :
    u ∉ SA.equivocators {v | v ∈ (tr.projAC.state y c).pool s} := by
  have hrun := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hrun.localRun
  rintro ⟨v, hv, w, hw, hvw, rfl, hwv⟩
  obtain ⟨jv, -, ev, hev, rfl⟩ := hrun.honest.pool_vote y hy c s _ hv hu
  obtain ⟨jw, -, ew, hew, rfl⟩ := hrun.honest.pool_vote y hy c s _ hw (hwv ▸ hu)
  rw [hwv] at hew
  obtain ⟨-, rfl⟩ := (SA.one_vote_per_slot sp) _ ro H _ _ hr _ hu jv jw ev ew hev hew
    ((SA.state_pool_slot sp hr hy c s _ hv).trans (SA.state_pool_slot sp hr hy c s _ hw).symm)
  exact hvw rfl

/-- The existing node premises supply all four fields of the healthy AC projection. -/
theorem healthy_base_of_reset_catch (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) :
    SA.HealthyBase tr.projAC H (tr.HonestBlocks H) proposer g :=
  ⟨Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl,
    projection_driven hp.run hp.noColl hp.run.genesis_root_ok hp.healthy,
    projection_healthy hp.run hp.noColl hp.healthy,
    projection_catch hp.run hp.noColl hp.healthy hc⟩

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
    hawake, hfaults⟩
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
    refine ⟨hp.awake y hy _ (by linarith) hsb, fun k hk hkt => ?_⟩
    change 0 < sp.slot (sp.ts s + sp.Δ) ∧
      tr.time k ≤ sp.toParams.slotTime (sp.slot (sp.ts s + sp.Δ) - 1)
    rw [hsl, sp.slotTime_eq]
    exact ⟨by omega, (restart_le_before hp hy hk (hkt.trans hsb)).trans
      ((SA.ts_le_iff sp).mpr (by
        exact_mod_cast (show sp.slot (SA.gbar g) + 1 ≤ s - 1 by omega)))⟩
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
    have he : sp.ts ((l : Int) + 1) = sp.ts l + 4 * sp.Δ := by
      simp only [SA.SAParams.ts]; ring
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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- At the first slot after a late raw result, every still-live older stored lock is
compatible with each prefix of that result. The late bound drains pre-clean sources. -/
theorem result_prefix_stored_locks
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r s i : Nat}
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocks H) B C)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s)
    (hi : s + 1 ≤ sp.slot (tr.time i)) :
    ∀ l ∈ (tr.projAC.state y i).locks,
      sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
      ∀ Y ∈ tr.HonestBlocks H, Y.root = l.block → Compatible (tr.HonestBlocks H) Y B := by
  have hS := healthy_base_of_reset_catch hp hc
  have hr := hS.run.localRun
  have hgs4 : SA.gbar g + 4 * sp.Δ ≤ sp.ts s := by
    have ht := (clean_source_timing hp (show cleanLabel sp a + sp.k + 2 ≤ s by
      have := sp.two_le_k; omega)).2
    exact ht.trans ((SA.ts_le_iff sp).mpr (by have := sp.two_le_k; omega))
  have down : ∀ {L D}, Anc (tr.HonestBlocks H) L D →
      Compatible (tr.HonestBlocks H) C D → Compatible (tr.HonestBlocks H) L B := by
    intro L D hLD hCD
    rcases hCD with h | h
    · exact SA.anc_total hr.coherent hLD (hBC.trans h)
    · exact SA.anc_total hr.coherent (hLD.trans h) hBC
  intro l hl hlive hle Y hY hYr
  rcases hle.lt_or_eq with hls | hls
  · have hclean : cleanLabel sp a + sp.k + 2 ≤ l.slot := by omega
    have compare : ∀ {q D},
        ((∃ CV, SA.FastLockAt tr.projAC y q l.slot D CV) ∨
          SA.SlowLockAt tr.projAC y q l.slot D) → Compatible (tr.HonestBlocks H) C D := by
      intro q D hsource
      obtain ⟨ell, hu, hC, -⟩ := hres
      obtain ⟨z, hz, j, e, hv, hes, Hd, hHd, he, hCH⟩ :=
        SA.result_extended hS hgs4 hx hu.1 (by rw [hu.2.2.1]; linarith [sp.toParams.hΔ]) hC
      obtain ⟨ell', hcast⟩ := hv
      obtain ⟨Hd', hHd', he', hDH⟩ := clean_source_votes_before hp hc
        (max (tr.time q) (tr.time j)) hy hsource hclean (le_max_left _ _)
        j (le_max_right _ _) z hz ell' e hcast (by omega)
      obtain rfl : Hd' = Hd := hr.coherent.1 hHd' hHd (he'.trans he.symm)
      exact SA.anc_total hr.coherent hCH hDH
    cases hf : l.fast
    · obtain ⟨q, -, D, hsl, L, hL, hLr, hLD⟩ := SA.slow_lock_provenance hr hy i l hl hf
      obtain rfl : Y = L := hr.coherent.1 hY hL (hYr.trans hLr.symm)
      exact down hLD (compare (Or.inr hsl))
    · obtain ⟨q, -, D, CV', hfl, L, hL, hLr, hLD⟩ := SA.fast_lock_provenance hr hy i l hl hf
      obtain rfl : Y = L := hr.coherent.1 hY hL (hYr.trans hLr.symm)
      exact down hLD (compare (Or.inl ⟨CV', hfl⟩))
  · obtain ⟨L, hL, hLr, D, hLD, q, -, CV', hD⟩ := SA.lock_below_origin hr hy i l hl
    obtain rfl : Y = L := hr.coherent.1 hY hL (hYr.trans hLr.symm)
    rw [hls] at hD
    apply down hLD
    rcases hD with hD | hD
    · exact SA.result_result_compatible hS hx hres hy hD hgs4
    · exact SA.result_optimistic_compatible hS hx hres hy hD hgs4

/-- Every honest cast after a late raw result extends each prefix of that result.
The induction is over receiving cuts for all later labels, not over the writer cut. -/
theorem late_result_prefix_votes_before
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    (Q : Time) {x : Fin sp.n} (hx : x ∈ H) {r s : Nat}
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocks H) B C)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrQ : tr.time r ≤ Q) :
    ∀ i, tr.time i ≤ Q → ∀ y ∈ H, ∀ ell e, SA.CastAt tr.projAC y i ell e →
      s < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hS := healthy_base_of_reset_catch hp hc
  have hr := hS.run.localRun
  have hsync := reset_raw_sync_window_before hp Q
  have hcatch := catch_window_of_reset_catch hp hc Q
  have hclean : cleanLabel sp a + sp.k + 2 ≤ s := by have := sp.two_le_k; omega
  have hts := (clean_source_timing hp hclean).1
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
    obtain ⟨hroot, hkeep⟩ := result_prefix_vote_domain_before hp hc Q hx hy hres hBC hclean
      hcast hsi hiQ hprior
    have hvi := vote_viable_of_root hp.run hp.noColl hy hcast hroot hkeep
    obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcast.1
    by_cases hBF : Anc (tr.HonestBlocks H) B ell.frame.fcRoot
    · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := Compose.cast_head_fcRoot hr hy hcast
      exact ⟨Hd, hΦU hHd, hHdr, hBF.trans (hfHd.mono hΦU)⟩
    have hv := hvi.resolve_right hBF
    have hFB := (hΦ.rooted.2 B hv.1.1).mono hΦU
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
          (hgs.trans ((SA.ts_le_iff sp).mpr (by omega)))))
    by_cases hfirst : e.msg.slot = s + 1
    · have carry : SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s CV := by
        apply Compose.carryAt_of_writer_window_before hr (SA.serviceWindowBefore_of_sync hsync)
          hgs hcatch (by linarith) hx hy hcast hfirst hiQ
        intro v hv
        obtain ⟨hvs, hw, D, hD, hDr, hCD, ha⟩ := Compose.result_writer hr hx hres v hv
        exact ⟨hvs, hw, D, hD, hDr, hFB.trans (hBC.trans hCD), ha⟩
      refine SA.result_prefix_vote_extends_of_stored hS.run (faulty_lt_half hp x)
        hx hy hres hBC hcast hfirst carry ?_
        (result_prefix_stored_locks hp hc hx hy hres hBC hs (by
          change s + 1 ≤ sp.slot (tr.projAC.time i)
          rw [← (SA.castAt_spec hr hy hcast).2.1, hfirst]))
        (fun z hz q hq e' he hslot => hprior z hz q hq e' he (by omega)) ?_
      · rw [← hfirst]; exact Or.inl hv
      · obtain ⟨ellX, hupd, -⟩ := hres
        exact SA.writer_merged_window_before hS.run (SA.serviceWindowBefore_of_sync hsync)
          hx hgs hupd hrQ hy hcast hfirst
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
        obtain ⟨Hv, hHv, hHvr, hBHv⟩ := hprior z hz q hqi e' ⟨ell', hc'⟩ (by omega)
        obtain ⟨⟨Hd, hHd, hHdr, -⟩, hqt⟩ := Compose.cast_head_fcRoot hr hz hc'
        obtain rfl : Hd = Hv := hr.coherent.1 ((SA.frameIn_of_callAt hr hz hc'.1).2 hHd)
          hHv (hHdr.trans hHvr.symm)
        have hgm := hgs.trans ((SA.ts_le_iff sp).mpr (show (s : Int) ≤ m by omega))
        apply Compose.carryAt_of_writer_window_before hr (SA.serviceWindowBefore_of_sync hsync)
          hgm hcatch (by linarith) hz hy hcast hm hiQ
        rintro v rfl
        have ht : tr.projAC.time q < sp.ts m + 2 * sp.Δ := by
          rw [hslot] at hqt
          linarith
        refine ⟨hslot, ⟨q, ⟨ell', hc'.1, Or.inl ⟨e', hc'.2, rfl⟩⟩,
          (SA.ts_le_iff_le_slot sp (hr.time_nonneg q) m).mpr
            (by rw [← (SA.castAt_spec hr hz hc').2.1, hslot]), ht⟩,
          Hd, hHv, hHvr, hFB.trans hBHv, ?_⟩
        rcases Compose.frame_anc_accepted hr hz q ell' hc'.1 Hd hHd Hd .refl with hg | ⟨k, hk, ha⟩
        · exact Or.inl hg
        · exact Or.inr ⟨k, ha, (hr.time_mono hk).trans_lt ht⟩
      refine SA.next_vote_extends_before hS.run hy hcast hm
        (fun z hz q hq e' he hslot => hprior z hz q hq e' he (by rcases hslot with h | h <;> omega))
        (half_committee hp (hts.trans ((SA.ts_le_iff sp).mpr (by omega))))
        ⟨hr.awake_of_call y hy i ell hcast.1, (SA.castAt_spec hr hy hcast).2.2.1,
          fun v hv => (hone v hv).heads v rfl, fun v hv => (hone v hv).holds v rfl⟩
        hfault (sync m hsm.le) ?_
      rw [← hm]
      exact Or.inl hv

/-- Finite recent-result induction. Current vote domains and first-successor stored-lock
comparisons are the explicit M4/M5 inputs, rather than whole-history invariants. -/
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
          hgs hS.catchUp (by linarith) hx hy hcast hfirst hib
        intro v hv
        obtain ⟨hvs, hw, D, hD, hDr, hCD, ha⟩ := Compose.result_writer hr hx hres v hv
        exact ⟨hvs, hw, D, hD, hDr, hFB.trans (hBC.trans hCD), ha⟩
      refine SA.result_prefix_vote_extends_of_stored hS.run hf hx hy hres hBC hcast
        hfirst carry ?_ (hstored y hy i ell e hcast hib hfirst)
        (fun z hz q hq e' he hslot => hprior z hz q hq e' he (by omega)) ?_
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
        obtain ⟨Hv, hHv, hHvr, hBHv⟩ := hprior z hz q hqi e' ⟨ell', hc'⟩ (by omega)
        obtain ⟨⟨Hd, hHd, hHdr, -⟩, hqt⟩ := Compose.cast_head_fcRoot hr hz hc'
        obtain rfl : Hd = Hv := hr.coherent.1 ((SA.frameIn_of_callAt hr hz hc'.1).2 hHd)
          hHv (hHdr.trans hHvr.symm)
        have hgm := hgs.trans ((SA.ts_le_iff sp).mpr (show (s : Int) ≤ m by omega))
        apply Compose.carryAt_of_writer_window_before hr (SA.serviceWindowBefore_of_sync hS.sync)
          hgm hS.catchUp (by linarith) hz hy hcast hm hib
        rintro v rfl
        have ht : tr.projAC.time q < sp.ts m + 2 * sp.Δ := by rw [hslot] at hqt; linarith
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
        simp only [SA.SAParams.ts] at htime ⊢; push_cast at htime; linarith
      have hcut : cutZ sp.toParams g ≤ tr.time i := hts.trans
        (((SA.ts_le_iff sp).mpr (by omega)).trans htime)
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
        (fun z hz q hq e' he hslot => hprior z hz q hq e' he (by rcases hslot with h | h <;> omega))
        (hp.half_committee (hts.trans ((SA.ts_le_iff sp).mpr (by omega))) hmt)
        ⟨hr.awake_of_call y hy i ell hcast.1, (SA.castAt_spec hr hy hcast).2.2.1,
          fun v hv => (hone v hv).heads v rfl, fun v hv => (hone v hv).holds v rfl⟩
        hfault
        (hp.sync.syncAC hp.run ((SA.le_gbar g).trans
          (hgs.trans ((SA.ts_le_iff sp).mpr (by omega))))) ?_
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
    exact ht.trans ((SA.ts_le_iff sp).mpr (by dsimp [n]; omega))
  obtain ⟨j, e, hv, hes⟩ := SA.honest_votes_in_slot hS htime x hx
  obtain ⟨ell, hcast⟩ := hv
  have hB := clean_source_votes_before hp hc (max (tr.time r) (tr.time j)) hx hsource hs
    (le_max_left _ _) j (le_max_right _ _) x hx ell e hcast (by dsimp [n] at hes; omega)
  exact target_compatible_older_origin hp ho hx ⟨ell, hcast⟩ hes
    (by dsimp [n]; omega) hB

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
    have ht := (SA.ts_le_iff sp).mpr (show (s : Int) + 1 ≤ u by omega)
    simp only [SA.SAParams.ts] at ht ⊢
    nlinarith
  obtain ⟨v, _, D, hD, hDr, hBD, hg | ⟨q, hq, hqt⟩⟩ :=
    raw_writer_relay_source hr hx hwriter hBC
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
          have hd := deadline_le_restarts
            (T := tr.projAC) (c := k) (fun k' _ hr' => hS.restart_le hpH hr') (tr.time q)
          have ht : max (tr.time q) (SA.gbar g) < sp.ts s + 2 * sp.Δ := by
            apply max_lt hqt
            linarith
          change _ ≤ max (tr.time q) (SA.gbar g) + sp.Δ at hd
          linarith
        obtain ⟨k, hki, hak, _⟩ := (hS.syncAC le_rfl (tr.time q)).2 x hx q D hq hg le_rfl
          p hpH i ell hci (by
            have := hdl i le_rfl
            change tr.projAC.deadline p i (tr.time q) ≤ tr.time i
            linarith) hFD
        exact SA.mem_tree_of_acceptAt sp hr hpH hak hki hci hFD
      · obtain ⟨k, hki, hak, _⟩ := hS.catchUp x hx q D hq (not_le.mp hg) p hpH i ell hci
          (by change _ ≤ tr.time i; linarith) hFD
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
  · have hd := deadline_le_restarts
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

/-- A floor above a held target above a high seed has an actual earlier honest report
extending the target with strictly greater height at the reporter's cut. -/
theorem held_target_high_floor_report_before
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {y v : Fin sp.n} (hy : y ∈ H) {i q m : Nat}
    {P S : SA.Blk sp.n (List (FG.Att sp.n))} (hPy : P ∈ (tr.state y i).fg.tree)
    (hseed : HighOrigin tr H g v q m S) (hSP : Anc (tr.HonestBlocks H) S P)
    (hcompare : ∀ x r b B, r < i → HighOrigin tr H g x r b B →
      Compatible (tr.HonestBlocks H) P B)
    (hfloor : ((tr.state y i).fg.σ P.root).h < (tr.state y i).fg.headHeightFloor) :
    ∃ x ∈ H, ∃ r ell C, r < i ∧ SA.ToFGAt tr.projAC x r ell C ∧
      Anc (tr.HonestBlocks H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h := by
  have hU := honest_coherent hp
  have hSy := mem_tree_of_anc hp hy hSP hPy
  have hreach := Compose.fg_reachable hp.run.toLocalRun hy i
  have hret := height_scoped_retention sp ro proposer dg H tr g ΔF
    hp.run hp.healthy hp.noColl a hp.reset
  obtain ⟨-, -, -, -, -, -, -, -, -, hSs⟩ := highOrigin_mem hp hseed
  have hSh := σ_h_le_of_anc hreach (anc_tree_of_anc hp hy hSP hPy)
  have hSf : ((tr.state v q).fg.σ S.root).h < (tr.state y i).fg.headHeightFloor := by
    rw [σ_eq_run hp hseed.1 hy hSs hSy]
    omega
  obtain ⟨x, r, b, B, E, hri, ho, -, hE, hEB, -, hEf, d, att, hrd, hdi, hsign, haT⟩ :=
    high_floor_signed_source_of_row_bound hp hseed hy (u := sp.slot (tr.time i) + 1)
      (fun W hW att ha z hz d hd hdi r' l O hrd ho => by
        obtain ⟨-, D, CV, -, hfl, -⟩ := highOrigin_mem hp ho
        have ht : sp.ts l ≤ tr.time i :=
          (ts_le_of_fastLock hp hfl).trans (hp.run.time_mono (by omega))
        have hlabel : (l : Int) ≤ sp.slot (tr.time i) :=
          (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg i) l).mp ht
        omega)
      (fun x r b B _ ho x' r' b' B' _ ho' => hret.comparable x r b B x' r' b' B' ho ho')
      (fun x r b B _ ho => hret.comparable v q m S x r b B hseed ho) hSf
  have hPE : Anc (tr.HonestBlocks H) P E := by
    have hcomp : Compatible (tr.HonestBlocks H) P E := by
      rcases hcompare x r b B hri ho with h | h
      · exact SA.anc_total hU h hEB
      · exact Or.inr (hEB.trans h)
    rcases hcomp with h | h
    · exact h
    · have := σ_h_le_of_anc hreach (anc_tree_of_anc hp hy h hPy)
      omega
  obtain ⟨j, hdj, -, ell, C, E', hreport, hC, hE', hEr, hEC, -, -, hEh, -⟩ :=
    signAt_report_entry hp.run ho.1 hsign
  obtain rfl : E' = E := hU.1 ⟨x, ho.1, j, hE'⟩ ⟨y, hy, i, hE⟩ (hEr.trans haT)
  have hPC := hPE.trans (hEC.mono (fun X hX => ⟨x, ho.1, j, hX⟩))
  have hPx := mem_tree_of_anc hp ho.1 hPC hC
  refine ⟨x, ho.1, j, ell, C, by omega, hreport, hPC, ?_⟩
  rw [← hEh, σ_eq_run hp ho.1 hy hPx hPy, σ_eq_run hp ho.1 hy hE' hE]
  omega

end Consensus.Goldilocks.Healing

end
