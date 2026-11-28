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
the report-cover suppliers; this separation lets
those suppliers use the pivot without an import cycle. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload Vote)

variable {sp : ACParams}
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

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n}
  {ini : Fin sp.n → (goldilocksNode sp).State} {g ΔF a : Time}

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

/-- Guarded receipt of an actual acceptance: old sources use Catch, newer ones use Sync.
The receiver's finalization bound is required; archival heldness alone is not frame membership. -/
theorem reset_accept_frame
    (hp : ResetPremises tr H K proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {q j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (ha : tr.projAC.AcceptAt x q B)
    {ell : ACLabel (goldilocksNode sp)} (hcall : tr.projAC.CallAt y j ell)
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
    {ellx elly : ACLabel (goldilocksNode sp)}
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
