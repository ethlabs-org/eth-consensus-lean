module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Served
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Service
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Pivot
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotOldSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotSourceVotes
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Head
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Strict
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FastExpiry
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Operational update selection and reports after the drain

Finite-horizon vote propagation, update selection and report coverage shared by Healing and
the obligations proof. Start with `UpTo.operational_update_selection` and
`UpTo.report_cover_of_proposal`; their supporting arguments work backwards from actual bounded
calls to unanimous votes, retained sources and compatible locks. Generic effective-record
preservation and interval contracts are in `Obligations/HealthyEffective`.
-/

namespace Consensus.Goldilocks.Obligations

variable {sp : AC.ACParams} {FGP : Type} {U : Set (AC.Blk sp.n FGP)}

/-- Writing a held candidate leaves that candidate or a strictly later descendant.
The guard can retain a record only above the candidate, never an older fork. -/
theorem effective_record_update_slot_growth
    {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ) {A : AC.ACState sp.n}
    {P : AC.Blk sp.n FGP} (hP : P ∈ Φ.tree) :
    let C := (AC.lookup Φ (AC.updateLatestConfirmed sp A Φ P).latestConfirmed).getD Φ.F
    Φ.Anc P C ∧ (C = P ∨ P.slot < C.slot) := by
  classical
  dsimp only
  have lookup_self : ∀ D ∈ Φ.tree, AC.lookup Φ D.root = some D := by
    intro D hD
    cases he : AC.lookup Φ D.root with
    | none => exact False.elim (AC.lookup_eq_none he ⟨D, hD, rfl⟩)
    | some C =>
      obtain ⟨hC, hr⟩ := AC.lookup_eq_some he
      exact congrArg some (hΦ.coherent.1 hC hD hr)
  have hanc : Φ.Anc P
      ((AC.lookup Φ (AC.updateLatestConfirmed sp A Φ P).latestConfirmed).getD Φ.F) := by
    unfold AC.updateLatestConfirmed
    split_ifs with hg
    · obtain ⟨C, hC, hr, hPC⟩ := hg
      rw [← hr, lookup_self C hC]
      exact hPC
    · change Φ.Anc P ((AC.lookup Φ P.root).getD Φ.F)
      rw [lookup_self P hP]
      exact .refl
  refine ⟨hanc, ?_⟩
  by_cases he : (AC.lookup Φ (AC.updateLatestConfirmed sp A Φ P).latestConfirmed).getD Φ.F = P
  · exact Or.inl he
  · exact Or.inr ((hanc.slot_le hΦ.coherent).2 (Ne.symm he))

section CoveredEndpoint

variable {ro : AC.ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {K : AC.CommitteeDict sp.n} {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)} {g ΔF a : Time}

namespace UpTo

/-- Reset and drain timing put every bounded honest restart before the preceding
slot's join threshold; no last-wake bound at GST is assumed. -/
theorem restart_before_unanimous_slot {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {u : Nat} (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    {y : Fin sp.n} (hy : y ∈ H) {r : Nat} (hr : tr.RestartAt y r)
    (hrb : tr.time r ≤ b) : tr.time r ≤ sp.ts ((u : Int) - 1) := by
  have hca := Healing.cutZ_lt_reset_of_snapshot hp.run
    (by obtain ⟨k, hk, -⟩ := hp.snapshot; exact ⟨k, hk⟩) hp.reset
  have ha0 : 0 ≤ a := by
    have := Healing.lt_cutZ sp g
    have := AC.gbar_nonneg g
    linarith [sp.toParams.hΔ]
  rw [Healing.cutZ_eq] at hca
  have hqa := (AC.ts_le_iff_le_slot sp ha0 _).1 hca.le
  rw [Healing.drainTime_eq] at hR
  have hAu := (AC.ts_le_iff sp).1 hR
  apply (Healing.restart_le_before hp hy hr hrb).trans
  apply (AC.ts_le_iff sp).2
  push_cast at hqa hAu ⊢
  omega

/-- The drain puts the slot before it at or after `c_z = g' + 8Δ`, `g' = t_{slot(ḡ)+1}`: the
AC base from `g'` serves it. -/
theorem slotAfter_add_le_of_drain {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {u : Nat} (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat)) :
    AC.gbar (sp.ts (sp.slot (AC.gbar g) + 1 : Nat)) + 4 * sp.Δ ≤ sp.ts u := by
  have hca := Healing.cutZ_lt_reset_of_snapshot hp.run
    (by obtain ⟨k, hk, -⟩ := hp.snapshot; exact ⟨k, hk⟩) hp.reset
  have ha0 : 0 ≤ a := by
    have := Healing.lt_cutZ sp g
    have := AC.gbar_nonneg g
    linarith [sp.toParams.hΔ]
  have hcz : Healing.cutZ sp.toParams g ≤ sp.ts u := by
    rw [Healing.cutZ_eq] at hca ⊢
    have hqa := (AC.ts_le_iff_le_slot sp ha0 _).1 hca.le
    rw [Healing.drainTime_eq] at hR
    have hAu := (AC.ts_le_iff sp).1 hR
    apply (AC.ts_le_iff sp).2
    push_cast at hqa hAu ⊢
    omega
  rw [Healing.gbar_slotAfter]
  rw [Healing.cutZ_eq_slotAfter] at hcz
  linarith [sp.toParams.hΔ]

/-- Finite reset service supplies actual votes from every honest member of the slot's committee
by the slot deadline. -/
theorem honest_votes_in_slot {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b) :
    ∀ y ∈ H, y ∈ K.committee u → ∃ j e, AC.VoteAt tr.projAC y j e ∧ e.msg.slot = u ∧
      tr.time j ≤ sp.ts u + sp.Δ := by
  intro y hy hyK
  refine AC.honest_votes_in_slot_before (Healing.healthy_base_of_reset_catch_before hp hc)
    (slotAfter_add_le_of_drain hp hR) hub ?_ y hy hyK
  intro y hy r hr hrs
  exact restart_before_unanimous_slot hp hR hy
    (Compose.projAC_restartAt.mp hrs) (hr.trans hub)

/-- The honest voters of the slot are half of the committee size, so one of them votes by the
slot deadline. These witnesses seed the old-origin ancestry argument. -/
theorem exists_honest_vote_in_slot {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b) :
    ∃ z ∈ H, ∃ j e, AC.VoteAt tr.projAC z j e ∧ e.msg.slot = u ∧
      tr.time j ≤ sp.ts u + sp.Δ := by
  obtain ⟨z, hz, j, e, hv, hs, ht⟩ := Set.nonempty_of_ncard_ne_zero (s := {x | x ∈ H ∧
    ∃ j e, AC.VoteAt tr.projAC x j e ∧ e.msg.slot = u ∧ tr.projAC.time j ≤ sp.ts u + sp.Δ})
      (by
      have := AC.honest_voters_half_before (Healing.healthy_base_of_reset_catch_before hp hc)
        (slotAfter_add_le_of_drain hp hR) hub fun y hy r ht hrs =>
          restart_before_unanimous_slot hp hR hy (Compose.projAC_restartAt.mp hrs)
            (ht.trans hub)
      have := hp.committee_pos
      omega)
  exact ⟨z, hz, j, e, hv, hs, ht⟩

/-- The drain puts the slot after the slot of `ḡ`. -/
theorem slot_gbar_lt_of_drain {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {u : Nat} (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat)) :
    sp.slot (AC.gbar g) + 1 ≤ u := by
  have h := slotAfter_add_le_of_drain hp hR
  rw [Healing.gbar_slotAfter] at h
  exact Healing.slot_gbar_lt_of_slotAfter_le (by linarith [sp.toParams.hΔ])

/-- Finite writer service carries the previous honest vote batch to a bounded
next-slot cast. Only actual previous votes, bounded by this cast, are consulted. -/
theorem unanimous_carry_votes {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H)
    (hun : ∀ y ∈ H, ∀ j e, AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hcast : AC.CastAt tr.projAC y i ell e)
    (hs : e.msg.slot = u + 1) (hib : tr.time i ≤ b)
    (hFP : Anc (tr.HonestBlocks H) ell.frame.F P) :
    AC.CarryAt tr.projAC (tr.HonestBlocks H) y i e u (Compose.honestVotes tr H u) := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  have hDelta := sp.toParams.hΔ
  apply AC.carryAt_of_each (hr.awake_of_call y hy i ell hcast.1)
    (AC.castAt_spec hr hy hcast).2.2.1
  rintro v ⟨z, hz, q, e', ⟨ell', hc'⟩, rfl, hsl⟩
  have hqi : q < i := by
    by_contra hn
    have := AC.slot_mono sp (hr.time_nonneg i) (hr.time_mono (Nat.le_of_not_gt hn))
    have := (AC.castAt_spec hr hz hc').2.1
    have := (AC.castAt_spec hr hy hcast).2.1
    omega
  obtain ⟨⟨Hd, hHd, hHdr, _⟩, hqt⟩ := Compose.cast_head_fcRoot hr
      hp.run.vstart hz hc'
  have hHdP : Hd = P := hr.coherent.1 ((AC.frameIn_of_callAt hr hz hc'.1).2 hHd) hP
    (hHdr.trans (hun z hz q e' ⟨ell', hc'⟩ ((hp.run.time_mono hqi.le).trans hib) hsl))
  subst Hd
  apply Compose.carryAt_of_writer_window_before hr hp.run.vstart
    (AC.serviceWindowBefore_of_sync (Healing.sync_window_of_service hp.run hp.sync))
    (by linarith : AC.gbar g ≤ sp.ts u) (Healing.catch_window_of_run hp.run hc) (by linarith)
    hz hy hcast hs hib
  rintro v rfl
  have ht : tr.projAC.time q < sp.ts u + 2 * sp.Δ := by rw [hsl] at hqt; linarith
  refine ⟨hsl, ⟨q, ⟨ell', hc'.1, Or.inl ⟨e', hc'.2, rfl⟩⟩,
    (AC.ts_le_iff_le_slot sp (hr.time_nonneg q) u).mpr
      (by rw [← (AC.castAt_spec hr hz hc').2.1, hsl]), ht⟩, P, hP, hHdr, hFP, ?_⟩
  rcases Compose.frame_anc_accepted hr hz q ell' hc'.1 P hHd P .refl with hg | ⟨k, hk, ha⟩
  · exact Or.inl hg
  · exact Or.inr ⟨k, ha, (hr.time_mono hk).trans_lt ht⟩

/-- Finite unanimity bounds all origins written before the following slot, including
same-label optimistic writes. The old-origin bound is derived, not supplied. -/
theorem high_origins_before_next_slot_below {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H)
    (hun : ∀ y ∈ H, ∀ j e, AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b)
    {x : Fin sp.n} {r m : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : Healing.HighOrigin tr H g x r m B)
    (ht : tr.time r < sp.ts (u + 1 : Nat)) (hrb : tr.time r ≤ b) :
    Anc (tr.HonestBlocks H) B P := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  obtain ⟨ell, D, CV, hcall, hfl, _, _, _, hBD, _⟩ := hp.highOrigin_mem ho
  have hmu : m ≤ u := by
    rcases hfl with ⟨ell, C, hu, _⟩ | ⟨ell, A, _, hs, _⟩
    · have htime : tr.time r = sp.ts m + 6 * sp.Δ := hu.2.2.1
      have hts : sp.ts m < sp.ts (u + 1 : Nat) := by linarith [sp.toParams.hΔ]
      have := (AC.ts_lt_iff sp).1 hts
      omega
    · have hs' : sp.slot (tr.time r) = m := hs
      have := (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg r) ((u + 1 : Nat) : Int)).not.mp
        (not_le.mpr ht)
      omega
  rcases lt_or_eq_of_le hmu with hmu | rfl
  · obtain ⟨z, hz, q, e, ⟨ellv, hv⟩, hs, hq⟩ := exists_honest_vote_in_slot hp hc hR hub
    obtain ⟨Hd, hHd, he, hBH⟩ := hp.high_origin_votes_before q (hq.trans hub)
      x r m B ho hrb z hz ellv e hv (by omega)
    have heq : Hd = P := hr.coherent.1 hHd hP
      (he.trans (hun z hz q e ⟨ellv, hv⟩ (hq.trans hub) hs))
    exact heq ▸ hBH
  · exact (hBD.mono (AC.frameIn_of_callAt hr ho.1 hcall).2).trans
      (hp.same_slot_source_below_unanimous ho.1 (Or.inl ⟨CV, hfl⟩) hrb
        (hp.cutZ_le_ts_of_highOrigin ho) hP hun)

/-- Actual bounded unanimity admits P into every next-slot frozen viable tree. -/
theorem unanimous_next_vote_viable {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y ∈ H, ∀ j e, AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hcast : AC.CastAt tr.projAC y j ell e)
    (hs : e.msg.slot = u + 1) (hjb : tr.time j ≤ b) :
    Anc (tr.HonestBlocks H) ell.frame.F P ∧
      P ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame (u + 1)) := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  have hbound := fun x r m B ho ht hrb =>
    high_origins_before_next_slot_below hp hc hP hun hgu hR hub
      (x := x) (r := r) (m := m) (B := B) ho ht hrb
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hy hcast.1
  have hroot := hp.reset_vote_root_below_bound hR hP hbound hy hcast hs hjb
  have hFP := (hPhi.F_anc_fcRoot.mono hPhiU).trans hroot
  -- an honest slot-`u` voter holds `P` by `t_u + Δ`; the relay reaches `y` by `t_u + 2Δ`
  obtain ⟨z, hz, q, v, ⟨ellv, hv⟩, hvs, hq⟩ := exists_honest_vote_in_slot hp hc hR hub
  obtain ⟨⟨Hd, hHd, he, _⟩, _⟩ := Compose.cast_head_fcRoot hr hp.run.vstart hz hv
  have heq : Hd = P := hr.coherent.1 ((AC.frameIn_of_callAt hr hz hv.1).2 hHd) hP
    (he.trans (hun z hz q v ⟨ellv, hv⟩ (hq.trans hub) hvs))
  subst Hd
  have hΔ := sp.toParams.hΔ
  have hjt : sp.ts (u + 1 : Nat) ≤ tr.time j :=
    (AC.ts_le_iff_le_slot sp (hr.time_nonneg j) _).2
      (by rw [← (AC.castAt_spec hr hy hcast).2.1, hs])
  have hsucc : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [AC.ACParams.ts]; push_cast; ring
  have hg' := slotAfter_add_le_of_drain hp hR
  rw [Healing.gbar_slotAfter] at hg'
  have hacc : AC.AcceptedBefore tr.projAC y P (sp.ts u + 3 * sp.Δ) := by
    rcases AC.frame_genesis_or_accepted sp hr hz hv.1 P hHd with hz0 | ⟨k, hk, ha⟩
    · omega
    have hkq : tr.time k ≤ tr.time q := hp.run.time_mono hk
    refine Or.inr ?_
    by_cases hnew : AC.gbar g ≤ tr.time k
    · obtain ⟨k', -, hak, hkt⟩ := hp.reset_relay_accept hz hy ha hnew hcast.1 hjb
        (by linarith) (by linarith) hFP
      refine ⟨k', hak, hkt.trans_le ?_⟩
      have := max_le (show tr.time k ≤ sp.ts u + sp.Δ by linarith)
        (show sp.ts (sp.slot (AC.gbar g) + 1 : Nat) ≤ sp.ts u + sp.Δ by linarith)
      linarith
    · obtain ⟨k', -, hak, hkt⟩ := (Healing.catch_window_of_run hp.run hc).relay z hz k P ha
        (not_le.mp hnew) y hy j ell hcast.1 (by change _ ≤ tr.time j; linarith) hjb hFP
      exact ⟨k', hak, hkt.trans_le (by linarith)⟩
  have hPt := Compose.accepted_voter_tree hp.run hp.noColl hy hcast hs hP hacc hFP
  have hstore : P ∈ (tr.state y j).fg.tree := by
    have hm := hPt.1
    rw [Compose.frame_of_projAC hp.run hy hcast.1] at hm
    exact hm.1
  have hfloor := hp.reset_vote_floor_above_old hy hR hcast hs hjb hstore hbound
  have hroot' := AC.anc_tree_of_anc_U hr.coherent hPhi hPhiU
    hPhi.fcRoot_mem hroot hPt.1
  refine ⟨hFP, hPt, hroot', P, hPt, ?_, .refl⟩
  have hm := hPt.1
  rw [Compose.frame_of_projAC hp.run hy hcast.1] at hm hroot' ⊢
  exact ⟨hm.1, hm.2, hroot'.mono (fun X hX => hX.1), hfloor⟩

/-- Bounded actual unanimity propagates through every next-slot cast by finite
retention and writer service, without a supplied old-origin or viability duty. -/
theorem unanimous_next_votes_extend {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y ∈ H, ∀ j e, AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b) :
    ∀ y ∈ H, ∀ j e, AC.VoteAt tr.projAC y j e → tr.time j ≤ b → e.msg.slot = u + 1 →
      AC.VoteExtends (tr.HonestBlocks H) e.msg P := by
  have hac := Compose.goldilocks_ac_projection_from hp.run hp.noColl
  have hr := hac.localRun
  have hu1 := slot_gbar_lt_of_drain hp hR
  have hhalf : sp.committeeSize ≤ 2 * {y | y ∈ H ∧ ∃ j e, AC.VoteAt tr.projAC y j e ∧
      e.msg.slot = u}.ncard := by
    have h := AC.honest_voters_half_before (Healing.healthy_base_of_reset_catch_before hp hc)
      (slotAfter_add_le_of_drain hp hR) hub (by
      intro y hy r ht hrs
      exact restart_before_unanimous_slot hp hR hy (Compose.projAC_restartAt.mp hrs)
        (ht.trans hub))
    have hm := Set.ncard_le_ncard (s := {y | y ∈ H ∧ ∃ j e, AC.VoteAt tr.projAC y j e ∧
      e.msg.slot = u ∧ tr.time j ≤ sp.ts u + sp.Δ})
      (t := {y | y ∈ H ∧ ∃ j e, AC.VoteAt tr.projAC y j e ∧ e.msg.slot = u})
      (by rintro y ⟨hy, j, e, hv, hs, _⟩; exact ⟨hy, j, e, hv, hs⟩)
    exact h.trans (Nat.mul_le_mul_left 2 hm)
  have all : ∀ j, tr.time j ≤ b → ∀ y ∈ H, ∀ e,
      AC.VoteAt tr.projAC y j e → e.msg.slot = u + 1 →
      AC.VoteExtends (tr.HonestBlocks H) e.msg P := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      rintro hjb y hy e ⟨ell, hcast⟩ hs
      obtain ⟨hFP, hvi⟩ := unanimous_next_vote_viable hp hc hP hslot hu hun hgu hR hub
        hy hcast hs hjb
      have htime : sp.ts (u + 1 : Nat) ≤ tr.time j :=
        (AC.ts_le_iff_le_slot sp (hr.time_nonneg j) _).2
          (by rw [← (AC.castAt_spec hr hy hcast).2.1, hs])
      obtain ⟨v, r, l, O, ho, _, hl, _⟩ := hp.reset_seed_before_slot hR
      have hcut : Healing.cutZ sp.toParams g ≤ tr.time j :=
        (hp.cutZ_le_ts_of_highOrigin ho).trans
          (((AC.ts_le_iff sp).2 (by omega)).trans htime)
      apply AC.next_vote_extends_before hac K hp.hP hp.hT hp.hsize hy hcast hs ?_ hhalf
        (unanimous_carry_votes hp hc hP hun hgu hy hcast hs hjb hFP)
        (hp.faultBoundK_late hu1 hcut hjb) (hp.cs2 (hu1.trans (Nat.le_succ u)))
        (hp.sync.syncAC hp.run (by have := AC.le_gbar g; linarith [sp.toParams.hΔ]))
        (Or.inl hvi)
      intro z hz q hq e' hv hsl
      have hqb := (hp.run.time_mono hq.le).trans hjb
      rcases hsl with hsl | hsl
      · exact ⟨P, hP, (hun z hz q e' hv hqb hsl).symm, .refl⟩
      · exact ih q hq hqb z hz e' hv hsl
  exact fun y hy j e hv hjb hs => all j hjb y hy e hv hs

/-- A bounded next-slot optimistic source compares with P through an actual honest
supporter, whose cast is no later than the source. -/
theorem unanimous_next_optimistic_compatible {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y ∈ H, ∀ j e, AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {D : AC.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (AC.Vote sp.n)} (hopt : AC.OptimisticLockAt tr.projAC y j (u + 1) D CV)
    (hjb : tr.time j ≤ b) : Compatible (tr.HonestBlocks H) D P := by
  obtain ⟨_, z, hz, q, hq, e, hv, hs, Hd, hHd, he, hDH⟩ := hp.optimistic_supporter hy
    ((slot_gbar_lt_of_drain hp hR).trans (Nat.le_succ u)) hopt
  obtain ⟨Hd', hHd', he', hPH⟩ := unanimous_next_votes_extend hp hc hP hslot hu hun hgu hR hub
    z hz q e hv ((hp.run.time_mono hq).trans hjb) hs
  obtain rfl : Hd' = Hd := hp.honest_coherent.1 hHd' hHd (he'.trans he.symm)
  exact AC.anc_total hp.honest_coherent hDH hPH

/-- Every high origin written through the update deadline compares with P. The
next-slot optimistic arm uses finite vote extension; later raw writes cannot occur. -/
theorem high_origin_compatible_before_update {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y ∈ H, ∀ j e, AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {x : Fin sp.n} {r m : Nat} (ho : Healing.HighOrigin tr H g x r m B)
    (ht : tr.time r ≤ sp.ts u + 6 * sp.Δ) : Compatible (tr.HonestBlocks H) B P := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  have hub : sp.ts u + sp.Δ ≤ b := by linarith [sp.toParams.hΔ]
  have hrb := ht.trans hTb
  obtain ⟨ell, D, CV, hcall, hfl, _, _, _, hBD, _⟩ := hp.highOrigin_mem ho
  have hBDU := hBD.mono (AC.frameIn_of_callAt hr ho.1 hcall).2
  by_cases hmu : m < u
  · obtain ⟨z, hz, q, e, ⟨ellv, hv⟩, hs, hq⟩ := exists_honest_vote_in_slot hp hc hR hub
    obtain ⟨Hd, hHd, he, hBH⟩ := hp.high_origin_votes_before q (hq.trans hub)
      x r m B ho hrb z hz ellv e hv (by omega)
    have heq : Hd = P := hr.coherent.1 hHd hP
      (he.trans (hun z hz q e ⟨ellv, hv⟩ (hq.trans hub) hs))
    exact Or.inl (heq ▸ hBH)
  by_cases heq : m = u
  · subst m
    exact Or.inl (hBDU.trans (hp.same_slot_source_below_unanimous ho.1
      (Or.inl ⟨CV, hfl⟩) hrb (hp.cutZ_le_ts_of_highOrigin ho) hP hun))
  have hgt : u < m := by omega
  have hDP : Compatible (tr.HonestBlocks H) D P := by
    rcases hfl with ⟨ellr, C, hupd, _⟩ | hop
    · have ht' : tr.time r = sp.ts m + 6 * sp.Δ := hupd.2.2.1
      have := (AC.ts_lt_iff sp).2 (show (u : Int) < m by omega)
      exfalso; linarith
    · have hs : sp.slot (tr.time r) = m := hop.choose_spec.choose_spec.2.1
      have hdeadline : sp.slot (sp.ts u + 6 * sp.Δ) = u + 1 :=
        AC.slot_of_mem sp (u + 1)
          (by simp only [AC.ACParams.ts]; push_cast; linarith [sp.toParams.hΔ])
          (by simp only [AC.ACParams.ts]; push_cast; linarith [sp.toParams.hΔ])
      have hm := AC.slot_mono sp (hp.run.time_nonneg r) ht
      rw [hs, hdeadline] at hm
      have heq : m = u + 1 := by omega
      exact unanimous_next_optimistic_compatible hp hc hP hslot hu hun hgu hR hub
        ho.1 (heq ▸ hop) hrb
  rcases hDP with h | h
  · exact Or.inl (hBDU.trans h)
  · exact AC.anc_total hr.coherent hBDU h

/-- Finite finality compatibility through the update deadline, derived from actual
unanimous votes rather than an update-selection or high-origin compatibility duty. -/
theorem finalized_compatible_before_update {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y ∈ H, ∀ j e, AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} (ha : a ≤ tr.time k)
    (ht : tr.time k ≤ sp.ts u + 6 * sp.Δ) :
    Compatible (tr.HonestBlocks H) (tr.state y k).fg.F P := by
  obtain ⟨x, r, m, B, ho, hrk, _, hFB⟩ := hp.finalized_below_high_origin hy ha
    (fun q hq => (hp.run.time_mono hq.le).trans (ht.trans hTb))
  rcases high_origin_compatible_before_update hp hc hP hslot hu hun hgu hR hTb ho
      (hrk.trans ht) with h | h
  · exact Or.inl (hFB.trans h)
  · exact AC.anc_total hp.honest_coherent hFB h

/-- Finite deadline alternative: finality is below P, or an actual earlier report
extends P with strictly greater height at that reporter's own cut. -/
theorem finality_alternative_before_update {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y ∈ H, ∀ j e, AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} (ha : a ≤ tr.time k)
    (ht : tr.time k ≤ sp.ts u + 6 * sp.Δ) :
    Anc (tr.HonestBlocks H) (tr.state y k).fg.F P ∨
      ∃ z ∈ H, ∃ r ell C, r < k ∧ AC.ToFGAt tr.projAC z r ell C ∧
        tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P C ∧
        ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h := by
  rcases hp.finality_below_or_higher_report hy
      (finalized_compatible_before_update hp hc hP hslot hu hun hgu hR hTb hy ha ht) with
    h | ⟨z, hz, r, ell, C, hrk, hto, hPC, hlt⟩
  · exact Or.inl h
  · exact Or.inr ⟨z, hz, r, ell, C, hrk, hto, (hp.run.time_mono hrk.le).trans ht, hPC, hlt⟩

/-- Every honest unanimous vote is uniquely present and early-resolved in a
bounded post-service call holding P. Restart and deadline duties are derived. -/
theorem unanimous_pool {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hun : ∀ y ∈ H, ∀ j e, AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b) (hPt : P ∈ ell.frame.tree) :
    ∀ x ∈ H, x ∈ K.committee u →
      ∃ v ∈ (tr.projAC.state y j).pool u, v.val = x ∧ v.head = P.root ∧
      AC.resolutionTime (tr.projAC.state y j) ell.frame v < AC.ETime.of (sp.ts u + 2 * sp.Δ) ∧
      ∀ v' ∈ (tr.projAC.state y j).pool u, v'.val = x → v' = v := by
  have hS := Healing.healthy_base_of_reset_catch_before hp hc
  have hrestart : ∀ k ≤ j, tr.projAC.RestartAt y k → tr.projAC.time k < sp.ts u := by
    intro k hkj hk
    have h := restart_before_unanimous_slot hp hR hy (Compose.projAC_restartAt.mp hk)
      ((hp.run.time_mono hkj).trans hjb)
    exact h.trans_lt ((AC.ts_lt_iff sp).2 (by omega))
  refine AC.unanimous_pool_before hS hy hcall (slotAfter_add_le_of_drain hp hR) ht hjb ?_
    hrestart hPt ?_
  · intro k hkj t _
    exact Compose.ac_deadline_le_of_restarts
      (fun r hr hrs => (hrestart r (hr.trans hkj) hrs).le) t
  · intro x hx hxK
    have hub : sp.ts u + sp.Δ ≤ b := by linarith [sp.toParams.hΔ]
    obtain ⟨q, e, hv, hs, hq⟩ := honest_votes_in_slot hp hc hR hub x hx hxK
    exact ⟨q, e, hv, hs, hun x hx q e hv (hq.trans hub) hs⟩

/-- At a bounded call holding a target above a bounded high seed, compatible
causal origins give full viability or an actual earlier strictly higher report. -/
theorem held_target_viable_or_higher_report {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {y v : Fin sp.n} (hy : y ∈ H) {i q m : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} (hcall : tr.projAC.CallAt y i ell)
    (hib : tr.time i ≤ b) {P S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ ell.frame.tree) (hseed : Healing.HighOrigin tr H g v q m S)
    (hqb : tr.time q ≤ b) (hSP : Anc (tr.HonestBlocks H) S P)
    (hcompare : ∀ x r l B, r < i → Healing.HighOrigin tr H g x r l B →
      Compatible (tr.HonestBlocks H) P B) :
    P ∈ ell.frame.viableTree ell.frame.tree ∨
      ∃ x ∈ H, ∃ r ell' C, r < i ∧ AC.ToFGAt tr.projAC x r ell' C ∧
        Anc (tr.HonestBlocks H) P C ∧
        ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hy hcall
  have hPy := hp.frame_tree_subset hy hcall hPt
  have hfr := Compose.frame_of_projAC hp.run hy hcall
  have hroot : Compatible (tr.HonestBlocks H) ell.frame.fcRoot P := by
    by_cases hlow : (tr.state y i).fg.hj ≤ Healing.HZ tr H g
    · exact hp.low_root_of_held_seed_at_call hy hPy hy hseed hcall
        (hp.mem_tree_of_anc hy hSP hPy) hlow (Or.inr hSP) (fun _ => hPt)
    · exact hp.high_J_root_of_held_at_call_before hy hPy hy hcall (by omega) hcompare
  by_cases hrootP : Anc (tr.HonestBlocks H) ell.frame.fcRoot P
  · by_cases hfloor : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ P.root).h
    · have hrootf := AC.anc_tree_of_anc_U hp.honest_coherent hPhi hPhiU
        hPhi.fcRoot_mem hrootP hPt
      refine Or.inl ⟨hPt, hrootf, P, hPt, ?_, .refl⟩
      have hPt' := hPt
      rw [hfr] at hPt' hrootf ⊢
      exact ⟨hPy, hPt'.2, hrootf.mono (fun X hX => hX.1), hfloor⟩
    · exact Or.inr (hp.held_target_high_floor_report_before hy hPy hseed hSP
        (fun x r l B hri ho x' r' l' B' hr'i ho' => hp.origins_compatible ho
          ((hp.run.time_mono hri.le).trans hib) ho' ((hp.run.time_mono hr'i.le).trans hib))
        (fun x r l B hri ho => hp.origins_compatible hseed hqb ho
          ((hp.run.time_mono hri.le).trans hib)) hcompare (lt_of_not_ge hfloor))
  · have hPR := hroot.resolve_left hrootP
    have hne : P ≠ ell.frame.fcRoot := fun he => hrootP (he ▸ .refl)
    have hJ : ell.frame.fcRoot = (tr.state y i).fg.J := by
      have hFP := (hPhi.rooted.2 P hPt).mono hPhiU
      rw [hfr] at hrootP hFP ⊢
      change ¬ Anc (tr.HonestBlocks H) (tr.state y i).fg.fcRoot P at hrootP
      change Anc (tr.HonestBlocks H) (tr.state y i).fg.F P at hFP
      change (tr.state y i).fg.fcRoot = _
      unfold Store.fcRoot at hrootP ⊢
      split_ifs at hrootP ⊢ with hactive
      · rfl
      · exact False.elim (hrootP hFP)
    have hf : Hᶜ.ncard < sp.toParams.fg.q := by
      have hf := hp.faults
      have hn : 0 < sp.n := sp.toParams.hn
      change 3 * Hᶜ.ncard ≤ sp.n - 1 at hf
      change Hᶜ.ncard < (2 * sp.n + 2) / 3
      omega
    obtain ⟨x, hx, r, hri, d, _, att, ell', C, _, _, _, _, hto, _, hJx, hJC, _, hCh, hPh⟩ :=
      Healing.cache_ahead_report hp.run hp.noColl hf hy (Or.inr hJ) hPy hPR hne
    have hPx := hp.mem_tree_of_anc hx hPR hJx
    have hσ := hp.σ_eq_run hy hx hPy hPx
    exact Or.inr ⟨x, hx, r, ell', C, hri, hto, hPR.trans hJC, by
      rw [← hσ, hCh]
      exact hPh⟩

/-- A deepest block of `T` lying in `S ⊆ T` is the deepest block of `S`. -/
theorem deepest_of_subset {FGP : Type} {Φ : AC.Frm sp.n FGP}
    {S T : Set (AC.Blk sp.n FGP)} {D : AC.Blk sp.n FGP} (hT : AC.deepest Φ T = some D)
    (hST : S ⊆ T) (hD : D ∈ S) : AC.deepest Φ S = some D := by
  have h : AC.IsDeepest Φ S D := ⟨hD, fun C hC hne => (AC.deepest_mem hT).2 C (hST hC) hne⟩
  cases hd : AC.deepest Φ S with
  | none =>
    unfold AC.deepest at hd
    simp only [show ∃ B, AC.IsDeepest Φ S B from ⟨D, h⟩, ↓reduceDIte, reduceCtorEq] at hd
  | some D' =>
    have h' := AC.deepest_mem hd
    by_contra hne
    have hne' : D' ≠ D := fun h => hne (congrArg some h)
    rcases h.2 D' h'.1 hne' with h₁ | ⟨h₁, h₂⟩ <;>
      rcases h'.2 D h.1 (Ne.symm hne') with h₃ | ⟨h₃, h₄⟩ <;> omega

/-- Full viability makes the newly selected fast lock an exact toFG candidate,
including the second normalization by liveLocks at the adjacent call. -/
theorem candidate_after_fast_update {A : AC.ACState sp.n} {Phi : AC.Frm sp.n FGP}
    (hPhi : FrameOK Phi) {t : Time} {u : Nat} {P : AC.Blk sp.n FGP}
    (hPv : P ∈ Phi.viableTree Phi.tree)
    (hconf : AC.getConfirmation sp A Phi u = some P)
    (hnv : ¬ AC.conflictsWithLock sp A.locks Phi t P)
    (hfast : AC.fastSelect sp A Phi u P = some P)
    (_hlive : sp.slot t ≤ u + sp.k) (hage : sp.slot t ≤ u + 2) :
    P ∈ AC.toFGCandidates sp (AC.updateConfirmation sp A Phi t u) Phi t := by
  have hself : Phi.viableAncestor P = P := AC.viableAncestor_self hPhi hPv.1 (Or.inl hPv)
  -- unvetoed, so the filtered fast selection is the raw one; its expiry is `fastExpiry ≥ u + 2`
  have hD := deepest_of_subset (S := {B | B ∈ {B | B ∈ AC.confirmationPath sp Phi P ∧
      ¬ AC.conflictsWithLock sp A.locks Phi t B} ∧ AC.FastTest sp A Phi u B}) hfast
    (fun B hB => ⟨hB.1.1, hB.2⟩)
    ⟨⟨(AC.deepest_mem hfast).1.1, hnv⟩, (AC.deepest_mem hfast).1.2⟩
  have hlock : ∃ e, sp.slot t ≤ e ∧ (⟨P.root, u, true, e⟩ : AC.Lock) ∈
      (AC.updateConfirmation sp A Phi t u).locks := by
    unfold AC.updateConfirmation
    simp only [hconf]
    rw [ite_eq_right hnv]
    exact ⟨_, hage.trans (AC.le_fastExpiry sp _ _ _ _), ⟨P.root, u, true, _⟩,
      Or.inr ⟨_, Or.inl ⟨P, hD, rfl⟩, rfl⟩, P, hPv.1, rfl,
      hage.trans (AC.le_fastExpiry sp _ _ _ _), by rw [hself]⟩
  obtain ⟨e, he, hlock⟩ := hlock
  exact ⟨hPv, ⟨P.root, u, true, e⟩, ⟨⟨P.root, u, true, e⟩, hlock, P, hPv.1, rfl, he,
    by rw [hself]⟩, rfl, rfl, hage⟩

/-- The exact fast candidate persists into an adjacent call with the same frame
and timestamp; these are the equalities supplied by `update_toFG_calls`. -/
theorem candidate_at_adjacent_call
    {y : Fin sp.n} {j u : Nat} {ell ell' : ACLabel (goldilocksNode sp ro)}
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hc : tr.projAC.CallAt y j ell) (hPhi : FrameOK ell.frame)
    (hframe : ell'.frame = ell.frame) (htime : tr.time (j + 1) = tr.time j)
    (hPv : P ∈ ell.frame.viableTree ell.frame.tree)
    (hconf : AC.getConfirmation sp (tr.projAC.state y j) ell.frame u = some P)
    (hnv : ¬ AC.conflictsWithLock sp (tr.projAC.state y j).locks ell.frame (tr.time j) P)
    (hfast : AC.fastSelect sp (tr.projAC.state y j) ell.frame u P = some P)
    (hpost : tr.projAC.post j =
      AC.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u)
    (hlive : sp.slot (tr.time j) ≤ u + sp.k) (hage : sp.slot (tr.time j) ≤ u + 2) :
    P ∈ AC.toFGCandidates sp (tr.projAC.state y (j + 1)) ell'.frame (tr.time (j + 1)) := by
  rw [tr.projAC.state_succ_of_call hc, hpost, hframe, htime]
  exact candidate_after_fast_update hPhi hPv hconf hnv hfast hlive hage

/-- A full viable unanimous pool at an actual update produces an actual report
at or before the adjacent toFG call, not merely a selected candidate. -/
theorem report_of_viable_unanimous_pool {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {j u : Nat}
    {ell ell' : ACLabel (goldilocksNode sp ro)}
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hu : AC.UpdateAt tr.projAC y j u ell)
    (hc : tr.projAC.CallAt y (j + 1) ell') (hto : ell'.call = .toFG)
    (hframe : ell'.frame = ell.frame) (htime : tr.time (j + 1) = tr.time j)
    (hjoin : AC.joined sp (tr.projAC.state y (j + 1)) (tr.time (j + 1)))
    (hPg : P.root ≠ sp.genesisRoot) (hPv : P ∈ ell.frame.viableTree ell.frame.tree)
    (hu1 : sp.slot (AC.gbar g) + 1 ≤ u)
    (hpool : ∀ v ∈ H, v ∈ K.committee u → ∃ vote ∈ (tr.projAC.state y j).pool u,
      vote.val = v ∧ vote.head = P.root ∧
      AC.resolutionTime (tr.projAC.state y j) ell.frame vote < AC.ETime.of (sp.ts u + 2 * sp.Δ) ∧
      ∀ vote' ∈ (tr.projAC.state y j).pool u, vote'.val = v → vote' = vote)
    (hlocks : ∀ L ∈ AC.liveLockBlocks sp (tr.projAC.state y j).locks ell.frame (tr.time j),
      Compatible (tr.HonestBlocks H) L P)
    (hnext : ∀ C ∈ AC.toFGCandidates sp (tr.projAC.state y (j + 1)) ell'.frame (tr.time (j + 1)),
      Compatible (tr.HonestBlocks H) C P)
    (hlive : sp.slot (tr.time j) ≤ u + sp.k) (hage : sp.slot (tr.time j) ≤ u + 2) :
    ∃ r e R, AC.ToFGAt tr.projAC y r e R ∧ tr.time r ≤ tr.time (j + 1) ∧
      Anc (tr.HonestBlocks H) P R := by
  obtain ⟨hconf, hnv, hfast, hpost, _⟩ :=
    hp.ready_update_selection_of_pool hy hu1 hu hPv.1 hPg hpool hlocks
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  have hPc := candidate_at_adjacent_call hu.1 (AC.frameIn_of_callAt hr hy hu.1).1
    hframe htime hPv hconf hnv hfast hpost hlive hage
  exact Healing.report_of_compatible_candidate_of_run hp.run hp.noColl hy hc hto hjoin hPg hPc hnext

/-- An honest node retains its unanimous vote head at a later call whenever
that call's finality is still below the head. -/
theorem unanimous_head_held_at_call {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H)
    (hun : ∀ y ∈ H, ∀ j e, AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b) (hFP : Anc (tr.HonestBlocks H) (tr.state y j).fg.F P) :
    P ∈ ell.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  have hΔ := sp.toParams.hΔ
  have hub : sp.ts u + sp.Δ ≤ b := by linarith
  -- an honest slot-`u` voter holds `P` by `t_u + Δ`; the relay reaches `y` by `t_u + 2Δ`
  obtain ⟨z, hz, q, e, ⟨ellv, hv⟩, hs, hq⟩ := exists_honest_vote_in_slot hp hc hR hub
  obtain ⟨⟨Hd, hHd, he, _⟩, _⟩ := Compose.cast_head_fcRoot hr hp.run.vstart hz hv
  have heq : Hd = P := hr.coherent.1 ((AC.frameIn_of_callAt hr hz hv.1).2 hHd) hP
    (he.trans (hun z hz q e ⟨ellv, hv⟩ (hq.trans hub) hs))
  rw [heq] at hHd
  have hg' := slotAfter_add_le_of_drain hp hR
  rw [Healing.gbar_slotAfter] at hg'
  have hF : Anc (tr.HonestBlocks H) ell.frame.F P := by
    rw [Compose.frame_of_projAC hp.run hy hcall]
    exact hFP
  exact hp.reset_frame_relay hc hz hy hv.1 hcall hHd hjb (by linarith) (by linarith)
    (by linarith) hF

/-- At the update deadline, finality below the unanimous head gives full
viability or an actual higher report. Holding and the high seed are derived. -/
theorem unanimous_viable_or_higher_report {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y ∈ H, ∀ j e, AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) (ht : tr.time j = sp.ts u + 6 * sp.Δ)
    (hFP : Anc (tr.HonestBlocks H) (tr.state y j).fg.F P) :
    P ∈ ell.frame.viableTree ell.frame.tree ∨
      ∃ x ∈ H, ∃ r e C, r < j ∧ AC.ToFGAt tr.projAC x r e C ∧
        tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P C ∧
        ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h := by
  have hjb : tr.time j ≤ b := ht ▸ hTb
  have hPt := unanimous_head_held_at_call hp hc hP hun hgu hR hy hcall
    (by rw [ht]; linarith [sp.toParams.hΔ]) hjb hFP
  obtain ⟨v, q, m, S, ho, hqb, _, hqt⟩ := hp.reset_seed_before_slot hR
  have hSP := high_origins_before_next_slot_below hp hc hP hun hgu hR
    (by linarith [sp.toParams.hΔ]) ho hqt hqb
  have hcompare : ∀ x r l B, r < j → Healing.HighOrigin tr H g x r l B →
      Compatible (tr.HonestBlocks H) P B := by
    intro x r l B hrj horig
    exact (high_origin_compatible_before_update hp hc hP hslot hu hun hgu hR hTb
      horig ((hp.run.time_mono hrj.le).trans ht.le)).symm
  rcases held_target_viable_or_higher_report hp hy hcall hjb hPt ho hqb hSP hcompare with
    hv | ⟨x, hx, r, e, C, hrj, hto, hPC, hh⟩
  · exact Or.inl hv
  · exact Or.inr ⟨x, hx, r, e, C, hrj, hto, (hp.run.time_mono hrj.le).trans ht.le, hPC, hh⟩

/-- Finite report duty from actual unanimity: each honest node reports above P
by the update deadline, unless an honest strict-higher report already exists. -/
theorem report_cover_of_unanimous {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hPg : P.root ≠ sp.genesisRoot)
    (hun : ∀ y ∈ H, ∀ j e, AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b) :
    (∀ y ∈ H, ∃ r e R, AC.ToFGAt tr.projAC y r e R ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P R) ∨
    (∃ x ∈ H, ∃ r e C, AC.ToFGAt tr.projAC x r e C ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h) := by
  classical
  by_cases hescape : ∃ x ∈ H, ∃ r e C, AC.ToFGAt tr.projAC x r e C ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h
  · exact Or.inr hescape
  left
  intro y hy
  have hd := sp.toParams.hΔ
  have hub : sp.ts u + sp.Δ ≤ b := by linarith only [hTb, hd]
  have hjoin : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) ≤ sp.ts u := by
    have hbase := (AC.ts_le_iff_le_slot sp (AC.gbar_nonneg g) (sp.slot (AC.gbar g))).2 (by rfl)
    simp only [AC.ACParams.ts] at hbase ⊢
    simp only [AC.ACParams.ts] at hgu
    push_cast at hbase hgu ⊢
    linarith only [hbase, hgu]
  obtain ⟨j, ell, ell', hup, hto, htoeq, hnexttime, hframe, hjoined⟩ :=
    hp.update_toFG_calls hy hjoin hTb
  have hjtime : tr.time j = sp.ts u + 6 * sp.Δ := hup.2.2.1
  have hjb : tr.time j ≤ b := hjtime ▸ hTb
  have hnextb : tr.time (j + 1) ≤ b := hnexttime ▸ hTb
  have hRT : Healing.drainTime sp a ≤ sp.ts u + 6 * sp.Δ := by
    simp only [AC.ACParams.ts] at hR ⊢
    push_cast at hR ⊢
    linarith only [hR, hd]
  have hca := Healing.cutZ_lt_reset_of_snapshot hp.run
    (by obtain ⟨k, hk, -⟩ := hp.snapshot; exact ⟨k, hk⟩) hp.reset
  have ha0 : 0 ≤ a := by
    have h1 := Healing.lt_cutZ sp g
    have h2 := AC.gbar_nonneg g
    linarith only [h1, h2, hca, hd]
  have haT : a ≤ sp.ts u + 6 * sp.Δ := by
    have hanext : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
      have := (AC.ts_le_iff_le_slot sp ha0 _).1 h
      omega
    have hle : sp.ts ((sp.slot a : Int) + 1) ≤ Healing.drainTime sp a := by
      rw [Healing.drainTime_eq]
      exact (AC.ts_le_iff sp).2 (by push_cast; omega)
    exact (hanext.le.trans hle).trans hRT
  have hFP : Anc (tr.HonestBlocks H) (tr.state y j).fg.F P := by
    rcases finality_alternative_before_update hp hc hP hslot hu hun hgu hR hTb hy
        (hjtime ▸ haT) hjtime.le with h | ⟨x, hx, r, e, C, _, hto, ht, hPC, hh⟩
    · exact h
    · exact False.elim (hescape ⟨x, hx, r, e, C, hto, ht, hPC, hh⟩)
  have hPv : P ∈ ell.frame.viableTree ell.frame.tree := by
    rcases unanimous_viable_or_higher_report hp hc hP hslot hu hun hgu hR hTb hy
        hup.1 hjtime hFP with h | ⟨x, hx, r, e, C, _, hto, ht, hPC, hh⟩
    · exact h
    · exact False.elim (hescape ⟨x, hx, r, e, C, hto, ht, hPC, hh⟩)
  have hpool := unanimous_pool hp hc hun hR hy hup.1
    (by rw [hjtime]; linarith only [hd]) hjb hPv.1
  have hts : Healing.cutZ sp.toParams g ≤ sp.ts u := by
    have hk := sp.two_le_k
    apply hp.clean_window_timing (s := u) ?_ u (by omega)
    rw [Healing.cleanLabel_eq]
    rw [Healing.drainTime_eq] at hR
    have := (AC.ts_le_iff sp).1 hR
    push_cast at this
    omega
  obtain ⟨z, hz, q, e, ⟨ellv, hv⟩, hs, hq⟩ := exists_honest_vote_in_slot hp hc hR hub
  have hvote : ∃ z ∈ H, ∃ q ell e, AC.CastAt tr.projAC z q ell e ∧
      tr.time q ≤ b ∧ e.msg.slot = u := ⟨z, hz, q, ellv, e, hv, hq.trans hub, hs⟩
  have hlocks := hp.call_locks_compatible_of_unanimous hc hP hts hun hvote hy hup.1 hjb
    (hjtime ▸ hRT) hjtime.le (fun r hr B CV ho =>
      unanimous_next_optimistic_compatible hp hc hP hslot hu hun hgu hR hub hy ho
        ((hp.run.time_mono hr.le).trans hjb))
  have hnextlocks := hp.call_locks_compatible_of_unanimous hc hP hts hun hvote hy hto hnextb
    (hnexttime ▸ hRT) hnexttime.le (fun r hr B CV ho =>
      unanimous_next_optimistic_compatible hp hc hP hslot hu hun hgu hR hub hy ho
        ((hp.run.time_mono hr.le).trans hnextb))
  have hsl : sp.slot (tr.time j) = u + 1 := by
    rw [hjtime]
    apply AC.slot_of_mem sp (u + 1)
    · simp only [AC.ACParams.ts]; push_cast; linarith only [hd]
    · simp only [AC.ACParams.ts]; push_cast; linarith only [hd]
  obtain ⟨r, e, R, hr, ht, hPR⟩ := report_of_viable_unanimous_pool hp hy hup hto htoeq
    hframe (hnexttime.trans hjtime.symm) hjoined hPg hPv (Healing.slot_gbar_lt_of_cutZ_le hts)
    hpool hlocks
    (fun C hC => by
      obtain ⟨hCv, l, hl, he, _⟩ := hC
      exact hnextlocks C ⟨hCv.1, l, hl, he⟩)
    (by rw [hsl]; have := sp.two_le_k; omega) (by rw [hsl]; omega)
  exact ⟨r, e, R, hr, ht.trans hnexttime.le, hPR⟩

/-- Operational C2 discharges the unanimous-vote input of finite report coverage. -/
theorem report_cover_of_proposal {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P)
    (hP : P ∈ tr.HonestBlocks H) (hslot : P.slot = u) (hu : 0 < u)
    (hPg : P.root ≠ sp.genesisRoot)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hTb : sp.ts u + 6 * sp.Δ ≤ b) :
    (∀ y ∈ H, ∃ r e R, AC.ToFGAt tr.projAC y r e R ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P R) ∨
    (∃ x ∈ H, ∃ r e C, AC.ToFGAt tr.projAC x r e C ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h) := by
  have hun := hp.operational_unanimous hc hpH hdesignated hactual hslot hR
    (show sp.ts u ≤ b by linarith [sp.toParams.hΔ])
  exact report_cover_of_unanimous hp hc hP hslot hu hPg
    (fun y hy j e hv hjb hs => hun y hy j e hv hs hjb) hgu
    (hR.trans ((AC.ts_le_iff sp).2 (by push_cast; omega))) hTb

end UpTo

end CoveredEndpoint

end Consensus.Goldilocks.Obligations
end
