module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Bounded clean-source comparisons and vote retention -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams ReplayOrder Payload Vote)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {K : AC.CommitteeDict sp.n} {g ΔF a b : Time}

/-- The Catch deadline `ḡ + 2Δ` from `ḡ ≤ x`. -/
private theorem catch_time_le {x : Time} (h : AC.gbar g ≤ x) :
    AC.gbar g + 2 * sp.Δ ≤ x + 3 * sp.Δ :=
  add_le_add h (mul_le_mul_of_nonneg_right (by norm_num) sp.toParams.hΔ.le)

/-- Finite same-label comparison with either kind of actual raw source. -/
theorem ResetPremisesUpTo.result_source_compatible
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r q s : Nat}
    {C D : AC.Blk sp.n (List (FG.Att sp.n))} {CV DV : Set (Vote sp.n)}
    (hR : AC.ResultAt tr.projAC x r s C CV)
    (hD : AC.ResultAt tr.projAC y q s D DV ∨ AC.OptimisticLockAt tr.projAC y q s D DV)
    (hrb : tr.time r ≤ b) (hqb : tr.time q ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts s) :
    Compatible (tr.HonestBlocks H) C D := by
  have hac := Compose.goldilocks_ac_projection_from hp.run hp.noColl
  have hsync := sync_window_of_service hp.run hp.sync
  have hgs : AC.gbar g ≤ sp.ts s := gbar_le_of_cutZ_le sp hts
  have hreset : ∀ z ∈ H, ∀ c, tr.time c ≤ b → tr.projAC.RestartAt z c →
      tr.time c ≤ sp.ts s := by
    intro z hz c hcb hrest
    apply (restart_le_before hp hz (Compose.projAC_restartAt.mp hrest) hcb).trans
    have hh := (AC.ts_le_iff sp).mp ((cutZ_eq sp g) ▸ hts)
    exact (AC.ts_le_iff sp).mpr (by omega)
  rcases hD with hD | hD
  · apply AC.result_result_compatible_window_before hac hsync hgs hx hy hR hD hrb hqb
    intro z hz c hle hrest
    apply hreset z hz c ((hp.run.time_mono hle).trans ?_) hrest
    rcases le_total r q with h | h
    · simpa only [max_eq_right h] using hqb
    · simpa only [max_eq_left h] using hrb
  · exact AC.result_optimistic_compatible_window_before_of_voters hac hsync hgs hx hy hR hD hrb
      (fun c hle hrest => hreset x hx c ((hp.run.time_mono hle).trans hrb) hrest)
      ((Set.ncard_le_ncard (t := K.committee s) (by
        rintro _ ⟨v, hv, rfl⟩; exact hp.hP.1 x hx r s v hv)).trans (hp.hsize s).le)

/-- Two optimistic sources of one label need no service after either source cut. -/
theorem ResetPremisesUpTo.optimistic_sources_compatible
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r q s : Nat}
    {C D : AC.Blk sp.n (List (FG.Att sp.n))} {CV DV : Set (Vote sp.n)}
    (hs1 : sp.slot (AC.gbar g) + 1 ≤ s)
    (hC : AC.OptimisticLockAt tr.projAC x r s C CV)
    (hD : AC.OptimisticLockAt tr.projAC y q s D DV) :
    Compatible (tr.HonestBlocks H) C D := by
  have hrun := Compose.goldilocks_ac_projection_from hp.run hp.noColl
  have hr := hrun.localRun
  obtain ⟨ell, A, hpt, hsl, hsel, _⟩ := hC
  obtain ⟨ell', A', hpt', hsl', hsel', _⟩ := hD
  have hU := (AC.frameIn_of_callAt hr hx hpt.1).2
  have hU' := (AC.frameIn_of_callAt hr hy hpt'.1).2
  unfold AC.optimisticSelect at hsel hsel'
  dsimp only at hsel hsel'
  split_ifs at hsel
  split_ifs at hsel'
  have h34 := (AC.deepest_mem hsel).1.2.1
  have h34' := (AC.deepest_mem hsel').1.2.1
  rw [hsl] at h34
  rw [hsl'] at h34'
  have hI := Set.ncard_inter_add_ncard_union (AC.optimisticVoters sp A ell.frame s C)
    (AC.optimisticVoters sp A' ell'.frame s D)
  have hKC : AC.optimisticVoters sp A ell.frame s C ⊆ K.committee s := by
    rintro _ ⟨v, hv, rfl, -⟩; exact hp.hP.2 x hx r ell A hpt s v (hsl ▸ hv)
  have hKD : AC.optimisticVoters sp A' ell'.frame s D ⊆ K.committee s := by
    rintro _ ⟨v, hv, rfl, -⟩; exact hp.hP.2 y hy q ell' A' hpt' s v (hsl' ▸ hv)
  have hle := (Set.ncard_le_ncard (Set.union_subset hKC hKD)).trans (hp.hsize s).le
  have hf := hp.cs2 hs1
  obtain ⟨z, ⟨⟨v, hv, rfl, R, hR, hRr, hCR⟩,
      ⟨v', hv', hvz, R', hR', hRr', hDR⟩⟩, hz⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (s := K.committee s ∩ Hᶜ)
      (t := AC.optimisticVoters sp A ell.frame s C ∩
        AC.optimisticVoters sp A' ell'.frame s D) (by omega)
  have hz : v.val ∈ H := by
    by_contra hn
    exact hz ⟨hKC ⟨v, hv, rfl, R, hR, hRr, hCR⟩, hn⟩
  obtain ⟨hvs, i, _, e, he, rfl⟩ := AC.optimisticPoint_pool_voteU hrun.toU hx hpt hv hz
  obtain ⟨hvs', i', _, e', he', rfl⟩ :=
    AC.optimisticPoint_pool_voteU hrun.toU hy hpt' hv' (hvz ▸ hz)
  rw [hvz] at he'
  obtain ⟨_, rfl⟩ := (AC.one_vote_per_slotU sp) _ ro H _ _ hr.toU _ hz i i' e e' he he'
    (hvs.trans hvs'.symm)
  obtain rfl : R = R' := hr.coherent.1 (hU hR) (hU' hR') (hRr.trans hRr'.symm)
  exact AC.anc_total hr.coherent (hCR.mono hU) (hDR.mono hU')

/-- Same-label bounded raw sources compare without any high-origin hypothesis. -/
theorem ResetPremisesUpTo.sources_same_label_compatible
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r q s : Nat}
    {C D : AC.Blk sp.n (List (FG.Att sp.n))} {CV DV : Set (Vote sp.n)}
    (hC : AC.ResultAt tr.projAC x r s C CV ∨ AC.OptimisticLockAt tr.projAC x r s C CV)
    (hD : AC.ResultAt tr.projAC y q s D DV ∨ AC.OptimisticLockAt tr.projAC y q s D DV)
    (hrb : tr.time r ≤ b) (hqb : tr.time q ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts s) :
    Compatible (tr.HonestBlocks H) C D := by
  rcases hC with hC | hC
  · exact hp.result_source_compatible hx hy hC hD hrb hqb hts
  rcases hD with hD | hD
  · exact (hp.result_source_compatible hy hx hD (Or.inr hC) hqb hrb hts).symm
  · exact hp.optimistic_sources_compatible hx hy (slot_gbar_lt_of_cutZ_le hts) hC hD

/-- An optimistic source has an actual honest supporting vote no later than its write. -/
theorem ResetPremisesUpTo.optimistic_supporter
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {x : Fin sp.n} (hx : x ∈ H) {r s : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hs1 : sp.slot (AC.gbar g) + 1 ≤ s) (hop : AC.OptimisticLockAt tr.projAC x r s B CV) :
    B ∈ (tr.state x r).fg.tree ∧ ∃ z ∈ H, ∃ q ≤ r, ∃ e,
      AC.VoteAt tr.projAC z q e ∧ e.msg.slot = s ∧
      AC.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hrun := Compose.goldilocks_ac_projection_from hp.run hp.noColl
  obtain ⟨ell, A, hpt, hsl, hsel, _⟩ := hop
  have hU := (AC.frameIn_of_callAt hrun.localRun hx hpt.1).2
  unfold AC.optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  refine ⟨hp.frame_tree_subset hx hpt.1 (AC.deepest_mem hsel).1.1, ?_⟩
  have h34 := (AC.deepest_mem hsel).1.2.1
  rw [hsl] at h34
  have hK : AC.optimisticVoters sp A ell.frame s B ⊆ K.committee s := by
    rintro _ ⟨v, hv, rfl, -⟩; exact hp.hP.2 x hx r ell A hpt s v (hsl ▸ hv)
  have hf := hp.cs2 hs1
  obtain ⟨z, ⟨v, hv, rfl, R, hR, hRr, hBR⟩, hz⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (s := K.committee s ∩ Hᶜ)
      (t := AC.optimisticVoters sp A ell.frame s B) (by omega)
  have hvH : v.val ∈ H := by
    by_contra hn
    exact hz ⟨hK ⟨v, hv, rfl, R, hR, hRr, hBR⟩, hn⟩
  obtain ⟨hvs, q, hqr, e, he, rfl⟩ :=
    AC.optimisticPoint_pool_voteU hrun.toU hx hpt (hsl ▸ hv) hvH
  exact ⟨_, hvH, q, hqr, e, he, hvs.trans hsl, R, hU hR, hRr, hBR.mono hU⟩

/-- Finite fast-source transfer, with its prospective domain supplied at earlier cuts. -/
theorem ResetPremisesUpTo.fast_source_votes_of_domain_before
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} (hx : x ∈ H) {r s : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfast : AC.FastLockAt tr.projAC x r s B CV) (hts : cutZ sp.toParams g ≤ sp.ts s)
    (hdomain : ∀ y ∈ H, ∀ i ell e, AC.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → s < e.msg.slot →
      (∀ z ∈ H, ∀ q < i, ∀ e', AC.VoteAt tr.projAC z q e' →
        s < e'.msg.slot → AC.VoteExtends (tr.HonestBlocks H) e'.msg B) →
      Anc (tr.HonestBlocks H) B ell.frame.fcRoot ∨
        B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot)) :
    ∀ i, tr.time i ≤ b → ∀ y ∈ H, ∀ ell e, AC.CastAt tr.projAC y i ell e →
      s < e.msg.slot → AC.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hac := Compose.goldilocks_ac_projection_from hp.run hp.noColl
  have hr := hac.localRun
  have hsync := sync_window_of_service hp.run hp.sync
  have hcatch := catch_window_of_run (b := b) hp.run hc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hgs : AC.gbar g ≤ sp.ts s := gbar_le_of_cutZ_le sp hts
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
    · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, _⟩ := Compose.cast_head_fcRoot hr
        hp.run.vstart hy hcast
      exact ⟨Hd, hΦU hHd, hHdr, hBF.trans (hfHd.mono hΦU)⟩
    have hFB := (hΦ.rooted.2 B hv.1.1).mono hΦU
    have hslot := (AC.castAt_specU hr.toU hy hcast).2.1
    have htime : sp.ts e.msg.slot ≤ tr.time i :=
      (AC.ts_le_iff_le_slot sp (hr.time_nonneg i) _).mpr (by rw [← hslot])
    have hcut : cutZ sp.toParams g ≤ tr.time i :=
      hts.trans (((AC.ts_le_iff sp).mpr (by omega)).trans htime)
    by_cases hfirst : e.msg.slot = s + 1
    · have carry : AC.CarryAt tr.projAC (tr.HonestBlocks H) y i e s CV := by
        apply Compose.carryAt_of_writer_window_before hr hp.run.vstart
          (AC.serviceWindowBefore_of_sync hsync) hgs hcatch (catch_time_le hgs) hx hy hcast hfirst
          hib
        intro v hv
        obtain ⟨hvs, hw, D, hD, hDr, hBD, ha⟩ :=
          fastLock_writer hr hp.run.vstart hx hfast v hv
        exact ⟨hvs, hw, D, hD, hDr, hFB.trans hBD, ha⟩
      apply AC.first_transfer_storedU sp hac.toU K hp.hP hp.hT hp.hsize hx hfast .refl hy hcast
        hfirst (hp.sync.syncAC hp.run ((AC.le_gbar g).trans hgs)) carry
        (hp.faultBoundK_late hs1 hcut hib) (hp.cs2 (by omega))
      · rw [← hfirst]; exact Or.inl hv
      · exact fun z hz q hq e' he hslot => hprior z hz q hq e' he (by omega)
    · obtain ⟨m, hm⟩ : ∃ m, e.msg.slot = m + 1 := ⟨e.msg.slot - 1, by omega⟩
      have hone : ∀ v ∈ Compose.honestVotes tr H m,
          AC.CarryAt tr.projAC (tr.HonestBlocks H) y i e m {v} := by
        rintro v ⟨z, hz, q, e', ⟨ell', hc'⟩, rfl, hsl⟩
        have hqi : q < i := by
          by_contra hn
          have := AC.slot_mono sp (hr.time_nonneg i) (hr.time_mono (Nat.le_of_not_gt hn))
          have := (AC.castAt_specU hr.toU hz hc').2.1
          omega
        obtain ⟨Hv, hHv, hHvr, hBHv⟩ := hprior z hz q hqi e' ⟨ell', hc'⟩ (by omega)
        obtain ⟨⟨Hd, hHd, hHdr, _⟩, hqt⟩ := Compose.cast_head_fcRoot hr
            hp.run.vstart hz hc'
        obtain rfl : Hd = Hv := hr.coherent.1 ((AC.frameIn_of_callAt hr hz hc'.1).2 hHd)
          hHv (hHdr.trans hHvr.symm)
        have hgm := hgs.trans ((AC.ts_le_iff sp).mpr (show (s : Int) ≤ m by omega))
        apply Compose.carryAt_of_writer_window_before hr hp.run.vstart
          (AC.serviceWindowBefore_of_sync hsync) hgm hcatch (catch_time_le hgm) hz hy hcast hm hib
        rintro v rfl
        have ht : tr.projAC.time q < sp.ts m + 2 * sp.Δ := by
          rw [hsl] at hqt
          exact hqt.trans_lt (add_lt_add_of_le_of_lt le_rfl (lt_two_mul_self hΔ))
        refine ⟨hsl, ⟨q, ⟨ell', hc'.1, Or.inl ⟨e', hc'.2, rfl⟩⟩,
          (AC.ts_le_iff_le_slot sp (hr.time_nonneg q) m).mpr
            (by rw [← (AC.castAt_specU hr.toU hz hc').2.1, hsl]), ht⟩,
          Hd, hHv, hHvr, hFB.trans hBHv, ?_⟩
        rcases Compose.frame_anc_acceptedU hr.toU hz q ell' hc'.1 Hd hHd Hd .refl
            with hg | ⟨k, hk, ha⟩
        · exact Or.inl hg
        · exact Or.inr ⟨k, ha, (hr.time_mono hk).trans_lt ht⟩
      have hmt : sp.ts m + sp.Δ ≤ b := by
        rw [hm] at htime
        simp only [AC.ACParams.ts] at htime ⊢; push_cast at htime; linarith
      refine AC.next_vote_extends_before hac K hp.hP hp.hT hp.hsize hy hcast hm
        (fun z hz q hq e' he hsl => hprior z hz q hq e' he (by rcases hsl with h | h <;> omega))
        (hp.half_committee (hts.trans ((AC.ts_le_iff sp).mpr (by omega))) hmt)
        ⟨hr.awake_of_call y hy i ell hcast.1, (AC.castAt_specU hr.toU hy hcast).2.2.1,
          fun v hv => (hone v hv).heads v rfl, fun v hv => (hone v hv).holds v rfl⟩
        (hp.faultBoundK_late (by omega) hcut hib) (hp.cs2 (by omega))
        (hp.sync.syncAC hp.run ((AC.le_gbar g).trans
          (hgs.trans ((AC.ts_le_iff sp).mpr (by omega))))) ?_
      rw [← hm]
      exact Or.inl hv

end Consensus.Goldilocks.Healing

end
