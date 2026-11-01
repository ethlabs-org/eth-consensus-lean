module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction

public section

/-! # Bounded clean-source comparisons and vote retention -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- A clean-label bound places the whole slow window after the high-origin cutoff. -/
theorem ResetPremisesUpTo.clean_window_timing
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {s : Nat}
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) :
    ∀ j : Nat, (s : Int) - sp.k < j → cutZ sp.toParams g ≤ sp.ts j := by
  obtain ⟨v, r, l, O, ho, _, hl⟩ := hp.reset_seed
  rw [cleanLabel_eq] at hs
  intro j hj
  exact (hp.cutZ_le_ts_of_highOrigin ho).trans ((SA.ts_le_iff sp).mpr (by omega))

/-- Finite same-label comparison with either kind of actual raw source. -/
theorem ResetPremisesUpTo.result_source_compatible
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r q s : Nat}
    {C D : SA.Blk sp.n (List (FG.Att sp.n))} {CV DV : Set (Vote sp.n)}
    (hR : SA.ResultAt tr.projAC x r s C CV)
    (hD : SA.ResultAt tr.projAC y q s D DV ∨ SA.OptimisticLockAt tr.projAC y q s D DV)
    (hrb : tr.time r ≤ b) (hqb : tr.time q ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts s) :
    Compatible (tr.HonestBlocks H) C D := by
  have hS := healthy_base_of_reset_catch_before hp hc
  have hgs : SA.gbar g ≤ sp.ts s := by
    have := lt_cutZ sp g
    have := sp.toParams.hΔ
    linarith
  have hreset : ∀ z ∈ H, ∀ c, tr.time c ≤ b → tr.projAC.RestartAt z c →
      tr.time c ≤ sp.ts s := by
    intro z hz c hcb hrest
    apply (restart_le_before hp hz (Compose.projAC_restartAt.mp hrest) hcb).trans
    have hh := (SA.ts_le_iff sp).mp ((cutZ_eq sp g) ▸ hts)
    exact (SA.ts_le_iff sp).mpr (by omega)
  rcases hD with hD | hD
  · apply SA.result_result_compatible_window_before hS.run hS.sync hgs hx hy hR hD hrb hqb
    intro z hz c hle hrest
    apply hreset z hz c ((hp.run.time_mono hle).trans ?_) hrest
    rcases le_total r q with h | h
    · simpa only [max_eq_right h] using hqb
    · simpa only [max_eq_left h] using hrb
  · exact SA.result_optimistic_compatible_window_before hS.run hS.sync hgs hx hy hR hD
      hrb hqb (fun c hle hrest => hreset x hx c ((hp.run.time_mono hle).trans hrb) hrest)

/-- Two optimistic sources of one label need no service after either source cut. -/
theorem ResetPremisesUpTo.optimistic_sources_compatible
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r q s : Nat}
    {C D : SA.Blk sp.n (List (FG.Att sp.n))} {CV DV : Set (Vote sp.n)}
    (hC : SA.OptimisticLockAt tr.projAC x r s C CV)
    (hD : SA.OptimisticLockAt tr.projAC y q s D DV) :
    Compatible (tr.HonestBlocks H) C D := by
  have hrun := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hrun.localRun
  obtain ⟨ell, A, hpt, hsl, hsel, _⟩ := hC
  obtain ⟨ell', A', hpt', hsl', hsel', _⟩ := hD
  have hU := (SA.frameIn_of_callAt hr hx hpt.1).2
  have hU' := (SA.frameIn_of_callAt hr hy hpt'.1).2
  unfold SA.optimisticSelect at hsel hsel'
  dsimp only at hsel hsel'
  split_ifs at hsel
  split_ifs at hsel'
  have h34 := (SA.deepest_mem hsel).1.2.1
  have h34' := (SA.deepest_mem hsel').1.2.1
  rw [hsl] at h34
  rw [hsl'] at h34'
  have hI := Set.ncard_inter_add_ncard_union (SA.optimisticVoters sp A ell.frame s C)
    (SA.optimisticVoters sp A' ell'.frame s D)
  have hle : (SA.optimisticVoters sp A ell.frame s C ∪
      SA.optimisticVoters sp A' ell'.frame s D).ncard ≤ sp.n :=
    (Set.ncard_le_ncard (Set.subset_univ _)).trans (by
      rw [Set.ncard_univ, Nat.card_fin])
  obtain ⟨z, ⟨⟨v, hv, rfl, R, hR, hRr, hCR⟩,
      ⟨v', hv', hvz, R', hR', hRr', hDR⟩⟩, hz⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
      (t := SA.optimisticVoters sp A ell.frame s C ∩
        SA.optimisticVoters sp A' ell'.frame s D) (by
          have := hp.faults
          have hn : sp.toParams.n = sp.n := rfl
          have := Fin.pos x
          omega)
  have hz := not_not.mp hz
  obtain ⟨hvs, i, _, e, he, rfl⟩ := SA.optimisticPoint_pool_vote hrun hx hpt hv hz
  obtain ⟨hvs', i', _, e', he', rfl⟩ :=
    SA.optimisticPoint_pool_vote hrun hy hpt' hv' (hvz ▸ hz)
  rw [hvz] at he'
  obtain ⟨_, rfl⟩ := (SA.one_vote_per_slot sp) _ ro H _ _ hr _ hz i i' e e' he he'
    (hvs.trans hvs'.symm)
  obtain rfl : R = R' := hr.coherent.1 (hU hR) (hU' hR') (hRr.trans hRr'.symm)
  exact SA.anc_total hr.coherent (hCR.mono hU) (hDR.mono hU')

/-- Same-label bounded raw sources compare without any high-origin hypothesis. -/
theorem ResetPremisesUpTo.sources_same_label_compatible
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r q s : Nat}
    {C D : SA.Blk sp.n (List (FG.Att sp.n))} {CV DV : Set (Vote sp.n)}
    (hC : SA.ResultAt tr.projAC x r s C CV ∨ SA.OptimisticLockAt tr.projAC x r s C CV)
    (hD : SA.ResultAt tr.projAC y q s D DV ∨ SA.OptimisticLockAt tr.projAC y q s D DV)
    (hrb : tr.time r ≤ b) (hqb : tr.time q ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts s) :
    Compatible (tr.HonestBlocks H) C D := by
  rcases hC with hC | hC
  · exact hp.result_source_compatible hc hx hy hC hD hrb hqb hts
  rcases hD with hD | hD
  · exact (hp.result_source_compatible hc hy hx hD (Or.inr hC) hqb hrb hts).symm
  · exact hp.optimistic_sources_compatible hx hy hC hD

/-- An optimistic source has an actual honest supporting vote no later than its write. -/
theorem ResetPremisesUpTo.optimistic_supporter
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x : Fin sp.n} (hx : x ∈ H) {r s : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hop : SA.OptimisticLockAt tr.projAC x r s B CV) :
    B ∈ (tr.state x r).fg.tree ∧ ∃ z ∈ H, ∃ q ≤ r, ∃ e,
      SA.VoteAt tr.projAC z q e ∧ e.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hrun := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  obtain ⟨ell, A, hpt, hsl, hsel, _⟩ := hop
  have hU := (SA.frameIn_of_callAt hrun.localRun hx hpt.1).2
  unfold SA.optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  refine ⟨hp.frame_tree_subset hx hpt.1 (SA.deepest_mem hsel).1.1, ?_⟩
  have h34 := (SA.deepest_mem hsel).1.2.1
  obtain ⟨z, ⟨v, hv, rfl, R, hR, hRr, hBR⟩, hz⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
      (t := SA.optimisticVoters sp A ell.frame (sp.slot (tr.projAC.time r)) B) (by
        have := hp.faults
        have := Fin.pos x
        have hn : sp.toParams.n = sp.n := rfl
        omega)
  obtain ⟨hvs, q, hqr, e, he, rfl⟩ :=
    SA.optimisticPoint_pool_vote hrun hx hpt hv (not_not.mp hz)
  exact ⟨_, not_not.mp hz, q, hqr, e, he, hvs.trans hsl, R, hU hR, hRr, hBR.mono hU⟩

/-- The prospective vote domain of an optimistic source uses only earlier receiving cuts. -/
theorem ResetPremisesUpTo.optimistic_vote_domain_before
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r s i : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hop : SA.OptimisticLockAt tr.projAC x r s B CV)
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
  obtain ⟨hBx, z, hz, q, hqr, ev, hv, hvs, hVB⟩ := hp.optimistic_supporter hx hop
  have hqb := (hp.run.time_mono hqr).trans hrb
  obtain ⟨v, d, m, S, hseed, hdb, hm⟩ := hp.reset_seed
  have hms : m < s := by rw [cleanLabel_eq] at hs; omega
  have hts := hp.clean_window_timing hs s (by have := sp.two_le_k; omega)
  have hgs : SA.gbar g ≤ sp.ts s := by
    have := lt_cutZ sp g
    have := sp.toParams.hΔ
    linarith
  apply hp.held_target_vote_domain_before hx hy hBx hcast ?_ hseed (by omega)
    (hp.target_compatible_older_origin hseed hdb hz hv hqb hvs hms hVB) ?_ ?_ ?_
  · intro hF
    exact raw_writer_voterBlockTree_window_before hr hS.sync hS.catchUp hx hy
      (Or.inr (Or.inr hop)) .refl hcast (by omega) hib (by
        have := (SA.ts_le_iff sp).mpr (show (s : Int) ≤ e.msg.slot - 1 by omega)
        linarith) hF
  · intro w c n O hci ho
    have hcb := (hp.run.time_mono hci.le).trans hib
    rcases lt_trichotomy n s with hn | rfl | hn
    · exact hp.target_compatible_older_origin ho hcb hz hv hqb hvs hn hVB
    · obtain ⟨CV', hst⟩ := ho.2.2.1
      obtain ⟨_, D, hfl, hOD⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
      have hcomp : Compatible (tr.HonestBlocks H) B D := by
        rcases hfl with ⟨ellD, R, huD, hR, _, hfast, _⟩ | hop'
        · have hDR := ((SA.deepest_mem hfast).1.1.2.2).mono
            (SA.frameIn_of_callAt hr ho.1 huD.1).2
          have hRB := hp.result_source_compatible hc ho.1 hx
            ⟨ellD, huD, hR, rfl⟩ (Or.inr hop) hcb hrb hts
          rcases hRB with h | h
          · exact Or.inr (hDR.trans h)
          · exact SA.anc_total hr.coherent h hDR
        · exact hp.optimistic_sources_compatible hx ho.1 hop hop'
      rcases hcomp with h | h
      · exact SA.anc_total hr.coherent h hOD
      · exact Or.inr (hOD.trans h)
    · exact hp.target_compatible_later_origin_before ho hci hn hprior
  · intro w c n O hci ho
    exact hp.origins_compatible hseed hdb ho ((hp.run.time_mono hci.le).trans hib)
  · intro w c n O hci ho w' c' n' O' hci' ho'
    exact hp.origins_compatible ho ((hp.run.time_mono hci.le).trans hib)
      ho' ((hp.run.time_mono hci'.le).trans hib)

/-- A bounded slow write compares with every older live stored lock through the horizon. -/
theorem ResetPremisesUpTo.slow_stored_locks
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r s i : Nat}
    {D : SA.Blk sp.n (List (FG.Att sp.n))} (hsl : SA.SlowLockAt tr.projAC x r s D)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b) (hib : tr.time i ≤ b)
    (hi : s + 1 ≤ sp.slot (tr.time i)) :
    ∀ l ∈ (tr.projAC.state y i).locks, sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
      ∀ Y ∈ tr.HonestBlocks H, Y.root = l.block → Compatible (tr.HonestBlocks H) Y D := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  intro l hl hlive hle Y hY hYr
  obtain ⟨L, hL, hLr, O, hLO, k, hki, CV, hO⟩ := SA.lock_below_origin hr hy i l hl
  obtain rfl : Y = L := hr.coherent.1 hY hL (hYr.trans hLr.symm)
  obtain ⟨q, R, RV, hR, hDR⟩ := SA.slow_window_results hr hx hsl l.slot (by omega) hle
  have hqb : tr.time q ≤ b := by
    obtain ⟨_, hu, _, _⟩ := hR
    have ht : tr.time q = sp.ts l.slot + 6 * sp.Δ := hu.2.2.1
    -- A slow write uses the update of its label.
    obtain ⟨ell, C, hupdate, _⟩ := hsl
    have ht' : tr.time r = sp.ts s + 6 * sp.Δ := hupdate.2.2.1
    have := (SA.ts_le_iff sp).mpr (show (l.slot : Int) ≤ s by omega)
    linarith
  have hcomp := hp.result_source_compatible hc hx hy hR hO hqb
    ((hp.run.time_mono hki.le).trans hib) (hp.clean_window_timing hs l.slot (by omega))
  rcases hcomp with h | h
  · exact SA.anc_total hr.coherent hLO (hDR.trans h)
  · exact SA.anc_total hr.coherent (hLO.trans h) hDR

/-- A clean slow source retains its prefix in every later vote through the fixed horizon. -/
theorem ResetPremisesUpTo.slow_source_votes_before
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} (hx : x ∈ H) {r s : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hslow : SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b) :
    ∀ i, tr.time i ≤ b → ∀ y ∈ H, ∀ ell e, SA.CastAt tr.projAC y i ell e →
      s < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨ellX, C, hupd, hconf, _, hdeep, _⟩ := id hslow
  have hBC := ((SA.deepest_mem hdeep).1.1.2.2).mono
    (SA.frameIn_of_callAt hr hx hupd.1).2
  have hres : SA.ResultAt tr.projAC x r s C
      (SA.fastCounted sp (tr.projAC.state x r) ellX.frame s C) :=
    ⟨ellX, hupd, hconf, rfl⟩
  apply hp.late_result_prefix_votes_before hc hx hres hBC hrb
    (hp.clean_window_timing hs s (by have := sp.two_le_k; omega))
  · intro y hy i ell e hcast hib hsi hprior
    exact hp.result_prefix_vote_domain_before hc hx hy hres hBC hs hrb hcast hsi hib hprior
  · intro y hy i ell e hcast hib hfirst
    exact hp.slow_stored_locks hc hx hy hslow hs hrb hib (by
      change s + 1 ≤ sp.slot (tr.projAC.time i)
      rw [← (SA.castAt_spec hr hy hcast).2.1, hfirst])

/-- Finite fast-source transfer, with its prospective domain supplied at earlier cuts. -/
theorem ResetPremisesUpTo.fast_source_votes_of_domain_before
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} (hx : x ∈ H) {r s : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfast : SA.FastLockAt tr.projAC x r s B CV) (hts : cutZ sp.toParams g ≤ sp.ts s)
    (hdomain : ∀ y ∈ H, ∀ i ell e, SA.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → s < e.msg.slot →
      (∀ z ∈ H, ∀ q < i, ∀ e', SA.VoteAt tr.projAC z q e' →
        s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e'.msg B) →
      Anc (tr.HonestBlocks H) B ell.frame.fcRoot ∨
        B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot)) :
    ∀ i, tr.time i ≤ b → ∀ y ∈ H, ∀ ell e, SA.CastAt tr.projAC y i ell e →
      s < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hS := healthy_base_of_reset_catch_before hp hc
  have hr := hS.run.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hgs : SA.gbar g ≤ sp.ts s := by have := lt_cutZ sp g; linarith
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
    · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, _⟩ := Compose.cast_head_fcRoot hr hy hcast
      exact ⟨Hd, hΦU hHd, hHdr, hBF.trans (hfHd.mono hΦU)⟩
    have hFB := (hΦ.rooted.2 B hv.1.1).mono hΦU
    have hslot := (SA.castAt_spec hr hy hcast).2.1
    have htime : sp.ts e.msg.slot ≤ tr.time i :=
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).mpr (by rw [← hslot])
    have hcut : cutZ sp.toParams g ≤ tr.time i :=
      hts.trans (((SA.ts_le_iff sp).mpr (by omega)).trans htime)
    have hfault : SA.FaultBound tr.projAC H (tr.time i) := by
      have h := fault_bound_late_before hp hcut hib
      unfold RunTrace.FaultBound RunTrace.honestAwakeJoined at h
      unfold SA.FaultBound SA.honestAwakeJoined
      convert h using 1
      congr 1
      ext z
      exact and_congr_right fun hz => and_congr_right fun _ =>
        (Compose.joined_projection sp ro dg H tr proposer hp.run z hz (tr.time i)).1.symm
    by_cases hfirst : e.msg.slot = s + 1
    · have carry : SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s CV := by
        apply Compose.carryAt_of_writer_window_before hr (SA.serviceWindowBefore_of_sync hS.sync)
          hgs hS.catchUp (by linarith) hx hy hcast hfirst hib
        intro v hv
        obtain ⟨hvs, hw, D, hD, hDr, hBD, ha⟩ := fastLock_writer hr hx hfast v hv
        exact ⟨hvs, hw, D, hD, hDr, hFB.trans hBD, ha⟩
      apply SA.first_transfer_stored sp hS.run hx hfast .refl hy hcast hfirst
        (hp.sync.syncAC hp.run ((SA.le_gbar g).trans hgs)) carry hfault
      · rw [← hfirst]; exact Or.inl hv
      · exact fun z hz q hq e' he hslot => hprior z hz q hq e' he (by omega)
    · obtain ⟨m, hm⟩ : ∃ m, e.msg.slot = m + 1 := ⟨e.msg.slot - 1, by omega⟩
      have hone : ∀ v ∈ Compose.honestVotes tr H m,
          SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e m {v} := by
        rintro v ⟨z, hz, q, e', ⟨ell', hc'⟩, rfl, hsl⟩
        have hqi : q < i := by
          by_contra hn
          have := SA.slot_mono sp (hr.time_nonneg i) (hr.time_mono (Nat.le_of_not_gt hn))
          have := (SA.castAt_spec hr hz hc').2.1
          omega
        obtain ⟨Hv, hHv, hHvr, hBHv⟩ := hprior z hz q hqi e' ⟨ell', hc'⟩ (by omega)
        obtain ⟨⟨Hd, hHd, hHdr, _⟩, hqt⟩ := Compose.cast_head_fcRoot hr hz hc'
        obtain rfl : Hd = Hv := hr.coherent.1 ((SA.frameIn_of_callAt hr hz hc'.1).2 hHd)
          hHv (hHdr.trans hHvr.symm)
        have hgm := hgs.trans ((SA.ts_le_iff sp).mpr (show (s : Int) ≤ m by omega))
        apply Compose.carryAt_of_writer_window_before hr (SA.serviceWindowBefore_of_sync hS.sync)
          hgm hS.catchUp (by linarith) hz hy hcast hm hib
        rintro v rfl
        have ht : tr.projAC.time q < sp.ts m + 2 * sp.Δ := by rw [hsl] at hqt; linarith
        refine ⟨hsl, ⟨q, ⟨ell', hc'.1, Or.inl ⟨e', hc'.2, rfl⟩⟩,
          (SA.ts_le_iff_le_slot sp (hr.time_nonneg q) m).mpr
            (by rw [← (SA.castAt_spec hr hz hc').2.1, hsl]), ht⟩,
          Hd, hHv, hHvr, hFB.trans hBHv, ?_⟩
        rcases Compose.frame_anc_accepted hr hz q ell' hc'.1 Hd hHd Hd .refl with hg | ⟨k, hk, ha⟩
        · exact Or.inl hg
        · exact Or.inr ⟨k, ha, (hr.time_mono hk).trans_lt ht⟩
      have hmt : sp.ts m + sp.Δ ≤ b := by
        rw [hm] at htime
        simp only [SA.SAParams.ts] at htime ⊢; push_cast at htime; linarith
      refine SA.next_vote_extends_before hS.run hy hcast hm
        (fun z hz q hq e' he hsl => hprior z hz q hq e' he (by rcases hsl with h | h <;> omega))
        (hp.half_committee (hts.trans ((SA.ts_le_iff sp).mpr (by omega))) hmt)
        ⟨hr.awake_of_call y hy i ell hcast.1, (SA.castAt_spec hr hy hcast).2.2.1,
          fun v hv => (hone v hv).heads v rfl, fun v hv => (hone v hv).holds v rfl⟩
        hfault
        (hp.sync.syncAC hp.run ((SA.le_gbar g).trans
          (hgs.trans ((SA.ts_le_iff sp).mpr (by omega))))) ?_
      rw [← hm]
      exact Or.inl hv

/-- Clean fast sources retain their raw selected block through the horizon. -/
theorem ResetPremisesUpTo.fast_source_votes_before
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} (hx : x ∈ H) {r s : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfast : SA.FastLockAt tr.projAC x r s B CV)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b) :
    ∀ i, tr.time i ≤ b → ∀ y ∈ H, ∀ ell e, SA.CastAt tr.projAC y i ell e →
      s < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  apply hp.fast_source_votes_of_domain_before hc hx hfast
    (hp.clean_window_timing hs s (by have := sp.two_le_k; omega))
  intro y hy i ell e hcast hib hsi hprior
  rcases hfast with ⟨ellX, C, hupd, hconf, _, hdeep, _⟩ | hop
  · have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
    have hBC := ((SA.deepest_mem hdeep).1.1.2.2).mono
      (SA.frameIn_of_callAt hr hx hupd.1).2
    exact hp.result_prefix_vote_domain_before hc hx hy ⟨ellX, hupd, hconf, rfl⟩ hBC
      hs hrb hcast hsi hib hprior
  · exact hp.optimistic_vote_domain_before hc hx hy hop hs hrb hcast hsi hib hprior

/-- Every live older stored lock compares with a late raw-result prefix, within the horizon. -/
theorem ResetPremisesUpTo.result_prefix_stored_locks
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r s i : Nat}
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocks H) B C)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b) (hib : tr.time i ≤ b)
    (hi : s + 1 ≤ sp.slot (tr.time i)) :
    ∀ l ∈ (tr.projAC.state y i).locks,
      sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
      ∀ Y ∈ tr.HonestBlocks H, Y.root = l.block → Compatible (tr.HonestBlocks H) Y B := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hts := hp.clean_window_timing (show cleanLabel sp a + sp.k + 2 ≤ s by
    have := sp.two_le_k; omega) s (by have := sp.two_le_k; omega)
  have down : ∀ {L D}, Anc (tr.HonestBlocks H) L D →
      Compatible (tr.HonestBlocks H) C D → Compatible (tr.HonestBlocks H) L B := by
    intro L D hLD hCD
    rcases hCD with h | h
    · exact SA.anc_total hr.coherent hLD (hBC.trans h)
    · exact SA.anc_total hr.coherent (hLD.trans h) hBC
  intro l hl hlive hle Y hY hYr
  rcases hle.lt_or_eq with hls | hls
  · have hclean : cleanLabel sp a + sp.k + 2 ≤ l.slot := by omega
    have compare : ∀ {q D}, tr.time q ≤ b →
        ((∃ CV, SA.FastLockAt tr.projAC y q l.slot D CV) ∨
          SA.SlowLockAt tr.projAC y q l.slot D) → Compatible (tr.HonestBlocks H) C D := by
      intro q D hqb hsource
      obtain ⟨z, hz, j, hjr, e, ⟨ell, hcast⟩, _, hes, Hd, hHd, he, hCH⟩ :=
        hp.result_supporter hc hx hres (.refl : Anc (tr.HonestBlocks H) C C) hrb hts
      have hv : SA.VoteExtends (tr.HonestBlocks H) e.msg D := by
        rcases hsource with ⟨CV', hfast⟩ | hslow
        · exact hp.fast_source_votes_before hc hy hfast hclean hqb j
            ((hp.run.time_mono hjr.le).trans hrb) z hz ell e hcast (by omega)
        · exact hp.slow_source_votes_before hc hy hslow hclean hqb j
            ((hp.run.time_mono hjr.le).trans hrb) z hz ell e hcast (by omega)
      obtain ⟨Hd', hHd', he', hDH⟩ := hv
      obtain rfl : Hd' = Hd := hr.coherent.1 hHd' hHd (he'.trans he.symm)
      exact SA.anc_total hr.coherent hCH hDH
    cases hf : l.fast
    · obtain ⟨q, hqi, D, hsl, L, hL, hLr, hLD⟩ := SA.slow_lock_provenance hr hy i l hl hf
      obtain rfl : Y = L := hr.coherent.1 hY hL (hYr.trans hLr.symm)
      exact down hLD (compare ((hp.run.time_mono hqi.le).trans hib) (Or.inr hsl))
    · obtain ⟨q, hqi, D, CV', hfl, L, hL, hLr, hLD⟩ := SA.fast_lock_provenance hr hy i l hl hf
      obtain rfl : Y = L := hr.coherent.1 hY hL (hYr.trans hLr.symm)
      exact down hLD (compare ((hp.run.time_mono hqi.le).trans hib) (Or.inl ⟨CV', hfl⟩))
  · obtain ⟨L, hL, hLr, D, hLD, q, hqi, CV', hD⟩ := SA.lock_below_origin hr hy i l hl
    obtain rfl : Y = L := hr.coherent.1 hY hL (hYr.trans hLr.symm)
    rw [hls] at hD
    exact down hLD (hp.result_source_compatible hc hx hy hres hD hrb
      ((hp.run.time_mono hqi.le).trans hib) hts)

/-- Late raw sources retain every prefix without an external domain or lock hypothesis. -/
theorem ResetPremisesUpTo.clean_result_prefix_votes_before
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} (hx : x ∈ H) {r s : Nat}
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocks H) B C)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b) :
    ∀ i, tr.time i ≤ b → ∀ y ∈ H, ∀ ell e, SA.CastAt tr.projAC y i ell e →
      s < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hclean : cleanLabel sp a + sp.k + 2 ≤ s := by have := sp.two_le_k; omega
  apply hp.late_result_prefix_votes_before hc hx hres hBC hrb
    (hp.clean_window_timing hclean s (by have := sp.two_le_k; omega))
  · intro y hy i ell e hcast hib hsi hprior
    exact hp.result_prefix_vote_domain_before hc hx hy hres hBC hclean hrb hcast hsi hib hprior
  · intro y hy i ell e hcast hib hfirst
    exact hp.result_prefix_stored_locks hc hx hy hres hBC hs hrb hib (by
      change s + 1 ≤ sp.slot (tr.projAC.time i)
      rw [← (SA.castAt_spec hr hy hcast).2.1, hfirst])

/-- Two actual clean raw sources are compatible, using a vote already in the later source. -/
theorem ResetPremisesUpTo.clean_sources_compatible
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r q s t : Nat}
    {C D : SA.Blk sp.n (List (FG.Att sp.n))} {CV DV : Set (Vote sp.n)}
    (hC : SA.ResultAt tr.projAC x r s C CV ∨ SA.OptimisticLockAt tr.projAC x r s C CV)
    (hD : SA.ResultAt tr.projAC y q t D DV ∨ SA.OptimisticLockAt tr.projAC y q t D DV)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (ht : cleanLabel sp a + 2 * sp.k + 1 ≤ t)
    (hrb : tr.time r ≤ b) (hqb : tr.time q ≤ b) :
    Compatible (tr.HonestBlocks H) C D := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have ordered : ∀ {x y r q s t C D CV DV}, x ∈ H → y ∈ H →
      (SA.ResultAt tr.projAC x r s C CV ∨ SA.OptimisticLockAt tr.projAC x r s C CV) →
      (SA.ResultAt tr.projAC y q t D DV ∨ SA.OptimisticLockAt tr.projAC y q t D DV) →
      cleanLabel sp a + 2 * sp.k + 1 ≤ s → s < t → tr.time r ≤ b → tr.time q ≤ b →
      Compatible (tr.HonestBlocks H) C D := by
    intro x y r q s t C D CV DV hx hy hC hD hs hst hrb hqb
    have hclean : cleanLabel sp a + sp.k + 2 ≤ s := by have := sp.two_le_k; omega
    have hts := hp.clean_window_timing (show cleanLabel sp a + sp.k + 2 ≤ t by omega)
      t (by have := sp.two_le_k; omega)
    have supporter : ∃ z ∈ H, ∃ j ≤ q, ∃ e, SA.VoteAt tr.projAC z j e ∧
        e.msg.slot = t ∧ SA.VoteExtends (tr.HonestBlocks H) e.msg D := by
      rcases hD with hD | hD
      · obtain ⟨z, hz, j, hjq, e, hv, _, hes, hDH⟩ :=
          hp.result_supporter hc hy hD (.refl : Anc (tr.HonestBlocks H) D D) hqb hts
        exact ⟨z, hz, j, hjq.le, e, hv, hes, hDH⟩
      · exact (hp.optimistic_supporter hy hD).2
    obtain ⟨z, hz, j, hjq, e, ⟨ell, hcast⟩, hes, Hd, hHd, he, hDH⟩ := supporter
    have hv : SA.VoteExtends (tr.HonestBlocks H) e.msg C := by
      rcases hC with hC | hC
      · exact hp.clean_result_prefix_votes_before hc hx hC .refl hs hrb j
          ((hp.run.time_mono hjq).trans hqb) z hz ell e hcast (by omega)
      · exact hp.fast_source_votes_before hc hx (Or.inr hC) hclean hrb j
          ((hp.run.time_mono hjq).trans hqb) z hz ell e hcast (by omega)
    obtain ⟨Hd', hHd', he', hCH⟩ := hv
    obtain rfl : Hd' = Hd := hr.coherent.1 hHd' hHd (he'.trans he.symm)
    exact SA.anc_total hr.coherent hCH hDH
  rcases lt_trichotomy s t with h | rfl | h
  · exact ordered hx hy hC hD hs h hrb hqb
  · exact hp.sources_same_label_compatible hc hx hy hC hD hrb hqb
      (hp.clean_window_timing (s := s) (by have := sp.two_le_k; omega) s
        (by have := sp.two_le_k; omega))
  · exact (ordered hy hx hD hC ht h hqb hrb).symm

end Consensus.Goldilocks.Healing

end
