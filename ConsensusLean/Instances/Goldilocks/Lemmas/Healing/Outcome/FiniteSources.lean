module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
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

end Consensus.Goldilocks.Healing

end
