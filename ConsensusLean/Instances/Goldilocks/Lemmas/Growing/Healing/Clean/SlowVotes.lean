module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.ResultDomain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Timing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Compatibility
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalService
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.WriterCompatible
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HealedMembers

public section

/-! # Clean slow sources and their votes, under growing faults

The growing forms of the slow-source part of `Healing/Outcome/FiniteSources`. Each writer is
honest at its own write; its frame, pool and locks are read on the prefix through the write, and
the comparisons of two writers of one label use the release service owed at each release.

* `ResetPremisesUpTo.result_source_compatible_at`: a result and a result or optimistic source of
  one label are compatible;
* `ResetPremisesUpTo.sources_same_label_compatible_at`: any two such sources of one label are;
* `ResetPremisesUpTo.slow_stored_locks_at`: a later voter's live stored locks of labels up to a
  slow source's are compatible with it;
* `ResetPremisesUpTo.slow_source_votes_before_at`: a clean slow source is extended by every later
  vote through the horizon (the latest-result induction on its result). -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open AC (ACParams Payload Vote)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
variable {hold : Time}

/-- The static AC run of the prefix through `d` of the nodes honest at `d`. -/
private theorem acRun_prefix {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) {d : Time}
    (hd : 0 ≤ d) :
    AC.ACRun proposer (tr.projAC.upTo d) (H d) ((tr.upTo d).HonestBlocks (H d))
      (AC.committeeStart sp.genesisRoot (Generic.dictOfTime sp cm)) := by
  have h := Compose.goldilocks_ac_projection_from (hp.run.upTo hd) (hp.noColl.upTo d)
  rwa [RunTrace.upTo_projAC] at h

/-- A slow write is a slow write of the prefix through its cut. -/
private theorem slowLockAt_upTo (hm : Monotone tr.time) {x : Fin sp.n} {r s : Nat}
    {D : AC.Blk sp.n (List (FG.Att sp.n))} (h : AC.SlowLockAt tr.projAC x r s D) :
    AC.SlowLockAt (tr.projAC.upTo (tr.time r)) x r s D := by
  obtain ⟨ell, C, hu, hconf, hdeep⟩ := h
  have hst : (tr.projAC.upTo (tr.time r)).state x r = tr.projAC.state x r :=
    Trace.upTo_state tr.projAC x fun _ hq => hm hq.le
  refine ⟨ell, C, (AC.upTo_updateAt hm).mpr ⟨le_rfl, hu⟩, ?_, ?_⟩
  · rw [hst]; exact hconf
  · simpa only [hst, Trace.upTo_time] using hdeep

/-- **A result and a result or optimistic source of one label are compatible**, for writers
honest at their writes by `b`, past `c_z`. -/
theorem result_source_compatible_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {r q s : Nat} (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time q))
    {C D : AC.Blk sp.n (List (FG.Att sp.n))} {CV DV : Set (Vote sp.n)}
    (hR : AC.ResultAt tr.projAC x r s C CV)
    (hD : AC.ResultAt tr.projAC y q s D DV ∨ AC.OptimisticLockAt tr.projAC y q s D DV)
    (hrb : tr.time r ≤ b) (hqb : tr.time q ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts s) :
    Compatible (tr.HonestBlocksAt H) C D := by
  have hm := hp.run.time_mono
  have hac := Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl
  have hsvc := hp.sync.ac_service_at hp.run (lo := g) (hi := b) le_rfl
  have hgs : g ≤ sp.ts s := by
    have := Healing.lt_cutZ sp g
    have := Healing.le_gbar g
    have := sp.toParams.hΔ
    linarith
  have hreset : ∀ z c, z ∈ H (tr.time c) → tr.time c ≤ b → tr.projAC.RestartAt z c →
      tr.time c ≤ sp.ts s := by
    intro z c hz hcb hrest
    apply (hp.restart_le_before_at hz (Compose.projAC_restartAt.mp hrest) hcb).trans
    have hh := (AC.ts_le_iff sp).mp ((Healing.cutZ_eq sp g) ▸ hts)
    exact (AC.ts_le_iff sp).mpr (by clear * - hh; omega)
  rcases hD with hD | hD
  · exact AC.Growing.result_result_compatible_window_before_at hac hsvc hgs hx hy hR hD hrb hqb
      (fun c hc hrest => hreset x c (hp.run.antitone (hm hc) hx) ((hm hc).trans hrb) hrest)
      (fun c hc hrest => hreset y c (hp.run.antitone (hm hc) hy) ((hm hc).trans hqb) hrest)
  · exact AC.Growing.result_optimistic_compatible_window_before_at hac hsvc hgs hx hy hR hD
      hrb hqb
      (fun c hc hrest => hreset x c (hp.run.antitone (hm hc) hx) ((hm hc).trans hrb) hrest)
      (fun v hv => hp.committeeFacts.hP.1 _ x hx r (fun _ hk => hm hk.le) s v hv)
      (hp.committeeFacts.hsize s)

/-- **Two result or optimistic sources of one label are compatible**, for writers honest at their
writes by `b`, past `c_z`. -/
theorem sources_same_label_compatible_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {r q s : Nat} (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time q))
    {C D : AC.Blk sp.n (List (FG.Att sp.n))} {CV DV : Set (Vote sp.n)}
    (hC : AC.ResultAt tr.projAC x r s C CV ∨ AC.OptimisticLockAt tr.projAC x r s C CV)
    (hD : AC.ResultAt tr.projAC y q s D DV ∨ AC.OptimisticLockAt tr.projAC y q s D DV)
    (hrb : tr.time r ≤ b) (hqb : tr.time q ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts s) :
    Compatible (tr.HonestBlocksAt H) C D := by
  rcases hC with hC | hC
  · exact hp.result_source_compatible_at hx hy hC hD hrb hqb hts
  rcases hD with hD | hD
  · exact (hp.result_source_compatible_at hy hx hD (Or.inr hC) hqb hrb hts).symm
  · exact hp.optimistic_sources_compatible_at hx hy hrb hqb (Healing.gbar_le_of_cutZ_le sp hts)
      hC hD

/-- **A bounded slow write compares with every older live stored lock** of a later voter honest
at its cut, within the horizon. -/
theorem slow_stored_locks_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {r s i : Nat} (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time i))
    {D : AC.Blk sp.n (List (FG.Att sp.n))} (hsl : AC.SlowLockAt tr.projAC x r s D)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b) (hib : tr.time i ≤ b)
    (hi : s + 1 ≤ sp.slot (tr.time i)) :
    ∀ l ∈ (tr.projAC.state y i).locks, sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
      ∀ Y ∈ tr.HonestBlocksAt H, Y.root = l.block → Compatible (tr.HonestBlocksAt H) Y D := by
  have hm := hp.run.time_mono
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hr0 := hp.run.time_nonneg r
  have hi0 := hp.run.time_nonneg i
  have hrr := (acRun_prefix hp hr0).localRun
  have hri := (acRun_prefix hp hi0).localRun
  have subr := RunTrace.honestBlocks_upTo_subset hm (H := H) hr0
  have subi := RunTrace.honestBlocks_upTo_subset hm (H := H) hi0
  intro l hl hlive hle Y hY hYr
  rw [← Trace.upTo_state tr.projAC y (d := tr.time i) fun _ hq => hm hq.le] at hl
  obtain ⟨L, hL, hLr, O, hLO, k, hki, CV, hO⟩ := AC.lock_below_origin hri
    (acRun_prefix hp hi0).vstart hy i l hl
  obtain rfl : Y = L := hU.1 hY (subi hL) (hYr.trans hLr.symm)
  have hsl' := slowLockAt_upTo hm hsl
  obtain ⟨q, R, RV, hR, hDR⟩ := AC.slow_window_resultsU (hr := hrr.toU)
    (acRun_prefix hp hr0).vstart hx hsl' l.slot (by omega) hle
  obtain ⟨hqr, hR⟩ := (AC.upTo_resultAt hm).mp hR
  have hO' : AC.ResultAt tr.projAC y k l.slot O CV ∨ AC.OptimisticLockAt tr.projAC y k l.slot O CV
    := hO.imp (fun h => ((AC.upTo_resultAt hm).mp h).2)
      (fun h => ((AC.upTo_optimisticLockAt hm).mp h).2)
  have hkb : tr.time k ≤ b := (hm hki.le).trans hib
  have hcomp := hp.result_source_compatible_at (hp.run.antitone hqr hx)
    (hp.run.antitone (hm hki.le) hy) hR hO' (hqr.trans hrb) hkb
    (hp.clean_window_timing_at hs l.slot (by omega))
  have hDR' := hDR.mono subr
  have hLO' := hLO.mono subi
  rcases hcomp with h | h
  · exact AC.anc_total hU hLO' (hDR'.trans h)
  · exact AC.anc_total hU (hLO'.trans h) hDR'

/-- **A clean slow source is extended by every later vote** of a node honest at it, through the
horizon: the latest-result induction on the source's result. -/
theorem slow_source_votes_before_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {r s : Nat} (hx : x ∈ H (tr.time r))
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hslow : AC.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b) :
    ∀ i, tr.time i ≤ b → ∀ y, y ∈ H (tr.time i) → ∀ ell e, AC.CastAt tr.projAC y i ell e →
      s < e.msg.slot → AC.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hm := hp.run.time_mono
  have hxU : (tr.state x r).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨x, r, tr.time r, hp.run.time_nonneg r, fun _ hq => hm hq.le, hx, h⟩
  have hcase : (∀ D, sp.deepDepth = some D → b ≤ cutZ sp.toParams g + 4 * D * sp.Δ) ∨
      HighSourceCover tr H g a b := by
    cases hdd : sp.deepDepth with
    | none => exact Or.inl fun D hD => by cases hD
    | some D =>
      rcases hp.deepCover D hdd with hb | hc
      · exact Or.inl fun D' hD' => by cases hD'; exact hb
      · exact Or.inr hc
  rcases hcase with hpre | hc
  swap
  · -- under the high-source cover: S2, the slow lock past the drain being a member
    intro i hib y hy ell e hcast hsi
    exact Compose.Growing.healed_source_votes_at hc.s2
      (Compose.Growing.HealedOrigin.of_lock (rL := healedLockFloor sp a)
        (rO := healedOriginFloor sp a) hs
        (Compose.Growing.lockWithin_iff.2 ⟨x, r, hx, hrb, Or.inr hslow⟩)) .refl
      (Compose.Growing.hVoteAt_iff.2 ⟨hy, ell, hcast⟩) hib hsi
  obtain ⟨ellX, C, hupd, hconf, hdeep⟩ := id hslow
  have hBC := ((AC.deepest_mem hdeep).1.1.2.2).mono
    ((frame_tree_subset_at hp.run hp.noColl hx hupd.1).2.trans hxU)
  have hres : AC.ResultAt tr.projAC x r s C
      (AC.fastCounted sp (tr.projAC.state x r) ellX.frame s C) :=
    ⟨ellX, hupd, hconf, rfl⟩
  apply hp.late_result_prefix_votes_before_at hx hres hBC hrb
    (hp.clean_window_timing_at hs s (by have := sp.two_le_k; clear * - this; omega))
  · intro y i ell e hy hcast hib hsi hprior
    exact ProposalImpl.result_prefix_vote_domain_before_of_quarantine_at hp hx hy hres hBC hs hrb
      hcast hsi hib (fun z q hz hqi e' hv hse => hprior z q e' hqi
        (Compose.Growing.hVoteAt_iff.mpr ⟨hz, hv⟩) hse) hpre
  · intro y i ell e hy hcast hib hfirst
    have hi0 := hp.run.time_nonneg i
    have hcast' : AC.CastAt (tr.projAC.upTo (tr.time i)) y i ell e :=
      AC.upTo_castAt.mpr ⟨le_rfl, hcast⟩
    have hsl := (AC.castAt_specU (acRun_prefix hp hi0).localRun.toU hy hcast').2.1
    exact hp.slow_stored_locks_at hx hy hslow hs hrb hib (by
      change e.msg.slot = sp.slot (tr.time i) at hsl
      rw [← hsl, hfirst])

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
