module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.LocalSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.RowSource
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.ClientSteps

public section

/-! # Goldilocks suppliers for the local observation and source contracts -/

namespace Consensus.Goldilocks.Healing.Growing.Outcome

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Actual accepted-tree rows are authentic for the cohort surviving at observation. -/
theorem local_observations
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (Hz : Nat) (b : Time) :
    LocalSources.Observations (fun v i => (tr.state v i).fg) tr.time H tr.SignAt Hz b := by
  intro y k hy _ E hE _ _ W hW att ha haT haH
  have hk0 := hrun.time_nonneg k
  have hlek : ∀ q < k, tr.time q ≤ tr.time k := fun q hq => hrun.time_mono hq.le
  have he := Trace.upTo_state tr y hlek
  have hW' : W ∈ ((tr.upTo (tr.time k)).state y k).fg.tree := by rwa [he]
  rcases Healing.tree_accepted (hrun.upTo hk0).toLocalRun hy hW' with rfl | ⟨i', hi', hA⟩
  · cases ha
  have hA' := ((RunTrace.upTo_acceptAt tr).mp hA).2
  obtain ⟨d, hdi, hs⟩ := hrun.toLocalRun.att_unforgeable y i' att
    (hrun.antitone (hlek i' hi') hy) (Or.inr ⟨W, ⟨true, hA'⟩, ha⟩)
    (hrun.antitone (hlek i' hi') haH)
  have hdk : d < k := hdi.trans hi'
  have hv := hrun.antitone (hlek d hdk) haH
  obtain ⟨Es, hEs, hEsr, hEsh⟩ := Healing.signAt_entry
    (hrun.upTo (hrun.time_nonneg d)) hv ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩)
  have he' := Trace.upTo_state tr att.val (fun q (hq : q < d) => hrun.time_mono hq.le)
  rw [he'] at hEs hEsh
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨y, k, tr.time k, hk0, hlek, hy, h⟩
  have hsub' : (tr.state att.val d).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨att.val, d, tr.time d, hrun.time_nonneg d,
      fun q hq => hrun.time_mono hq.le, hv, h⟩
  obtain rfl : Es = E := hU.1 (hsub' hEs) (hsub hE) (hEsr.trans haT)
  have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg d)
    (fun q hq => hrun.time_mono hq.le) hv hk0 hlek hy hEs hE
  exact ⟨d, hdk, hs, hv, Es, hEs, hEsr, hEsh, congrArg FG.ChainState.h hσ⟩

/-- The signed-source supplier includes actual source-tree membership, recovered from the
stored fast-lock event on the source's own honest prefix, not inferred from highness. -/
theorem local_sources
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (g b : Time) :
    LocalSources.Sources (fun v i => (tr.state v i).fg) tr.time H tr.SignAt
      (HighOrigin tr H g) tr.JoinedAt (tr.HonestBlocksAt H) (HZ tr H g) b := by
  intro v d att hv hdb hs hh
  obtain ⟨r, hrd, l, O, ho, E0, hE0, hEO, hEr, hEh, hETh⟩ :=
    high_row_source_at hrun hnc hv hs hh
  have hr0 := hrun.time_nonneg r
  have hler : ∀ q < r, tr.time q ≤ tr.time r := fun q hq => hrun.time_mono hq.le
  obtain ⟨CV, ell, D, hc, hfl, hO⟩ := ho.2.2.1
  have hframe := frame_of_call hrun ho.1 hc
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time r))
    (tr.upTo (tr.time r)) proposer (hrun.upTo hr0) (hnc.upTo _)).localRun
  have hc' : (tr.upTo (tr.time r)).projAC.CallAt v r ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩
  have hPhi := (SA.frameIn_of_callAt hr ho.1 hc').1
  have hOt : O ∈ (tr.state v r).fg.tree := by
    rw [hO, hframe]
    have hm := (SA.viableAncestor_anc hPhi (fastLockAt_frame_mem hfl hc)).1
    rw [hframe] at hm
    exact hm.1
  have hsub : (tr.state v r).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨v, r, tr.time r, hr0, hler, ho.1, h⟩
  exact ⟨r, hrd, l, O, ho, ho.1, ho.2.1, (hrun.time_mono hrd.le).trans hdb,
    hOt, ho.2.2.2, E0, hE0, hEO.mono hsub, hEr, hEh, hETh⟩

end Consensus.Goldilocks.Healing.Growing.Outcome

end
