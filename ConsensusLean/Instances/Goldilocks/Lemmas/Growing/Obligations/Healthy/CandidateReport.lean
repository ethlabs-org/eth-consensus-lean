module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset

public section

/-! # Reports at a reading cut, under growing faults

Reader-local report lemmas, each the static one on the prefix through the reading cut, for the
validators honest then:

* `report_of_compatible_candidate_of_run_at`: at an `ac_to_fg` call of a node honest at it, a live
  report candidate compatible (among the blocks held while honest) with every other candidate is
  extended by an actual report at or before the call;
* `cache_ahead_report_at`: a cache strictly ahead of a held target is backed by an earlier report,
  at a strictly higher height, of a validator honest at the reading cut. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **A live report candidate compatible with every other candidate gives an actual report**
extending it, by the call, for a node honest at the call (`report_of_compatible_candidate_of_run`
on the prefix through the call). -/
theorem report_of_compatible_candidate_of_run_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y j ell)
    (hcall : ell.call = .toFG) (hjoin : SA.joined sp (tr.projAC.state y j) (tr.time j))
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hPg : P.root ≠ sp.genesisRoot)
    (hPc : P ∈ SA.toFGCandidates sp (tr.projAC.state y j) ell.frame (tr.time j))
    (hcompat : ∀ C ∈ SA.toFGCandidates sp (tr.projAC.state y j) ell.frame (tr.time j),
      Compatible (tr.HonestBlocksAt H) C P) :
    ∃ r ell' R, SA.ToFGAt tr.projAC y r ell' R ∧ tr.time r ≤ tr.time j ∧
      Anc (tr.HonestBlocksAt H) P R := by
  have hd := hrun.time_nonneg j
  have hst : (tr.upTo (tr.time j)).projAC.state y j = tr.projAC.state y j := by
    rw [RunTrace.upTo_projAC]
    exact Trace.upTo_state tr.projAC y (fun _ hk => hrun.time_mono hk.le)
  have hc' : (tr.upTo (tr.time j)).projAC.CallAt y j ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt_of_le _ le_rfl).mpr hc
  have hU : ∀ X ∈ ell.frame.tree, X ∈ (tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)) :=
    fun X hX => ⟨y, hy, j, by
      rw [RunTrace.upTo_state_of_le hrun.time_mono le_rfl]
      exact (frame_tree_subset_at hrun hnc hy hc).2 hX⟩
  obtain ⟨r, ell', R, hto, hrt, hPR⟩ := Healing.report_of_compatible_candidate_of_run
    (hrun.upTo hd) (hnc.upTo _) hy hc' hcall (by rw [hst]; exact hjoin) hPg
    (by rw [hst]; exact hPc)
    (fun C hC => by
      rw [hst] at hC
      exact (hcompat C hC).imp (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd (hU P hPc.1.1))
        (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd (hU C hC.1.1)))
  have hrj : tr.time r ≤ tr.time j := hrt
  exact ⟨r, ell', R, (toFGAt_upTo_iff hrun.time_mono hrj).mp hto, hrj,
    hPR.mono (RunTrace.honestBlocks_upTo_subset hrun.time_mono hd)⟩

/-- **A cache strictly ahead of a held target is backed by an earlier report**, at a strictly
higher height, of a validator honest at the reading cut (`cache_ahead_report` on the prefix
through the cut). -/
theorem cache_ahead_report_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    (hf : (H (tr.time i))ᶜ.ncard < sp.toParams.fg.q)
    {P X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X = (tr.state y i).fg.F ∨ X = (tr.state y i).fg.J)
    (hP : P ∈ (tr.state y i).fg.tree)
    (hPX : Anc (tr.HonestBlocksAt H) P X) (hne : P ≠ X) :
    ∃ v, v ∈ H (tr.time i) ∧ ∃ j < i, ∃ k < i, ∃ att : FG.Att sp.n, ∃ ℓ C,
      tr.SignAt v k att ∧ k = j + 1 ∧ tr.time j = tr.time k ∧ tr.time j ≤ tr.time i ∧
      SA.ToFGAt tr.projAC v j ℓ C ∧ att.T = X.root ∧
      X ∈ (tr.state v j).fg.tree ∧ Anc (tr.HonestBlocksAt H) X C ∧
      ((tr.state v j).fg.σ C.root).Th = X.root ∧
      ((tr.state v j).fg.σ C.root).h = ((tr.state y i).fg.σ X.root).h ∧
      ((tr.state y i).fg.σ P.root).h < ((tr.state y i).fg.σ X.root).h := by
  have hm := hrun.time_mono
  have hd := hrun.time_nonneg i
  have hst : ∀ z k, k ≤ i → (tr.upTo (tr.time i)).state z k = tr.state z k :=
    fun z k hk => RunTrace.upTo_state_of_le hm (hm hk)
  have hR := fg_reachable_at hrun hd (fun _ hk => hrun.time_mono hk.le) hy
  have hXt : X ∈ (tr.state y i).fg.tree := by
    rcases hX with rfl | rfl
    · exact (Store.cache_invariants _ _ _ _ hR).1
    · exact (Store.cache_invariants _ _ _ _ hR).2.1
  have hXp : X ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) :=
    ⟨y, hy, i, by rw [hst y i le_rfl]; exact hXt⟩
  obtain ⟨v, hv, j, hji, k, hki, att, ℓ, C, hs, hkj, hjk, hjt, hto, haT, hXv, hXC, hTh, hCh,
      hPh⟩ := Healing.cache_ahead_report (hrun.upTo hd) (hnc.upTo _) hf hy (X := X) (P := P)
    (by rw [hst y i le_rfl]; exact hX) (by rw [hst y i le_rfl]; exact hP)
    (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hXp hPX) hne
  rw [hst v j hji.le] at hXv hTh hCh
  rw [hst y i le_rfl] at hCh hPh
  exact ⟨v, hv, j, hji, k, hki, att, ℓ, C, ((RunTrace.upTo_signAt tr).mp hs).2, hkj, hjk, hjt,
    (toFGAt_upTo_iff hm (hm hji.le)).mp hto, haT, hXv,
    hXC.mono (RunTrace.honestBlocks_upTo_subset hm hd), hTh, hCh, hPh⟩

end Consensus.Goldilocks.Healing.Growing

end
