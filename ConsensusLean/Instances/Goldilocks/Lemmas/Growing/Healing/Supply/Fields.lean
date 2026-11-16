module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.GoldilocksBridge
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Components
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowReportOrigin
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows

public section

/-! # Goldilocks healing field bodies

Proofs of `ACHealing` fields at the committee-start Goldilocks run interface
`goldilocksRunInterface`, each with exactly the field's statement:

* `reportAt_iff_toFGAt`: an actual report of a node honest at it is an SA `ac_to_fg` call of the
  AC projection;
* `goldilocks_report_origin`: the `report_origin` field, with `Origin` the joined stored fast
  lock of the Goldilocks data.
-/

namespace Consensus.Goldilocks.Generic

open SA (SAParams ReplayOrder Payload)
open Healing.Growing (HZ IsReset)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- An actual report of a node honest at it is an `ac_to_fg` call of the AC projection. -/
theorem reportAt_iff_toFGAt {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    {i : Nat} (hy : y ∈ H (tr.time i)) {R : SA.Blk sp.n (List (FG.Att sp.n))} :
    ReportAt tr y i R ↔ ∃ ℓ, SA.ToFGAt tr.projAC y i ℓ R := by
  unfold ReportAt SA.ToFGAt
  rw [Compose.Growing.projAC_state_at hrun hy]
  refine exists_congr fun ℓ => ?_
  rw [Compose.projAC_callAt]
  rfl

/-- **The `report_origin` field** at the Goldilocks run interface: a high report of a node honest
at it extends the stored block of an earlier joined fast-lock write of the same node, held by it
at the write. Only collision freedom is read from the premises. -/
theorem goldilocks_report_origin {cm : Time → Finset (Fin sp.n)} {βK : ℚ} {g ΔF a b : Time}
    {y : Fin sp.n} {i : Nat} {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (_hβ : βK ≤ 1 / 2) (hrun : (goldilocksRunInterface sp ro).Run cm proposer dg H tr)
    (hp : Premises tr H cm βK proposer dg (fun v => v.val) g ΔF b)
    (_hr : IsReset tr H g a) (_hab : a ≤ b) (hy : y ∈ H (tr.time i)) (_hib : tr.time i ≤ b)
    (hR : ReportAt tr y i R) (_hh : HZ tr H g + 1 ≤ ((tr.state y i).fg.σ R.root).h) :
    ∃ r ≤ i, ∃ j B, y ∈ H (tr.time r) ∧
      (tr.JoinedAt y (tr.time r) ∧ ∃ CV, Compose.StoredFastLockAt tr y r j B CV) ∧
      B ∈ (tr.state y r).fg.tree ∧ Anc (tr.HonestBlocksAt H) R B := by
  have hr := ((goldilocksRunInterface_run_iff cm).mp hrun).1
  have hnc := hp.noColl
  obtain ⟨ℓ, hto⟩ := (reportAt_iff_toFGAt hr hy).mp hR
  obtain ⟨r, hri, j, ellw, D, CV, hyr, hcw, hD, hfl, hRB⟩ :=
    Healing.Growing.toFG_fast_candidate_origin_at hr hnc hy hto
  have hj : tr.JoinedAt y (tr.time r) :=
    (Healing.Growing.joinedAt_upTo_iff le_rfl).mp
      (Healing.joinedAt_of_fastLockAt (hr.upTo (hr.time_nonneg r)) (hnc.upTo _) hyr
        ((Healing.Growing.fastLockAt_upTo_iff hr.time_mono le_rfl).mpr hfl))
  obtain ⟨hok, hsub⟩ := Healing.Growing.frame_tree_subset_at hr hnc hyr hcw
  exact ⟨r, hri.le, j, ellw.frame.viableAncestor D, hyr, ⟨hj, CV, ellw, D, hcw, hfl, rfl⟩,
    hsub (SA.viableAncestor_anc hok hD).1, hRB⟩

end Consensus.Goldilocks.Generic

end
