module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowLocal

public section

/-! # Historical fast origins of actual reports

The fast writer is honest at its own cut by antitonicity from the report call. Its
ancestry is lifted into the historical universe, not a later honest cohort.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- An actual report retains its own earlier honest fast write and its lock-label bound. -/
theorem toFG_fast_origin_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp ro)}
    {R : SA.Blk sp.n (List (FG.Att sp.n))} (hto : SA.ToFGAt tr.projAC y i ell R) :
    ∃ a < i, ∃ j D CV, y ∈ H (tr.time a) ∧ SA.FastLockAt tr.projAC y a j D CV ∧
      Anc (tr.HonestBlocksAt H) R D ∧ j ≤ sp.slot (tr.time i) := by
  have hr := hrun.toLocalRun
  have hd := hr.time_nonneg i
  have hs := Trace.upTo_state tr.projAC y (d := tr.time i) (i := i)
    (fun k hk => hr.time_mono hk.le)
  have hto' : SA.ToFGAt (tr.upTo (tr.time i)).projAC y i ell R := by
    refine ⟨?_, hto.2.1, ?_⟩
    · rw [RunTrace.upTo_projAC]
      exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hto.1⟩
    · simpa only [RunTrace.upTo_projAC, hs, Trace.upTo_time] using hto.2.2
  obtain ⟨a, hai, j, D, CV, ho, hRD, hj⟩ :=
    Healing.toFG_fast_origin (hrun.upTo hd) (hnc.upTo (tr.time i)) hy hto'
  have ha : tr.time a ≤ tr.time i := hr.time_mono hai.le
  have hsa := Trace.upTo_state tr.projAC y (d := tr.time i) (i := a)
    (fun k hk => (hr.time_mono hk.le).trans ha)
  have hcall : ∀ l, (tr.projAC.upTo (tr.time i)).CallAt y a l ↔
      tr.projAC.CallAt y a l := fun _ => Trace.upTo_callAt_of_le _ ha
  have ho' : SA.FastLockAt tr.projAC y a j D CV := by
    simpa only [RunTrace.upTo_projAC, SA.FastLockAt, SA.FastUpdateAt, SA.UpdateAt,
      SA.OptimisticLockAt, SA.OptimisticPoint, hcall, hsa, Trace.upTo_time] using ho
  exact ⟨a, hai, j, D, CV, hr.antitone ha hy, ho',
    hRD.mono (RunTrace.honestBlocks_upTo_subset hr.time_mono hd), hj⟩

end Consensus.Goldilocks.Healing.Growing

end
