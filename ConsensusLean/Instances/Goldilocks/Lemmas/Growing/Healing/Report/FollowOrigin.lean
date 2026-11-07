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

/-- A report extending slot `u` by the next update has a fast origin labelled `u` or `u+1`. -/
theorem toFG_fast_origin_slot_bounds_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i u : Nat}
    (hy : y ∈ H (tr.time i))
    (hf : ∀ t, 0 ≤ t → t ≤ tr.time i → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    {ell : ACLabel (goldilocksNode sp ro)} {P R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hto : SA.ToFGAt tr.projAC y i ell R) (hPs : P.slot = u)
    (hPR : Anc (tr.HonestBlocksAt H) P R)
    (ht : tr.time i ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ) :
    ∃ a < i, ∃ j D CV, y ∈ H (tr.time a) ∧ SA.FastLockAt tr.projAC y a j D CV ∧
      Anc (tr.HonestBlocksAt H) R D ∧ u ≤ j ∧ j ≤ u + 1 := by
  obtain ⟨a, hai, j, D, CV, hya, ho, hRD, hj⟩ := toFG_fast_origin_at hrun hnc hy hto
  have hac := Compose.Growing.honest_blocks_coherent hrun hnc
  have hPD := (Anc.slot_le hac (hPR.trans hRD)).1
  have ha := hrun.time_mono hai.le
  have hs := Trace.upTo_state tr.projAC y (d := tr.time a) (i := a)
    (fun q hq => hrun.time_mono hq.le)
  have hc : ∀ l, (tr.projAC.upTo (tr.time a)).CallAt y a l ↔
      tr.projAC.CallAt y a l := fun _ => Trace.upTo_callAt_of_le _ le_rfl
  have ho' : SA.FastLockAt (tr.upTo (tr.time a)).projAC y a j D CV := by
    simpa only [RunTrace.upTo_projAC, SA.FastLockAt, SA.FastUpdateAt, SA.UpdateAt,
      SA.OptimisticLockAt, SA.OptimisticPoint, hc, hs, Trace.upTo_time] using ho
  have hDj := Healing.fast_selection_slot_le (hrun.upTo (hrun.time_nonneg a))
    (hnc.upTo _) (hf _ (hrun.time_nonneg a) ha) hya ho'
  have hupper : sp.slot (tr.time i) ≤ u + 1 := by
    by_contra hn
    have hlo := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg i) ((u + 2 : Nat) : Int)).2
      (by exact_mod_cast (by omega : u + 2 ≤ sp.slot (tr.time i)))
    have he : sp.ts (u + 2 : Nat) = sp.ts (u + 1 : Nat) + 4 * sp.Δ := SA.ts_succ (u + 1)
    linarith only [hlo, he, ht, sp.toParams.hΔ]
  refine ⟨a, hai, j, D, CV, hya, ho, hRD, ?_, hj.trans hupper⟩
  omega

end Consensus.Goldilocks.Healing.Growing

end
