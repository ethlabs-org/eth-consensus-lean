module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowOrigin
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC

public section

/-! # The actual candidate behind a historical report

The stored candidate and the selected raw block come from one provenance traversal.
The writer's honesty is needed only at that earlier write.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

/-- A report preserves the viable-ancestor candidate of its own earlier fast write. -/
theorem toFG_fast_candidate_origin_at
    {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp ro)}
    {R : SA.Blk sp.n (List (FG.Att sp.n))} (hto : SA.ToFGAt tr.projAC y i ell R) :
    ∃ a < i, ∃ j ellw D CV, y ∈ H (tr.time a) ∧
      tr.projAC.CallAt y a ellw ∧ D ∈ ellw.frame.tree ∧
      SA.FastLockAt tr.projAC y a j D CV ∧
      Anc (tr.HonestBlocksAt H) R (ellw.frame.viableAncestor D) := by
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := (hac.upTo (hrun.time_nonneg i)).localRun
  have hc := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hto.1⟩
  have hs := Trace.upTo_state tr.projAC y (d := tr.time i) (i := i)
    (fun k hk => hrun.time_mono hk.le)
  have hΦ := SA.frameIn_of_callAt hr hy hc
  have hRc : R ∈ SA.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i) := by
    have h := hto.2.2
    change (SA.acToFG sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some R at h
    unfold SA.acToFG at h
    split_ifs at h
    split at h
    · cases h
    · rename_i C hC
      split_ifs at h
      cases h
      exact (SA.deepest_mem hC).1
  obtain ⟨hv, l, hl, hlr, hlf, _⟩ := hRc
  obtain ⟨l₀, hl₀, B, hB, hBr, _, heq⟩ := hl
  have hf₀ : l₀.fast = true := by rw [heq] at hlf; exact hlf
  have hl₀' : l₀ ∈ ((tr.projAC.upTo (tr.time i)).state y i).locks := by
    rwa [hs]
  obtain ⟨a, hai, ellw, D, ha, hD, ho, L, hL, hLr, hLA⟩ :=
    SA.lock_selection_candidate_provenance hr hy i l₀ hl₀'
  have hRB : Anc (tr.HonestBlocksAt H) R B := by
    have he : R = ell.frame.viableAncestor B := hΦ.1.coherent.1 hv.1
      (SA.viableAncestor_anc hΦ.1 hB).1 (hlr.symm.trans (congrArg SA.Lock.block heq))
    rw [he]
    exact (SA.viableAncestor_anc hΦ.1 hB).2.mono hΦ.2
  obtain rfl : L = B := hac.localRun.coherent.1 hL (hΦ.2 hB) (hLr.trans hBr.symm)
  have hfast : ∃ CV, SA.FastLockAt (tr.projAC.upTo (tr.time i)) y a l₀.slot D CV := by
    rcases ho with ⟨_, CV, ho⟩ | ⟨hn, _⟩
    · exact ⟨CV, ho⟩
    · simp [hf₀] at hn
  obtain ⟨CV, ho⟩ := hfast
  exact ⟨a, hai, l₀.slot, ellw, D, CV, hrun.antitone (hrun.time_mono hai.le) hy,
    ((Trace.upTo_callAt tr.projAC).mp ha).2, hD,
    ((SA.upTo_fastLockAt hrun.time_mono).mp ho).2, hRB.trans hLA⟩

end Consensus.Goldilocks.Healing.Growing

end
