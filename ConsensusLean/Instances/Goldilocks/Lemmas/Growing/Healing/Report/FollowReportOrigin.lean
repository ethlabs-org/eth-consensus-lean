module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowLocal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements

public section

/-! # The actual candidate behind a historical report

The stored candidate and the selected raw block come from one provenance traversal.
The writer's honesty is needed only at that earlier write.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

/-- A report preserves the viable-ancestor candidate of its own earlier fast write, or, with deep
sources on and no fast-lock candidate at the call, is a deep candidate under a deep anchor whose
live locks are all slow (a deep anchor carried by a live fast lock gives the fast write). -/
theorem toFG_fast_candidate_origin_at
    {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp ro)}
    {R : AC.Blk sp.n (List (FG.Att sp.n))} (hto : AC.ToFGAt tr.projAC y i ell R) :
    (∃ a < i, ∃ j ellw D CV, y ∈ H (tr.time a) ∧
      tr.projAC.CallAt y a ellw ∧ D ∈ ellw.frame.tree ∧
      AC.FastLockAt tr.projAC y a j D CV ∧
      Anc (tr.HonestBlocksAt H) R (ellw.frame.viableAncestor D)) ∨
    ∃ D a, sp.deepDepth = some D ∧
      AC.deepest ell.frame (AC.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i)) =
        none ∧
      AC.deepAnchor sp (tr.projAC.state y i) ell.frame (tr.time i) = some a ∧
      R ∈ AC.toFGDeepCandidates sp D a (tr.projAC.state y i) ell.frame (tr.time i) ∧
      ∀ l ∈ AC.liveLocks sp (tr.projAC.state y i).locks ell.frame (tr.time i),
        l.block = a.root → l.fast = false := by
  have hac := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have hr := (hac.upTo (hrun.time_nonneg i)).localRun
  have hc := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hto.1⟩
  have hs := Trace.upTo_state tr.projAC y (d := tr.time i) (i := i)
    (fun k hk => hrun.time_mono hk.le)
  have hΦ := AC.frameIn_of_callAt hr hy hc
  -- a live fast lock whose block `Y` is at or above `R` gives the fast write
  have fast : ∀ l ∈ AC.liveLocks sp (tr.projAC.state y i).locks ell.frame (tr.time i),
      l.fast = true → ∀ Y ∈ ell.frame.tree, Y.root = l.block → ell.frame.Anc R Y →
      ∃ a < i, ∃ j ellw D CV, y ∈ H (tr.time a) ∧
        tr.projAC.CallAt y a ellw ∧ D ∈ ellw.frame.tree ∧
        AC.FastLockAt tr.projAC y a j D CV ∧
        Anc (tr.HonestBlocksAt H) R (ellw.frame.viableAncestor D) := by
    intro l hl hlf Y hY hYl hRY
    obtain ⟨l₀, hl₀, B, hB, hBr, _, heq⟩ := hl
    have hf₀ : l₀.fast = true := by rw [heq] at hlf; exact hlf
    have hl₀' : l₀ ∈ ((tr.projAC.upTo (tr.time i)).state y i).locks := by
      rwa [hs]
    obtain ⟨a, hai, ellw, D, ha, hD, ho, L, hL, hLr, hLA⟩ :=
      AC.lock_selection_candidate_provenance hr hrun.vstart hy i l₀ hl₀'
    have hRB : Anc (tr.HonestBlocksAt H) R B := by
      have he : Y = ell.frame.viableAncestor B := hΦ.1.coherent.1 hY
        (AC.viableAncestor_anc hΦ.1 hB).1 (hYl.trans (congrArg AC.Lock.block heq))
      rw [he] at hRY
      have hRB' : ell.frame.Anc R B := hRY.trans (AC.viableAncestor_anc hΦ.1 hB).2
      exact hRB'.mono hΦ.2
    obtain rfl : L = B := hac.localRun.coherent.1 hL (hΦ.2 hB) (hLr.trans hBr.symm)
    have hfast : ∃ CV, AC.FastLockAt (tr.projAC.upTo (tr.time i)) y a l₀.slot D CV := by
      rcases ho with ⟨_, CV, ho⟩ | ⟨hn, _⟩
      · exact ⟨CV, ho⟩
      · simp [hf₀] at hn
    obtain ⟨CV, ho⟩ := hfast
    exact ⟨a, hai, l₀.slot, ellw, D, CV, hrun.antitone (hrun.time_mono hai.le) hy,
      ((Trace.upTo_callAt tr.projAC).mp ha).2, hD,
      ((AC.upTo_fastLockAt hrun.time_mono).mp ho).2, hRB.trans hLA⟩
  obtain ⟨-, hRc | ⟨D, a, hD, ha, hn, hR⟩⟩ := AC.toFG_source (A := tr.projAC.state y i) hto.2.2
  · obtain ⟨hv, l, hl, hlr, hlf, _⟩ := hRc
    exact Or.inl (fast l hl hlf R hv.1 hlr.symm Relation.ReflTransGen.refl)
  · by_cases hslow : ∀ l ∈ AC.liveLocks sp (tr.projAC.state y i).locks ell.frame (tr.time i),
        l.block = a.root → l.fast = false
    · exact Or.inr ⟨D, a, hD, hn, ha, hR, hslow⟩
    · push Not at hslow
      obtain ⟨l, hl, hla, hlf⟩ := hslow
      have hat : a ∈ ell.frame.tree := (AC.deepest_mem ha).1.1
      exact Or.inl (fast l hl (by simpa using hlf) a hat hla.symm hR.2.1)

end Consensus.Goldilocks.Healing.Growing

end
