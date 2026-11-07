module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AnchorPrefix

public section

/-! # Local frame-root order before a lock reader's compromise

Only the receiving node's execution prefix is retained. Ancestry conclusions are
lifted into the historical block universe, without retaining historical writers.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A common frame kind makes the local root monotone through an honest reader cut. -/
theorem fcRoot_mono_at {lo hi : Time} {floor : Nat} {kindJ : Prop}
    {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H lo hi floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {a i : Nat} (hy : y ∈ H (tr.time i))
    (hai : a ≤ i) (halo : lo ≤ tr.time a) (hihi : tr.time i ≤ hi) :
    Anc (tr.HonestBlocksAt H) (tr.state y a).fg.fcRoot (tr.state y i).fg.fcRoot := by
  classical
  have htime := hrun.time_mono hai
  have hya := hrun.antitone htime hy
  by_cases hk : kindJ
  · have hka := (hframe.kind_iff y a hya halo (htime.trans hihi)).mpr hk
    have hki := (hframe.kind_iff y i hy (halo.trans htime) hihi).mpr hk
    change Anc _ (if _ then _ else _) (if _ then _ else _)
    rw [ite_eq_left hka, ite_eq_left hki,
      hframe.root_eq y a hya halo (htime.trans hihi) hk,
      hframe.root_eq y i hy (halo.trans htime) hihi hk]
    exact .refl
  · have hka := (hframe.kind_iff y a hya halo (htime.trans hihi)).not.mpr hk
    have hki := (hframe.kind_iff y i hy (halo.trans htime) hihi).not.mpr hk
    change Anc _ (if _ then _ else _) (if _ then _ else _)
    rw [ite_eq_right hka, ite_eq_right hki]
    have hd := hrun.time_nonneg i
    have ha := Trace.upTo_state tr y (d := tr.time i) (i := a)
      (fun k hk => (hrun.time_mono hk.le).trans htime)
    have hi' := Trace.upTo_state tr y (d := tr.time i) (i := i)
      (fun k hk => hrun.time_mono hk.le)
    have hmono := Healing.run_F_mono (hrun.upTo hd).toLocalRun hy hai
    rw [ha, hi'] at hmono
    exact hmono.mono (RunTrace.honestBlocks_upTo_subset hrun.time_mono hd)

/-- A live lock records a write made before this same reader's compromise. -/
theorem live_lock_selection_origin_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {x : Fin sp.n} {i : Nat}
    (hx : x ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt x i ell) {l : SA.Lock}
    (hl : l ∈ SA.liveLocks sp (tr.projAC.state x i).locks ell.frame (tr.time i))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ell.frame.tree)
    (hBr : B.root = l.block) :
    ∃ a < i, ∃ ellw D, x ∈ H (tr.time a) ∧ tr.projAC.CallAt x a ellw ∧
      D ∈ ellw.frame.tree ∧ Anc (tr.HonestBlocksAt H) B (ellw.frame.viableAncestor D) ∧
      ((∃ CV, SA.FastUpdateAt tr.projAC x a l.slot D CV) ∨
        SA.SlowLockAt tr.projAC x a l.slot D ∨
        ∃ CV, SA.OptimisticLockAt tr.projAC x a l.slot D CV) := by
  have hd := hrun.time_nonneg i
  have hs := Trace.upTo_state tr.projAC x (d := tr.time i) (i := i)
    (fun k hk => hrun.time_mono hk.le)
  have hc' : (tr.upTo (tr.time i)).projAC.CallAt x i ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  have hl' : l ∈ SA.liveLocks sp ((tr.upTo (tr.time i)).projAC.state x i).locks
      ell.frame ((tr.upTo (tr.time i)).time i) := by
    simpa only [RunTrace.upTo_projAC, hs, Trace.upTo_time] using hl
  obtain ⟨a, hai, ellw, D, ha, hD, hBA, ho⟩ := Healing.live_lock_selection_origin
    (hrun.upTo hd) (hnc.upTo _) hx hc' hl' hB hBr
  have hat := hrun.time_mono hai.le
  have hsa := Trace.upTo_state tr.projAC x (d := tr.time i) (i := a)
    (fun k hk => (hrun.time_mono hk.le).trans hat)
  have hcall : ∀ ℓ, (tr.projAC.upTo (tr.time i)).CallAt x a ℓ ↔
      tr.projAC.CallAt x a ℓ := fun _ => Trace.upTo_callAt_of_le _ hat
  refine ⟨a, hai, ellw, D, hrun.antitone hat hx, ?_, hD,
    hBA.mono (RunTrace.honestBlocks_upTo_subset hrun.time_mono hd), ?_⟩
  · rw [RunTrace.upTo_projAC] at ha
    exact (Trace.upTo_callAt _).mp ha |>.2
  · simpa only [RunTrace.upTo_projAC, SA.FastUpdateAt, SA.UpdateAt,
      SA.SlowLockAt, SA.OptimisticLockAt, SA.OptimisticPoint, hcall, hsa,
      Trace.upTo_time] using ho

/-- A historical write below its frame root stays below the later local frame root. -/
theorem unlocked_image_below_write_root_at {lo hi : Time} {floor : Nat} {kindJ : Prop}
    {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H lo hi floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {a i : Nat}
    (hy : y ∈ H (tr.time i)) (hai : a ≤ i)
    {ellw ell : ACLabel (goldilocksNode sp ro)}
    (hcw : tr.projAC.CallAt y a ellw) (hc : tr.projAC.CallAt y i ell)
    (halo : lo ≤ tr.time a) (hihi : tr.time i ≤ hi)
    {L B A : SA.Blk sp.n (List (FG.Att sp.n))}
    (hLB : ell.frame.Anc L B) (hBA : Anc (tr.HonestBlocksAt H) B A)
    (hroot : ellw.frame.Anc A ellw.frame.fcRoot) :
    Anc (tr.HonestBlocksAt H) L ell.frame.fcRoot := by
  have hd := hrun.time_nonneg i
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time i))
    (tr.upTo (tr.time i)) proposer (hrun.upTo hd) (hnc.upTo _)).localRun
  have htime := hrun.time_mono hai
  have hcw' : (tr.upTo (tr.time i)).projAC.CallAt y a ellw := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨htime, hcw⟩
  have hc' : (tr.upTo (tr.time i)).projAC.CallAt y i ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono hd
  have hAw := (hroot.mono (SA.frameIn_of_callAt hr hy hcw').2).mono hsub
  have hLB' := (hLB.mono (SA.frameIn_of_callAt hr hy hc').2).mono hsub
  have hwframe := (hrun.cutLaw y a _ (Compose.projAC_callAt.mp hcw)
    (hrun.antitone htime hy)).1
  have hiframe := (hrun.cutLaw y i _ (Compose.projAC_callAt.mp hc) hy).1
  have hbound := hLB'.trans (hBA.trans hAw)
  rw [hwframe] at hbound
  rw [hiframe]
  exact hbound.trans (fcRoot_mono_at hframe hrun hy hai halo hihi)

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
