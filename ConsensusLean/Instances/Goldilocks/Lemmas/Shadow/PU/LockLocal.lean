module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Window
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AnchorPrefix
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run

public section

/-! # Historical lock origins and finalized frame roots under P-U -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- The shadow frame root is the finalized tip, so its monotonicity needs no window premise. -/
theorem fcRoot_mono_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {a i : Nat} (hy : y ∈ H (tr.time i)) (hai : a ≤ i) :
    Anc (tr.HonestBlocksAt H) (Node.frame (tr.state y a)).fcRoot
      (Node.frame (tr.state y i)).fcRoot := by
  rw [Node.frame_eq, Node.frame_eq, Store.toFrame_fcRoot, Store.toFrame_fcRoot]
  exact hrun.toLocalRun.finalized_mono_on_prefix' (hrun.time_nonneg i) hy hai
    (fun k hk => hrun.time_mono hk.le)

/-- A live remapped lock records a selection made before this same reader's compromise. -/
theorem live_lock_selection_origin_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {x : Fin sp.n} {i : Nat}
    (hx : x ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt x i ell) {l : AC.Lock}
    (hl : l ∈ AC.liveLocks sp (tr.projAC.state x i).locks ell.frame (tr.time i))
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ell.frame.tree)
    (hBr : B.root = l.block) :
    ∃ a < i, ∃ ellw D, x ∈ H (tr.time a) ∧ tr.projAC.CallAt x a ellw ∧
      D ∈ ellw.frame.tree ∧ Anc (tr.HonestBlocksAt H) B (ellw.frame.viableAncestor D) ∧
      ((∃ CV, AC.FastUpdateAt tr.projAC x a l.slot D CV) ∨
        AC.SlowLockAt tr.projAC x a l.slot D ∨
        ∃ CV, AC.OptimisticLockAt tr.projAC x a l.slot D CV) := by
  have hd := hrun.time_nonneg i
  have hr := (Compose.Growing.goldilocks_ac_projection_from' hrun hnc).upTo hd
  have hs := Trace.upTo_state tr.projAC x (d := tr.time i) (i := i)
    (fun k hk => hrun.time_mono hk.le)
  have hc' := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩
  have hl' : l ∈ AC.liveLocks sp ((tr.projAC.upTo (tr.time i)).state x i).locks
      ell.frame ((tr.projAC.upTo (tr.time i)).time i) := by
    rw [hs]
    exact hl
  have hPhi := AC.frameIn_of_callAt hr.localRun hx hc'
  obtain ⟨l₀, hl₀, E, hE, hEr, -, heq⟩ := hl'
  have hslot : l.slot = l₀.slot := by rw [heq]
  have hBE : ell.frame.Anc B E := by
    have he : B = ell.frame.viableAncestor E := hPhi.1.coherent.1 hB
      (AC.viableAncestor_anc hPhi.1 hE).1 (hBr.trans (congrArg AC.Lock.block heq))
    rw [he]
    exact (AC.viableAncestor_anc hPhi.1 hE).2
  obtain ⟨a, hai, ellw, D, ha, hD, ho, M, hM, hMr, hMA⟩ :=
    AC.lock_selection_candidate_provenance hr.localRun hrun.vstart hx i l₀ hl₀
  have he : M = E := hr.localRun.coherent.1 hM (hPhi.2 hE) (hMr.trans hEr.symm)
  rw [← hslot] at ho
  have hat := hrun.time_mono hai.le
  have hsa := Trace.upTo_state tr.projAC x (d := tr.time i) (i := a)
    (fun k hk => (hrun.time_mono hk.le).trans hat)
  have hcall : ∀ ℓ, (tr.projAC.upTo (tr.time i)).CallAt x a ℓ ↔
      tr.projAC.CallAt x a ℓ := fun _ => Trace.upTo_callAt_of_le _ hat
  have ho' : ((∃ CV, AC.FastUpdateAt tr.projAC x a l.slot D CV) ∨
      AC.SlowLockAt tr.projAC x a l.slot D ∨
      ∃ CV, AC.OptimisticLockAt tr.projAC x a l.slot D CV) := by
    have hcases : ((∃ CV, AC.FastUpdateAt (tr.projAC.upTo (tr.time i)) x a l.slot D CV) ∨
        AC.SlowLockAt (tr.projAC.upTo (tr.time i)) x a l.slot D ∨
        ∃ CV, AC.OptimisticLockAt (tr.projAC.upTo (tr.time i)) x a l.slot D CV) := by
      rcases ho with ⟨_, CV, hf | hop⟩ | ⟨_, hslow⟩
      · exact Or.inl ⟨CV, hf⟩
      · exact Or.inr (Or.inr ⟨CV, hop⟩)
      · exact Or.inr (Or.inl hslow)
    simpa only [AC.FastUpdateAt, AC.UpdateAt, AC.SlowLockAt, AC.OptimisticLockAt,
      AC.OptimisticPoint, hcall, hsa, Trace.upTo_time] using hcases
  exact ⟨a, hai, ellw, D, hrun.antitone hat hx, ((Trace.upTo_callAt _).mp ha).2,
    hD, (hBE.mono hPhi.2).trans (he ▸ hMA), ho'⟩

/-- A historical write below its finalized frame root stays below the reader's frame root. -/
theorem unlocked_image_below_write_root_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {a i : Nat}
    (hy : y ∈ H (tr.time i)) (hai : a ≤ i)
    {ellw ell : ACLabel (goldilocksNode sp ro)}
    (hcw : tr.projAC.CallAt y a ellw) (hc : tr.projAC.CallAt y i ell)
    {L B A : AC.Blk sp.n (List (FG.Att sp.n))}
    (hLB : ell.frame.Anc L B) (hBA : Anc (tr.HonestBlocksAt H) B A)
    (hroot : ellw.frame.Anc A ellw.frame.fcRoot) :
    Anc (tr.HonestBlocksAt H) L ell.frame.fcRoot := by
  have rc := hrun.toCore
  have hya := hrun.antitone (hrun.time_mono hai) hy
  have hAw := hroot.mono (rc.frameIn_at hnc hya hcw).2
  have hLB' := hLB.mono (rc.frameIn_at hnc hy hc).2
  have hbound := hLB'.trans (hBA.trans hAw)
  rw [rc.frame_of_projAC_at hya hcw] at hbound
  rw [rc.frame_of_projAC_at hy hc]
  exact hbound.trans (fcRoot_mono_at' hrun hy hai)

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
