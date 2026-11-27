module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Deep

public section

/-! # Historical report roots in the P-U frame

The report root is the actual P-U fork-choice root, the finalized block `F`,
not the conditional root `J`.
-/

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A report lies in the reporter's tree above the actual P-U frame root, `F`. -/
theorem report_root_at {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hR : AC.ToFGAt tr.projAC y i ell R) :
    R ∈ (tr.state y i).fg.tree ∧ (tr.state y i).fg.Anc (tr.state y i).fg.F R := by
  have hret := hR.2.2
  change (AC.acToFG sp _ _ _).2 = some R at hret
  have hroot : R ∈ ell.frame.tree ∧ ell.frame.Anc ell.frame.fcRoot R :=
    ⟨(AC.toFG_source hret).1.1, (AC.toFG_source hret).1.2.1⟩
  rw [frame_of_projAC_at hrun hy hR.1, Node.frame_eq,
    Store.toFrame_tree, Store.toFrame_fcRoot] at hroot
  exact ⟨hroot.1.1, hroot.2.mono fun _ h => by
    rw [Store.toFrame_tree] at h
    exact h.1⟩

end Consensus.Goldilocks.Shadow.PU.Growing

end
