module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Window
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AnchorPrefix
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run

public section

/-! # Historical lock origins and finalized frame roots under P-U -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}

/-- The shadow frame root is the finalized tip, so its monotonicity needs no window premise. -/
theorem fcRoot_mono_at'
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {a i : Nat} (hy : y ∈ H (tr.time i)) (hai : a ≤ i) :
    Anc (tr.HonestBlocksAt H) (Node.frame (tr.state y a)).fcRoot
      (Node.frame (tr.state y i)).fcRoot := by
  rw [Node.frame_eq, Node.frame_eq, Store.toFrame_fcRoot, Store.toFrame_fcRoot]
  exact hrun.toLocalRun.finalized_mono_on_prefix (hrun.time_nonneg i) hy hai
    (fun k hk => hrun.time_mono hk.le)

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
