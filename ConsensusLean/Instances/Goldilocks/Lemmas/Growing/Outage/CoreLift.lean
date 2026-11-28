module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift

public section

/-! # Ancestry in a prefix of a growing run core

The remaining core consumers transport ancestry into a prefix through a read time. The concrete
run interface is in `Growing/Sleepy/Node/Lift`. -/

namespace Consensus.Goldilocks.GoldilocksRunCore

open AC (ACParams Payload)

variable {sp : ACParams}
  {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}
  (core : GoldilocksRunCore u frameOf proposer dg H tr ini)

include core

/-- Ancestry among the blocks held while honest, ending in a block of the prefix through `d`, is
ancestry in the prefix (`RunTrace.anc_upTo_of_right`). -/
theorem anc_upTo_of_right {d : Time} (hnc : Compose.NoCollRun dg tr) (hd : 0 ≤ d)
    {B C : AC.Blk sp.n (List (FG.Att sp.n))} (hC : C ∈ (tr.upTo d).HonestBlocks (H d))
    (h : Anc (tr.HonestBlocksAt H) B C) : Anc ((tr.upTo d).HonestBlocks (H d)) B C := by
  obtain ⟨y, hy, i, hC⟩ := hC
  obtain ⟨j, _, hj, he⟩ := Trace.upTo_state_exists tr core.time_mono y i (d := d)
  rw [he] at hC
  exact (core.held_anc_at hnc hd hy hj h hC).mono fun _ hX =>
    ⟨y, hy, i, by rw [he]; exact hX⟩

end Consensus.Goldilocks.GoldilocksRunCore

end
