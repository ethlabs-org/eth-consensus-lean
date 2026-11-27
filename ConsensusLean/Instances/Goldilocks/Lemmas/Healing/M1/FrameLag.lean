module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameKey
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs

public section

/-! # Store facts of the frame key

`accept_mem'`: a block held by an honest node is accepted by it. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp}

theorem accept_mem' {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))} (h : tr.AcceptAt y k B) :
    B ∈ (tr.state y (k + 1)).fg.tree :=
  accept_mem_from hrun.toLocalRun hy h

end Consensus.Goldilocks.Healing

end
