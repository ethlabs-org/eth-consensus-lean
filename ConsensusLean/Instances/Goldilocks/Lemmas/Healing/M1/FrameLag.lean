module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameKey
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs

public section

/-! # Store facts of the frame key

`accept_mem'`: a block held by an honest node is accepted by it. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

theorem accept_mem' (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} (h : tr.AcceptAt y k B) :
    B ∈ (tr.state y (k + 1)).fg.tree := by
  rw [tr.state_succ_of_call h, (Store.tree_grows _ _ _ _
    (Compose.fg_reachable hrun.toLocalRun hy k)).1 B _ (hrun.toLocalRun.cutLaw y hy k _ h).2.1]
  exact Set.mem_insert _ _

end Consensus.Goldilocks.Healing

end
