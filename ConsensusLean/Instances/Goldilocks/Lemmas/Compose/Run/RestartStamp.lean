module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.RestartTrace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC

public section

/-! # Admitted Goldilocks executions also execute restart stamping -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- The admitted run's AC projection satisfies the bulk-stamp execution contract on the
same carrier. In particular every state read and every emission read point is preserved.
`NoCollRun` is precisely the existing AC projection premise, not a new restart assumption. -/
theorem goldilocks_run_stamp (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) :
    AC.ACLocalRunStep (AC.WriteMode.parent sp) (AC.parentOracle sp tr.projAC)
      (fun _ => AC.stepWithStamp (AC.WriteMode.parent sp))
      H (tr.HonestBlocks H) tr.projAC ini :=
  AC.localRun_stamp (goldilocks_ac_projection_from hrun hnc).localRun

end Consensus.Goldilocks.Compose

end
