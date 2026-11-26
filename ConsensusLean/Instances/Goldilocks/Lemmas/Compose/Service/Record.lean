module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Head
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.ServedBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts

public section

/-! # Goldilocks Service: the frame at an honest cut

The frame of an honest node before every cut is well formed (`frameOK_state`), since every FG cut
of an honest node runs an FG handler; the fork-choice lemmas (`AC.anc_acHead`,
`AC.acConfirmed_eq`) read it. -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder Payload)

/-- The frame of an honest node before every cut is well formed. -/
theorem frameOK_state {P : Params} {A : NodeAC P}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n}
    {tr : RunTrace A} {proposer : Nat → Fin P.n} {ini : Fin P.n → A.State}
    (hrun : Node.LocalRun proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H) (i : Nat) :
    FrameOK (Node.frame (tr.state y i)) :=
  (Store.frame_realization P A.Payload _ _ (fg_reachable hrun hy i)).1

end Consensus.Goldilocks.Compose

end
