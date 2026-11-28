module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.CoreStock
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Reachable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Node.Cache
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Frame.Snapshots
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Reach

public section

namespace Consensus.Goldilocks.Node

variable {P : Params} {A : NodeAC P}

theorem step_iff (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n) (cfg : Config A)
    (e : Event A) (t' : Time) (cfg' : Config A) :
    Step proposer dg self cfg e t' cfg' ↔
      cfg.time ≤ t' ∧ EventOK t' (Phase.at cfg.time t' cfg.phase) e ∧ WireOK dg e ∧
        cfg'.st = (exec proposer dg self cfg.st t' e).1 ∧ cfg'.time = t' ∧
          cfg'.phase = e.phaseAfter := by rfl

theorem reachable_eq (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n) (a : A.State) :
    Reachable proposer dg self (a := a) =
      Relation.ReflTransGen (fun cfg cfg' => ∃ e t', Step proposer dg self cfg e t' cfg')
        (Config.init A a) := by rfl

end Consensus.Goldilocks.Node

end
