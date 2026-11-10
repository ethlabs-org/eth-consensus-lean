module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.NodeEngine.Family

@[expose] public section
namespace Consensus.Goldilocks.NodeEngine
open Blocks Shape

/-- Duty and candidate prefixes include own-release processing and the evolving seen list. -/
inductive Stage where
  | entry
  | duty (index : Nat)
  | candidate (dutyIndex candidateIndex : Nat)
  | gossip (candidateIndex : Nat)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  {I B : Type} {O : OutputSchema} [DecidableEq I] [Countable I]
  (A : Family I B) (fin : O.Id → Bool)
  (rho : Model.Run (compiled (shapeFamily A fin)) E)

/-- Entry to scheduled duties: restart has no duties, tick clocks, delivery processes first. -/
noncomputable def entry (i : Nat) (v : V) :
    Model.Node (Model.protoOf (compiled (shapeFamily A fin)) E) :=
  let nd := rho.stateBefore i v
  let P := Model.protoOf (compiled (shapeFamily A fin)) E
  match rho.events[i]? with
  | some (.tick _ t) => ⟨P.clock nd.st t (Model.mempool rho.inbox v t), nd.seen⟩
  | some (.deliver _ o _) => ⟨P.process nd.st o (Model.digests rho.hash o), nd.seen ++ [o]⟩
  | _ => nd

noncomputable def eventDuties (i : Nat) :=
  let P := Model.protoOf (compiled (shapeFamily A fin)) E
  match rho.events[i]? with
  | some (.tick v t) => if E.awake v t then P.duties t else []
  | some (.deliver _ _ t) => P.deliverDuties t
  | _ => []

noncomputable def stageNode (i : Nat) (v : V) : Stage →
    Model.Node (Model.protoOf (compiled (shapeFamily A fin)) E)
  | .entry => entry A fin rho i v
  | .duty j => (rho.runDuties v (entry A fin rho i v) ((eventDuties A fin rho i).take j)).1
  | .candidate j k =>
    let nd := (rho.runDuties v (entry A fin rho i v) ((eventDuties A fin rho i).take j)).1
    match (eventDuties A fin rho i)[j]? with
    | none => nd
    | some d =>
      let P := Model.protoOf (compiled (shapeFamily A fin)) E
      if rho.ownKey v ∈ rho.sel (P.role d) then
        let r := P.act nd.st d
        (Model.releaseAll P rho.hash (rho.ownKey v) ⟨r.1, nd.seen⟩
          ((rho.signedCandidate v d r.2).take k)).1
      else nd
  | .gossip k =>
    let P := Model.protoOf (compiled (shapeFamily A fin)) E
    let nd := (rho.runDuties v (entry A fin rho i v) (eventDuties A fin rho i)).1
    let t := match rho.events[i]? with | some e => e.time | none => 0
    (Model.releaseAll P rho.hash (rho.ownKey v) nd
      ((Model.gossipCandidates P nd.st t).take k)).1

end Consensus.Goldilocks.NodeEngine
