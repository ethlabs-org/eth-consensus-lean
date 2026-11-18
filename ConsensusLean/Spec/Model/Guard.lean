module
public import ConsensusLean.Spec.Model.Run

@[expose] public section

/-! # When slashing protection fires (L1)

The engine's slashing protection (`protects`) refuses an own-signed candidate that conflicts with
itself or with an own-signed object the node has seen. So an honest node never releases a
conflicting pair, whatever the protocol. What the guard cannot show is whether honest code would
have signed such a pair without it. `guardRefusalsAt i` lists the candidates of event `i` that
`protects` rejects at their turn in release, in the order and against the `seen` log the engine
uses (`Run.tick`, `Run.deliver`), whether or not the other release checks (`releasable`,
dependencies) pass. `GuardIdle` says no event has such a candidate, so the guard never changes
what the engine releases. -/

namespace Consensus.Model

/-- The candidates `cs` that slashing protection rejects when the node with own key `k` releases
them in order from node `nd`, as `releaseAll` does: each candidate is checked by `protects` against
the `seen` log at its turn, which holds the candidates released before it, whether or not the
candidate is `releasable` and its dependencies are held. -/
def guardRefusals {pub : Public} {Out : Type} (P : Protocol pub Out) (hash : P.Item → Nat)
    (k : Key pub) : Node P → List P.Object → List P.Object
  | _, [] => []
  | nd, c :: cs =>
    (if protects P k nd.seen c then [] else [c]) ++
      guardRefusals P hash k (releaseAll P hash k nd [c]).1 cs

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
  {E : Env V}

namespace Run

variable (rho : Run F E)

/-- The candidates of duty `d` of node `v` at node `nd` that slashing protection refuses: the
candidates `dutyStep` releases from, checked as `releaseAll` checks them. An unselected duty has
none. -/
def dutyRefusals (v : V) (nd : Node (protoOf F E)) (d : (protoOf F E).Duty) :
    List (protoOf F E).Object :=
  if rho.ownKey v ∈ rho.sel ((protoOf F E).role d) then
    let a := (protoOf F E).act nd.st d
    guardRefusals (protoOf F E) rho.hash (rho.ownKey v) ⟨a.1, nd.seen⟩ (rho.signedCandidate v d a.2)
  else []

/-- The refused candidates of the duties `ds` of node `v`, run one after the other from node `nd`
as `runDuties` runs them. -/
def runDutiesRefusals (v : V) : Node (protoOf F E) → List (protoOf F E).Duty →
    List (protoOf F E).Object
  | _, [] => []
  | nd, d :: ds => rho.dutyRefusals v nd d ++ runDutiesRefusals v (rho.dutyStep v nd d).1 ds

/-- The refused candidates of a tick (`Run.tick`): of its duties from the post-clock node, then of
the gossip from the node they leave. An asleep tick has none. -/
def tickRefusals (nd : Node (protoOf F E)) (v : V) (t : Time) : List (protoOf F E).Object :=
  let nd₁ : Node (protoOf F E) := ⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩
  if E.awake v t then
    let r := rho.runDuties v nd₁ ((protoOf F E).duties t)
    rho.runDutiesRefusals v nd₁ ((protoOf F E).duties t) ++
      guardRefusals (protoOf F E) rho.hash (rho.ownKey v) r.1
        (gossipCandidates (protoOf F E) r.1.st t)
  else []

/-- The refused candidates of a raw arrival (`Run.deliver`): of the delivery duties from the
processed node, then of the gossip from the node they leave. -/
def deliverRefusals (nd : Node (protoOf F E)) (v : V) (o : (protoOf F E).Object) (t : Time) :
    List (protoOf F E).Object :=
  let nd₁ : Node (protoOf F E) :=
    ⟨(protoOf F E).process nd.st o (digests rho.hash o), nd.seen ++ [o]⟩
  let r := rho.runDuties v nd₁ ((protoOf F E).deliverDuties t)
  rho.runDutiesRefusals v nd₁ ((protoOf F E).deliverDuties t) ++
    guardRefusals (protoOf F E) rho.hash (rho.ownKey v) r.1
      (gossipCandidates (protoOf F E) r.1.st t)

/-- The candidates that slashing protection refuses at the event at index `i`, from the world
before it (a restart has none). -/
def guardRefusalsAt (i : Nat) : List (protoOf F E).Object :=
  match rho.events[i]? with
  | some (.tick v t) => rho.tickRefusals (rho.stateBefore i v) v t
  | some (.deliver v o t) => rho.deliverRefusals (rho.stateBefore i v) v o t
  | _ => []

/-- **Slashing protection never fires** on run `rho`: no event refuses a candidate for conflicting
with the node's own signatures, so the engine releases what it would release without the guard. -/
def GuardIdle : Prop := ∀ i, rho.guardRefusalsAt i = []

end Run

end Consensus.Model

end
