module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.NodeEngine.Family
public import ConsensusLean.Instances.Goldilocks.AsChainShape

@[expose] public section

namespace Consensus.Goldilocks.NodeEngine.Concrete
open Blocks Shape
open Consensus.Model (Public)
open AsChainShape (Setup Info Body Out)
open SA (SAState)

noncomputable def runtime (S : Setup) (pub : Public) (hn : 1 ≤ pub.n) :
    Runtime pub hn (SAState pub.n) (SA.Vote pub.n) (SA.Payload pub.n) :=
  let A := goldilocksNode (S.params pub hn (binding := AsChainShape.stock)) (S.ro _)
  ⟨S.genesisRoot, S.δt, ⟨A.validPayload, A.validMsg, A.holdsMsg, A.genesisPayload,
    A.initial, A.onMessage, A.onBlock, A.onTick, A.proposal, A.toFG, A.confirmed,
    A.head, A.restart⟩⟩

open Classical in
noncomputable def wire (S : Setup) (pub : Public) (hn : 1 ≤ pub.n) :
    Wire (runtime S pub hn) Info Body where
  decBody := inferInstance
  decMsg := inferInstance
  decHolds := fun _ _ => inferInstance
  signer := (·.val)
  encodeMsg m := .vote (AsChainShape.encodeVote m)
  decodeMsg b := match b with
    | .vote w => AsChainShape.decodeVote pub.n w | _ => none
  encodeAtt a := .att (AsChainShape.encodeAtt a)
  encodeInfo := AsChainShape.encodeInfo
  decodeInfo := AsChainShape.decodeInfo pub.n
  payloadMsgs p := p.1 ++ p.2
  payloadObjs := AsChainShape.payloadObjs (binding := AsChainShape.stock)
  headerOf := AsChainShape.headerOf (S.params pub hn)
  blockOf := AsChainShape.blockOf (S.params pub hn)
  parentRef := AsChainShape.parentRef S.genesisRoot
  rootOf := AsChainShape.rootOf
  canonEvent := AsChainShape.canonEvent (binding := AsChainShape.stock)
    (S.params pub hn) (S.ro _)
  relayBody := .relay
  forwardBody := .forward
  msgForwardBody t m := .voteForward t (AsChainShape.encodeVote m)
  dependencies := AsChainShape.dependencies pub.n (binding := AsChainShape.stock)
  conflicts := AsChainShape.conflicts (binding := AsChainShape.stock)
  isFGAtt := AsChainShape.isFGAtt (binding := AsChainShape.stock)
  grid := (AsChainShape.skeleton pub).grid
  proposerSel := (AsChainShape.skeleton pub).proposerSel
  pollSel := (AsChainShape.skeleton pub).pollSel
  order := (AsChainShape.skeleton pub).order
  deliverOrder := (AsChainShape.skeleton pub).deliverOrder
  drain bs := match bs with | [] => ([], []) | b :: rest => ([b], rest)

noncomputable def family (S : Setup) : Family Info Body where
  State := SAState
  Msg := SA.Vote
  Payload := SA.Payload
  runtime := runtime S
  wire := wire S
  decBody := inferInstance
  grid pub := (AsChainShape.skeleton pub).grid
  proposerSel pub := (AsChainShape.skeleton pub).proposerSel
  pollSel pub := (AsChainShape.skeleton pub).pollSel
  order := [.poll, .poll, .pollPropose, .propose, .poll, .poll]
  deliverOrder := [.poll]
  dependencies := fun n => AsChainShape.dependencies n (binding := AsChainShape.stock)
  conflicts := fun _ => AsChainShape.conflicts (binding := AsChainShape.stock)
  isFGAtt := fun _ => AsChainShape.isFGAtt (binding := AsChainShape.stock)

noncomputable def shape (S : Setup) : ChainShapeFamily AsChainShape.schema Info :=
  shapeFamily (family S) fun | .finalized => true | .confirmed => false

/-- Fieldwise view, never equality of nominal state types. -/
noncomputable def view (S : Setup) (pub : Public) (hn : 1 ≤ pub.n)
    (st : AsChainShape.State (S.params pub hn (binding := AsChainShape.stock)) (S.ro _)
      (binding := AsChainShape.stock)) : State (wire S pub hn) :=
  ⟨st.self, ⟨st.node.fg, st.node.ac, st.node.record⟩, st.now, st.outbox, st.relayBuf,
    st.fgDue, st.wrappers, st.forwards, st.voteForwards⟩

/-- Copy external run data, not its derived state or releases. -/
noncomputable def reshape {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (AsChainShape.goldilocks S)) E) :
    Model.Run (compiled (shape S)) E where
  faultyAt := rho.faultyAt
  faultyAt_mono := rho.faultyAt_mono
  horizon := rho.horizon
  events := rho.events
  key := rho.key
  sel := rho.sel
  submit := rho.submit
  relay := rho.relay
  hash := rho.hash

end Consensus.Goldilocks.NodeEngine.Concrete
