module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.NodeEngine.Wire

@[expose] public section

namespace Consensus.Goldilocks.NodeEngine
open Blocks Shape
open Consensus.Model (Public)

variable {pub : Public} {hn : 1 ≤ pub.n} {S M Q Info Body : Type}
  [DecidableEq Info] [Countable Info] {R : Runtime pub hn S M Q}

/-- Every engine queue is durable. The clock and pending FG update are explicit. -/
structure State (W : Wire R Info Body) where
  self : Fin pub.n
  node : NodeState R.operations.toAC
  now : Time
  outbox : List Body
  relayBuf : List (ShapeObj pub.n Empty Info Body)
  fgDue : Bool
  wrappers : Nat → Option (ShapeObj pub.n Empty Info Body)
  forwards : List (Time × List (ShapeObj pub.n Empty Info Body))
  msgForwards : List (Time × M)

variable (W : Wire R Info Body)

def msgObj (m : M) : ShapeObj pub.n Empty Info Body :=
  .mk (.signed (W.signer m) .poll) (.data (W.encodeMsg m)) []

def blockObj (B : R.operations.toAC.Blk) : ShapeObj pub.n Empty Info Body :=
  .mk (.signed B.proposer (.proposer B.slot)) (.item (W.headerOf B))
    (W.payloadObjs B.fgPayload B.acPayload)

def emitted (cs : List (Cut R.operations.toAC)) : List Body :=
  cs.flatMap fun | .ac ℓ => ℓ.emits.map fun e => W.encodeMsg e.msg | .fg _ => []

def queueAccepted (st : State W) (B : R.operations.toAC.Blk) : State W :=
  match B.parent with
  | none => st
  | some root =>
    let parent := if root = R.genesisRoot then some none else (st.wrappers root).map some
    match parent with
    | none => st
    | some p =>
      let cs := p.toList ++ [blockObj W B]
      { st with
        wrappers := Function.update st.wrappers B.root
          (some (.mk (.signed st.self .poll) (.data (W.forwardBody st.now)) cs))
        forwards := st.forwards ++ [(st.now, cs)] }

/-- Freshness is tested across the handler. Agreement with per-cut admission is a run law. -/
def apply (st : State W) (r : NodeState R.operations.toAC × List (Cut R.operations.toAC)) :
    State W :=
  letI : DecidableEq M := W.decMsg
  let publications := r.2.foldl (fun s c => match c with
    | .fg (.block B true) => queueAccepted W s B | _ => s) st
  let candidates := r.2.flatMap fun
    | .fg _ => []
    | .ac ℓ => (match ℓ.call with
        | .message m => [m] | .block B => W.payloadMsgs B.acPayload | _ => []) ++
        ℓ.emits.map (fun e => (e.msg : M))
  let admitted := candidates.dedup.filter fun m =>
    !(@decide _ (W.decHolds st.node.ac m)) && @decide _ (W.decHolds r.1.ac m)
  { st with node := r.1, outbox := st.outbox ++ emitted W r.2
            wrappers := publications.wrappers, forwards := publications.forwards
            msgForwards := st.msgForwards ++ admitted.map (st.now, ·) }

open Classical in
noncomputable def processOne (hs : List (Header Info × Nat)) (st : State W)
    (o : ShapeObj pub.n Empty Info Body) : State W :=
  match W.canonEvent hs o with
  | some (.block B) =>
    let r := Node.onBlock st.self st.node st.now B
    let s := apply W st r
    if r.1.fg.blocks B.root = some B then { s with relayBuf := s.relayBuf ++ [o] } else s
  | some (.message m) => apply W st (Node.onMessage st.self st.node st.now m)
  | some (.attestation a) =>
    let s := apply W st (Node.onAttestation st.node a)
    { s with relayBuf := s.relayBuf ++ [o] }
  | _ => st

noncomputable def process (st : State W) (o : ShapeObj pub.n Empty Info Body)
    (hs : List (Header Info × Nat)) : State W :=
  o.parts.foldl (processOne W hs) st

noncomputable def recordOwn (st : State W) (o : ShapeObj pub.n Empty Info Body)
    (hs : List (Header Info × Nat)) : State W :=
  letI := W.decBody
  match o with
  | .mk .none (.data b) _ => if b = W.relayBody then { st with relayBuf := [] } else st
  | .mk (.signed k (.proposer _)) (.item h) _ =>
    match W.decodeInfo h.info, W.rootOf hs h with
    | some (atts, p), some d =>
      apply W st (Node.onBlock st.self st.node st.now (W.blockOf d h k atts p))
    | _, _ => st
  | _ => st

open Classical in
noncomputable def nodeTick (st : State W) : State W :=
  if (params pub hn R.genesisRoot R.δt).IsPublic st.now then
    let r := Node.acCall st.self st.node st.now .tick
    { apply W st (r.1, [r.2]) with fgDue := true }
  else st

noncomputable def propose (st : State W) (_ : Slot) :
    State W × Option (ParentRef × Info × List (ShapeObj pub.n Empty Info Body)) :=
  let r := Node.acProposal st.node st.now
  let st' := { st with node := r.1 }
  match r.2.2 with
  | none => (st', none)
  | some (d, p) =>
    let atts := r.1.fg.proposalAttestations d.head
    (st', some (W.parentRef (some d.head.root), W.encodeInfo atts p, W.payloadObjs atts p))

noncomputable def fgUpdate (st : State W) : State W :=
  let r := Node.acToFG st.node st.now
  let st₁ := { st with node := r.1, fgDue := false }
  match r.2.2 with
  | none => st₁
  | some C =>
    match r.1.fg.attest r.1.record st.self C with
    | none => st₁
    | some (a, Λ') =>
      { st₁ with node := (Node.onAttestation { r.1 with record := Λ' } a).1
                 outbox := st₁.outbox ++ [W.encodeAtt a] }

/-- Ordinary single poll, distinct from batch policy. Forward queues are snapshotted by batch. -/
noncomputable def poll (st : State W) (_ : Time) :
    State W × Option (Body × List (ShapeObj pub.n Empty Info Body)) :=
  let s := if st.fgDue then fgUpdate W st else st
  match s.outbox with
  | [] => ({ s with forwards := [], msgForwards := [] }, none)
  | b :: rest => ({ s with outbox := rest, forwards := [], msgForwards := [] }, some (b, []))

/-- The wire chooses ordinary drain policy; old forwarding queues follow in acceptance order. -/
noncomputable def pollBatch (st : State W) (_ : Time) :
    State W × List (Body × List (ShapeObj pub.n Empty Info Body)) :=
  let s := if st.fgDue then fgUpdate W st else st
  let d := W.drain s.outbox
  ({ s with outbox := d.2, forwards := [], msgForwards := [] },
    d.1.map (·, []) ++ st.forwards.map (fun p => (W.forwardBody p.1, p.2)) ++
    st.msgForwards.map (fun p => (W.msgForwardBody p.1 p.2, [msgObj W p.2])))

noncomputable def chainTo (blocks : Nat → Option R.operations.toAC.Blk) :
    Nat → R.operations.toAC.Blk → Chain Info
  | 0, _ => []
  | fuel + 1, B => if B.root = R.genesisRoot then [] else
    (match B.parent.bind blocks with
      | some p => chainTo blocks fuel p | none => []) ++ [W.headerOf B]

noncomputable def outOf (st : State W) : Bool → Chain Info
  | true => chainTo W st.node.fg.blocks (st.node.fg.F.slot + 1) st.node.fg.F
  | false =>
    let C := R.operations.confirmed st.node.ac (Node.frame st.node) st.now
    chainTo W st.node.fg.blocks (C.slot + 1) C

/-- Restore retains all queues, wrappers and node records; silence is not assumed here. -/
noncomputable def restore (k : Fin pub.n) (st : State W) (t : Time) : State W :=
  { apply W { st with self := k, now := t } (Node.restart k st.node t) with fgDue := false }

def skeleton : Skeleton pub.n where
  Kind := Empty
  grid := W.grid
  decKind := inferInstance
  kinds := []
  phase := fun k => k.elim
  kindSel := fun k => k.elim
  proposerSel := W.proposerSel
  pollSel := W.pollSel
  order := W.order
  deliverOrder := W.deliverOrder

noncomputable def nodeShape {Out : Type} (isFinalized : Out → Bool) : ChainShape pub Out Info where
  skel := skeleton W
  State := State W
  Body := Body
  Durable := State W
  decBody := W.decBody
  init k _ := ⟨k, Node.init R.operations.toAC, 0, [], [], false, fun _ => none, [], []⟩
  clock st t := { st with now := t }
  propose := propose W
  act := fun _ _ k => k.elim
  pollPropose st _ := (nodeTick W st, none)
  poll := poll W
  pollBatch := pollBatch W
  gossip st _ := match st.relayBuf with | [] => [] | cs => [(.data W.relayBody, cs)]
  process := process W
  dependencies := W.dependencies
  recordOwn := recordOwn W
  durable := id
  restore k _ := restore W k
  out g st := outOf W st (isFinalized g)
  conflicts := W.conflicts
  isFGAtt := W.isFGAtt

end Consensus.Goldilocks.NodeEngine
