module
public import ConsensusLean.Spec.Shape.Compile
public import ConsensusLean.Instances.Goldilocks.Spec.Node.Handlers

@[expose] public section

/-! # A node as a chain shape

The node supplies FG and AC transitions. The instance supplies the wire format, signing roles,
publication queues and skeleton. The encoder shares the handler dispatch and delivery order,
without assuming any AC message type or that the chosen polls suffice to release the emissions.
-/

namespace Consensus.Goldilocks.NodeAsChainShape

open Blocks Shape
open Model (Public Msg DependencyPolicy)

variable {P : Params} {A : NodeAC P} {K I B O S : Type}

/-- Embed a raw digest among node roots, reserving `g` exclusively for genesis. -/
def taggedRoot (g h : Nat) : Nat := if h < g then h else h + 1

/-- Recover the raw digest from a non-genesis node root. -/
def rawRoot (g r : Nat) : Nat := if r < g then r else r - 1

/-- Genesis is named by `.root`, all other parents by their raw digest. -/
def parentRef (g : Nat) : Option Nat → ParentRef
  | none => .root
  | some r => if r = g then .root else .digest (rawRoot g r)

/-- The node root of the parent named by the header. -/
def parentRoot (g : Nat) : ParentRef → Option Nat
  | .root => some g
  | .digest r => some (taggedRoot g r)

/-- The digest of a header from the engine's digest list. -/
def rootOf [DecidableEq I] (hs : List (Header I × Nat)) (h : Header I) : Option Nat :=
  (hs.find? fun q => q.1 == h).map (·.2)

/-- Wire data specific to the AC and the chosen roles. Block framing is shared. -/
structure WireCodec (A : NodeAC P) (K I B : Type) where
  encode : List (FG.Att P.n) → A.Payload → I
  decode : I → Option (List (FG.Att P.n) × A.Payload)
  carried : List (FG.Att P.n) → A.Payload → List (ShapeObj P.n K I B)
  message : ShapeObj P.n K I B → Option A.Msg
  attestation : ShapeObj P.n K I B → Option (FG.Att P.n)

/-- The canonical header of a node block. -/
def headerOf {Payload : Type} (encode : List (FG.Att P.n) → Payload → I)
    (b : NodeBlock P Payload) : Header I :=
  ⟨parentRef P.genesisRoot b.parent, b.slot, b.input, encode b.fgPayload b.acPayload⟩

/-- A node block from a header, engine digest, signing key and decoded payloads. -/
def blockOf {Payload : Type} (d : Nat) (h : Header I) (k : Fin P.n) (atts : List (FG.Att P.n))
    (p : Payload) : NodeBlock P Payload :=
  ⟨taggedRoot P.genesisRoot d, parentRoot P.genesisRoot h.parent, h.pos, k, h.input, atts, p⟩

/-- A block is signed by its proposer and carries the canonical objects of its payloads. -/
def blockObj {Payload : Type} (encode : List (FG.Att P.n) → Payload → I)
    (carried : List (FG.Att P.n) → Payload → List (ShapeObj P.n K I B))
    (b : NodeBlock P Payload) : ShapeObj P.n K I B :=
  .mk (.signed b.proposer (.proposer b.slot)) (.item (headerOf encode b))
    (carried b.fgPayload b.acPayload)

open Classical in
/-- Decode only canonical block objects with well-formed attestations and valid AC payload. -/
noncomputable def decodeBlock [DecidableEq I] {Payload : Type}
    (decode : I → Option (List (FG.Att P.n) × Payload))
    (carried : List (FG.Att P.n) → Payload → List (ShapeObj P.n K I B))
    (valid : NodeBlock P Payload → Prop)
    (hs : List (Header I × Nat)) : ShapeObj P.n K I B → Option (NodeBlock P Payload)
  | .mk (.signed k (.proposer s)) (.item h) cs =>
      match decode h.info, rootOf hs h with
      | some (atts, p), some d =>
          let b := blockOf (P := P) d h k atts p
          if h.pos = s ∧ cs = carried atts p ∧ (∀ a ∈ atts, a.WellFormed) ∧ valid b then some b
          else none
      | _, _ => none
  | _ => none

/-- The node call represented by a canonical received object; wrappers make no call. -/
noncomputable def canonEvent [DecidableEq I] (C : WireCodec A K I B)
    (hs : List (Header I × Nat)) (o : ShapeObj P.n K I B) : Option (Node.Event A) :=
  match decodeBlock C.decode C.carried A.validPayload hs o, C.message o, C.attestation o with
  | some b, _, _ => some (.block b)
  | none, some m, _ => some (.message m)
  | none, none, some a => some (.attestation a)
  | none, none, none => none

/-- The node, clock and publication operations on the instance's shape state. -/
structure Adapter (A : NodeAC P) (K I B S : Type) where
  self : S → Fin P.n
  node : S → NodeState A
  now : S → Time
  setNode : S → NodeState A → S
  setDue : S → Bool → S
  wake : S → Fin P.n → Time → S
  /-- Record a call's result; the optional object is the received wire object the call came
  from (the message branch of `processOne`), kept for exact relay. -/
  applyCuts : S → Option (ShapeObj P.n K I B) → (NodeState A × List (Cut A)) → S
  relayIf : S → (c : Prop) → [Decidable c] → ShapeObj P.n K I B → S
  attest : S → NodeState A → FG.Att P.n → S
  /-- Whether this validator runs the FG update at this public time. -/
  sign : Fin P.n → Time → Bool := fun _ _ => true

/-- A block-shaped object may refuse delivery of the objects it carries. -/
def BlockShaped : ShapeObj P.n K I B → Prop
  | .mk _ (.item _) _ => True
  | _ => False

variable [DecidableEq I] (C : WireCodec A K I B) (D : Adapter A K I B S)

open Classical in
/-- Dispatch a single receipt. Relay a block only on new acceptance, and relay attestations. -/
noncomputable def processOne (hs : List (Header I × Nat)) (st : S) (o : ShapeObj P.n K I B) : S :=
  match canonEvent C hs o with
  | some (.block b) =>
      let r := Node.onBlock (D.self st) (D.node st) (D.now st) b
      D.relayIf (D.applyCuts st none r)
        ((D.node st).fg.blocks b.root ≠ some b ∧ r.1.fg.blocks b.root = some b) o
  | some (.message m) =>
      D.applyCuts st (some o) (Node.onMessage (D.self st) (D.node st) (D.now st) m)
  | some (.attestation a) =>
      D.relayIf (D.applyCuts st none (Node.onAttestation (D.node st) a)) True o
  | _ => st

/-- Stop descending through a malformed, too early or FG-refused block. -/
def Refuses (hs : List (Header I × Nat)) (st : S) (o : ShapeObj P.n K I B) : Prop :=
  BlockShaped o ∧ ∀ b, canonEvent C hs o = some (.block b) →
    P.slotOf (D.now st) < b.slot ∨ (D.node st).fg.onBlock b = none

open Classical in
mutual
/-- Visit a receipt and its carried objects in preorder, threading the node state. -/
noncomputable def visit (hs : List (Header I × Nat)) :
    S → ShapeObj P.n K I B → List (ShapeObj P.n K I B) × S
  | st, .mk a m cs =>
      if Refuses C D hs st (.mk a m cs) then ([.mk a m cs], processOne C D hs st (.mk a m cs))
      else
        let r := visitList hs (processOne C D hs st (.mk a m cs)) cs
        (.mk a m cs :: r.1, r.2)

/-- Visit a list of carried objects in order. -/
noncomputable def visitList (hs : List (Header I × Nat)) :
    S → List (ShapeObj P.n K I B) → List (ShapeObj P.n K I B) × S
  | st, [] => ([], st)
  | st, c :: cs =>
      let r := visit hs st c
      let r' := visitList hs r.2 cs
      (r.1 ++ r'.1, r'.2)
end

/-- The objects processed for a receipt, including its root even on refusal. -/
noncomputable def delivered (hs : List (Header I × Nat)) (st : S) (o : ShapeObj P.n K I B) :
    List (ShapeObj P.n K I B) := (visit C D hs st o).1

/-- Apply the delivered objects' calls in order. -/
noncomputable def process (st : S) (o : ShapeObj P.n K I B) (hs : List (Header I × Nat)) : S :=
  (delivered C D hs st o).foldl (processOne C D hs) st

open Classical in
/-- Call the node's public tick and set the FG duty from the signing calendar. -/
noncomputable def nodeTick (D : Adapter A K I B S) (st : S) : S :=
  if P.IsPublic (D.now st) then
    let r := Node.acCall (D.self st) (D.node st) (D.now st) .tick
    D.setDue (D.applyCuts st none (r.1, [r.2])) (D.sign (D.self st) (D.now st))
  else st

omit [DecidableEq I] in
/-- Run the AC proposal and supply its parent and payloads to the engine. -/
noncomputable def propose (st : S) (_s : Slot) :
    S × Option (ParentRef × I × List (ShapeObj P.n K I B)) :=
  let r := Node.acProposal (D.node st) (D.now st)
  let st' := D.setNode st r.1
  match r.2.2 with
  | none => (st', none)
  | some (d, p) =>
      let atts := r.1.fg.proposalAttestations d.head
      (st', some (parentRef P.genesisRoot (some d.head.root), C.encode atts p, C.carried atts p))

/-- Apply the own-block call after release provided its digest. -/
noncomputable def recordBlock (st : S) (k : Fin P.n) (h : Header I)
    (hs : List (Header I × Nat)) : S :=
  match C.decode h.info, rootOf hs h with
  | some (atts, p), some d =>
      D.applyCuts st none (Node.onBlock (D.self st) (D.node st) (D.now st) (blockOf d h k atts p))
  | _, _ => st

/-- Read the AC source and run the FG attestation duty: on a signing the record is updated and
the adapter receives the attestation, with the node state before the own `on_attestation`; the
adapter processes the own attestation when it releases it (an unreleased attestation is not in
the own pool). -/
noncomputable def fgUpdate (D : Adapter A K I B S) (st : S) : S :=
  let r := Node.acToFG (D.node st) (D.now st)
  let st₁ := D.setDue (D.setNode st r.1) false
  match r.2.2 with
  | none => st₁
  | some b =>
      match r.1.fg.attest r.1.record (D.self st) b with
      | none => st₁
      | some (a, record) => D.attest st₁ { r.1 with record := record } a

/-- Restart the node, retaining the instance's durable envelope. -/
noncomputable def restore (D : Adapter A K I B S) (k : Fin P.n) (d : S) (t : Time) : S :=
  let r := Node.restart k (D.node d) t
  D.setDue (D.applyCuts (D.wake d k t) none r) false

/-- Read the headers from genesis (excluded) to a block, with bounded parent walk. -/
noncomputable def chainTo {Payload : Type} (header : NodeBlock P Payload → Header I)
    (blocks : Nat → Option (NodeBlock P Payload)) : Nat → NodeBlock P Payload → Chain I
  | 0, _ => []
  | fuel + 1, b =>
      if b.root = P.genesisRoot then []
      else
        (match b.parent.bind blocks with
          | some bp => chainTo header blocks fuel bp
          | none => []) ++ [header b]

/-- Shape operations with a fixed wire type and an explicit state type; `Tok` and `D` are the
vote-authentication evidence and vote data (`Model.VoteIO`) given to `init`. -/
structure Ops (n : Nat) (K I B O State Tok D : Type) where
  init : Fin n → (ShapeRole K → Bool) → Model.VoteIO Tok (ShapeRole K) D n → State
  clock : State → Time → State
  propose : State → Slot → State × Option (ParentRef × I × List (ShapeObj n K I B))
  pollPropose : State → Time → State × Option (ParentRef × Nat × I × List (ShapeObj n K I B))
  poll : State → Time → State × Option (B × List (ShapeObj n K I B))
  pollBatch : State → Time → State × List (B × List (ShapeObj n K I B))
  gossip : State → Time → List (Msg (Header I) B × List (ShapeObj n K I B))
  process : State → ShapeObj n K I B → List (Header I × Nat) → State
  recordOwn : State → ShapeObj n K I B → List (Header I × Nat) → State
  restore : Fin n → State → Time → State
  out : O → State → Chain I

/-- Assemble a polling and slot-proposing chain shape. -/
def shape {pub : Public} [Countable I] [DecidableEq B] (k : Skeleton pub.n)
    {S Tok D : Type} [DecidableEq Tok] [Infinite Tok] [Countable D]
    (g : Ops pub.n k.Kind I B O S Tok D)
    (claim : D → Option (Fin pub.n × ShapeRole k.Kind)) (voteBody : B → Bool)
    (presented : ShapeObj pub.n k.Kind I B → Option ((Fin pub.n × ShapeRole k.Kind × D) × Tok))
    (role : ShapeDuty k.Kind → Msg (Header I) B → Option (ShapeRole k.Kind))
    (dep : DependencyPolicy (ShapeObj pub.n k.Kind I B))
    (conflict : ShapeObj pub.n k.Kind I B → ShapeObj pub.n k.Kind I B → Bool)
    (fg : ShapeObj pub.n k.Kind I B → Prop) : ChainShape pub O I where
  skel := k
  State := S
  Body := B
  Durable := S
  decBody := inferInstance
  Token := Tok
  VoteData := D
  claim := claim
  tokensCover := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat {d : D // (claim d).isSome}
    exact ⟨⟨Infinite.natEmbedding Tok ∘ f, (Infinite.natEmbedding Tok).injective.comp hf⟩⟩
  voteBody := voteBody
  presented := presented
  candidateRole := role
  init := g.init
  clock := g.clock
  propose := g.propose
  act := fun st _ _ => (st, none)
  pollPropose := g.pollPropose
  poll := g.poll
  pollBatch := g.pollBatch
  gossip := g.gossip
  process := g.process
  dependencies := dep
  recordOwn := g.recordOwn
  durable := id
  restore := g.restore
  out := g.out
  conflicts := conflict
  isFGAtt := fg

/-- Lift nonempty-node operations to a public shape. At zero keys it sends and reads nothing. -/
def familyOps {n : Nat} {Tok D : Type} {S : (1 ≤ n) → Type}
    (G : (hn : 1 ≤ n) → Ops n K I B O (S hn) Tok D) :
    Ops n K I B O ((hn : 1 ≤ n) → S hn) Tok D where
  init k p io hn := (G hn).init k p io
  clock st t hn := (G hn).clock (st hn) t
  propose st s :=
    if hn : 1 ≤ n then (fun _ => ((G hn).propose (st hn) s).1, ((G hn).propose (st hn) s).2)
    else (st, none)
  pollPropose st t :=
    if hn : 1 ≤ n then
      (fun _ => ((G hn).pollPropose (st hn) t).1, ((G hn).pollPropose (st hn) t).2)
    else (st, none)
  poll st t :=
    if hn : 1 ≤ n then (fun _ => ((G hn).poll (st hn) t).1, ((G hn).poll (st hn) t).2)
    else (st, none)
  pollBatch st t :=
    if hn : 1 ≤ n then (fun _ => ((G hn).pollBatch (st hn) t).1, ((G hn).pollBatch (st hn) t).2)
    else (st, [])
  gossip st t := if hn : 1 ≤ n then (G hn).gossip (st hn) t else []
  process st o hs hn := (G hn).process (st hn) o hs
  recordOwn st o hs hn := (G hn).recordOwn (st hn) o hs
  restore k d t hn := (G hn).restore k (d hn) t
  out g st := if hn : 1 ≤ n then (G hn).out g (st hn) else []

end Consensus.Goldilocks.NodeAsChainShape

end
