module
public import ConsensusLean.Spec.Shape.Compile
public import ConsensusLean.Instances.Goldilocks.Spec.Run.Goldilocks

@[expose] public section

/-! # The Goldilocks node as a chain shape (Refinement, definitions)

The Goldilocks protocol of `Spec/Run/Goldilocks` (the node of `Spec/Node` over `goldilocksSA`),
written as a generic `ChainShape` so that the engine (`Spec/Model/Run`) runs it and the generic
L1 theorems (`System.NonFraming`, …) apply to it. The statements (`Statements/Refinement`) say
that every engine run of `compile (goldilocksShape sp ro)` is simulated by a `GoldilocksRun`
(claims C0.4 kept) and bind the evidence (G1.5). Decisions (`docs/decisions.md` §"Goldilocks
instance"):

* **Wire format.** A block is a header item signed in role `.proposer s`: `pos` the slot,
  `input` the engine's payload (`Block.input`), `info` the FG payload (the attestation list)
  and the AC payload (votes, support votes) in an `n`-independent encoding (`WireAtt`,
  `WireVote`: the validator index as a number; a header is read back through `decodeInfo`, and
  a block whose indices do not decode is dropped). A vote and an attestation are `.data` bodies
  signed in the `.poll` role by their validator (`voteObj`, `attObj`); a block **carries** the
  canonical objects of its payload (`payloadObjs`), so a node can later carry them on in its own
  blocks (the engine releases only carried objects it has seen). A received object is processed
  only in a canonical form (`blockObj`, `voteObj`, `attObj`; read back by `decodeBlock`,
  `decodeVoteObj`, `decodeAttObj`, together `canonEvent`), anything else is dropped.
* **Digest.** The engine hashes the header; the node's digest is `dgOf hash g`: `none ↦ g` (the
  genesis root is a parameter) and `some r ↦ hash` of the header with parent `.root` when
  `r = g`, `.digest r` otherwise (`parentRef`). A header whose parent is `.digest g` is dropped
  (it would name genesis by a second parent), so every admitted block satisfies `RootOk` by
  construction, without the shape evaluating the hash.
* **Steps.** `order := [.poll, .poll, .pollPropose, .propose, .poll, .poll]` and
  `deliverOrder := [.poll]`. A poll step releases the oldest queued body (an emitted vote or a
  signed attestation) and, when the node's tick has made it due, first runs the FG update. The
  poll at a delivery releases the vote the delivery emitted, if any (at most one: the node
  votes once per slot), at the delivery's own time; the FG update is due only between a tick's
  poll proposal step and its first trailing poll, never at a delivery, so the delivery poll is
  a drain. The two leading polls of a tick release what a restart emitted (a restart releases
  nothing itself), so that a proposal of this tick carries only released objects (the engine
  releases a block only if it has seen everything it carries). The poll proposal step never
  proposes: it is the node's tick (`ac_on_tick`) at the public times, as a duty so that it runs
  only while the node is awake (the engine's `clock` runs asleep too, and only keeps the time).
  The slot proposal step is C0.4's proposal step (`ac_proposal`, then the own `on_block`
  through `recordOwn`, which brings the digest). The first trailing poll runs the FG update
  (`ac_to_fg`, then `attest`, written out as `Node.tickStep … .fgUpdate` does) and queues the
  attestation; the two trailing polls drain the tick's at most one vote and one attestation.
* **Relay.** An admitted object (a block held after the call, a vote the pool holds, an
  attestation) is relayed at the gossip of the event that admitted it (a delivery or a tick) as
  a carried object of an unsigned `.relay` wrapper; a delivery's emission and relay leave at the
  delivery's own time (`Model.Run.deliver`), as the spec's relay rule sends them.
* **Restart.** Everything is durable (the spec keeps `Σ`, `𝒜`, `Λ` and restarts the AC); the
  queued bodies are kept and leave at the tick that follows the restart at the wake time.
* **Outputs.** `confirmed` is `ac_confirmed`, `finalized` is `Σ.F`, each as the chain of
  headers from genesis (excluded) to the block, read from `Σ.T` by parent walk (fuel: the slot).
* **Slashing rule.** `conflicts` is `FG.slashable` on two canonical attestation objects.
* **Family.** `family S` fixes the public parameters from `pub` (`Δ`, `n`) and the rest from a
  `Setup`. `Params` needs `1 ≤ n`; the family keeps that dependence out of its types
  (`FamilyState`), so that a run's state is a Goldilocks state at any proof of `1 ≤ n`. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape
open Consensus.Model (Public Key SelSpec Obj Msg)
open SA (SAParams ReplayOrder goldilocksSA Vote Payload)

/-! ## Wire types -/

/-- The output identifiers of the Goldilocks shape. -/
inductive Out where
  | confirmed
  | finalized
  deriving DecidableEq, Repr

/-- The schema: `confirmed` serves the available and the stable capability, `finalized` the
final one. -/
def schema : OutputSchema :=
  ⟨Out, fun
    | .available => some .confirmed
    | .stable => some .confirmed
    | .final => some .finalized⟩

/-- An attestation on the wire: `FG.Att` with the validator index as a number. -/
structure WireAtt where
  val : Nat
  h : Nat
  T : Nat
  timeout : Bool
  fin : Option (Nat × Nat)
  deriving DecidableEq

/-- `WireAtt` as a tuple. -/
def WireAtt.equiv : WireAtt ≃ Nat × Nat × Nat × Bool × Option (Nat × Nat) where
  toFun a := (a.val, a.h, a.T, a.timeout, a.fin)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `WireAtt` is countable through `WireAtt.equiv`. -/
instance : Countable WireAtt := WireAtt.equiv.injective.countable

/-- A vote on the wire: `SA.Vote` with the validator index as a number. -/
structure WireVote where
  val : Nat
  slot : Nat
  head : Nat
  deriving DecidableEq

/-- `WireVote` as a tuple. -/
def WireVote.equiv : WireVote ≃ Nat × Nat × Nat where
  toFun v := (v.val, v.slot, v.head)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `WireVote` is countable through `WireVote.equiv`. -/
instance : Countable WireVote := WireVote.equiv.injective.countable

/-- A header's protocol data: the attestation list, the votes and the support votes. -/
abbrev Info := List WireAtt × List WireVote × List WireVote

/-- The encoding of an attestation. -/
def encodeAtt {n : Nat} (a : FG.Att n) : WireAtt := ⟨a.val, a.h, a.T, a.timeout, a.fin⟩

/-- The decoding of an attestation; none if the index is not a validator. -/
def decodeAtt (n : Nat) (w : WireAtt) : Option (FG.Att n) :=
  if h : w.val < n then some ⟨⟨w.val, h⟩, w.h, w.T, w.timeout, w.fin⟩ else none

/-- The encoding of a vote. -/
def encodeVote {n : Nat} (v : Vote n) : WireVote := ⟨v.val, v.slot, v.head⟩

/-- The decoding of a vote; none if the index is not a validator. -/
def decodeVote (n : Nat) (w : WireVote) : Option (Vote n) :=
  if h : w.val < n then some ⟨⟨w.val, h⟩, w.slot, w.head⟩ else none

/-- The header data of a block with attestations `atts` and AC payload `p`. -/
def encodeInfo {n : Nat} (atts : List (FG.Att n)) (p : Payload n) : Info :=
  (atts.map encodeAtt, p.1.map encodeVote, p.2.map encodeVote)

/-- The attestations and the AC payload a header's data encodes, if every index decodes. -/
def decodeInfo (n : Nat) (i : Info) : Option (List (FG.Att n) × Payload n) := do
  let atts ← i.1.mapM (decodeAtt n)
  let votes ← i.2.1.mapM (decodeVote n)
  let support ← i.2.2.mapM (decodeVote n)
  pure (atts, (votes, support))

/-- The protocol data a node signs in the `.poll` role, or relays unsigned (`n`-independent, as
`Info`: the family fixes one body type for every parameter set). -/
inductive Body where
  /-- A Goldfish vote (an AC message). -/
  | vote (v : WireVote)
  /-- An FG attestation. -/
  | att (a : WireAtt)
  /-- The unsigned relay wrapper; its carried objects are the relayed ones. -/
  | relay
  /-- Forwarding tag with a claimed acceptance time. Authentication and actual acceptance
  provenance are established separately. -/
  | forward (acceptedAt : Time)
  deriving DecidableEq

/-- The wire objects of the shape (no committee kinds). -/
abbrev Wire (n : Nat) := ShapeObj n Empty Info Body

/-- The exact dependency reference of a parent-bearing forwarding shape. This computable
projection needs no protocol parameters or digests and certifies no validity or provenance.
Raw blocks and genesis-wrapper shapes have no dependency reference. -/
def forwardParent? {n : Nat} : Wire n → Option (Wire n)
  | .mk (.signed _ .poll) (.data (.forward _)) [parent, _] => some parent
  | _ => none

/-- The canonical object of a vote: signed by its validator in the `.poll` role, carrying
nothing. -/
def voteObj {n : Nat} (v : Vote n) : Wire n :=
  .mk (.signed v.val .poll) (.data (.vote (encodeVote v))) []

/-- The canonical object of an attestation: signed by its validator in the `.poll` role,
carrying nothing. -/
def attObj {n : Nat} (a : FG.Att n) : Wire n :=
  .mk (.signed a.val .poll) (.data (.att (encodeAtt a))) []

/-- The objects a block carries: the canonical objects of its attestations, then of its votes
and support votes. -/
def payloadObjs {n : Nat} (atts : List (FG.Att n)) (p : Payload n) : List (Wire n) :=
  atts.map attObj ++ (p.1 ++ p.2).map voteObj

/-- The slashing rule: two canonical attestation objects whose attestations are `slashable`
(E1/E2 of fg.tex). -/
def conflicts {n : Nat} : Wire n → Wire n → Bool
  | .mk (.signed k .poll) (.data (.att w)) [], .mk (.signed k' .poll) (.data (.att w')) [] =>
      match decodeAtt n w, decodeAtt n w' with
      | some a, some b => decide (k = a.val ∧ k' = b.val ∧ FG.slashable a b)
      | _, _ => false
  | _, _ => false

/-- The header's parent reference of a block parent named by root, with genesis root `g`:
genesis is `.root`, any other root a `.digest`. -/
def parentRef (g : Nat) : Option Nat → ParentRef
  | none => .root
  | some r => if r = g then .root else .digest r

/-- The block parent (by root) a header's parent reference names, with genesis root `g`. -/
def parentRoot (g : Nat) : ParentRef → Option Nat
  | .root => some g
  | .digest r => some r

/-- The node's digest from the engine's hash with genesis root `g`: genesis (no parent) has
root `g`; any other block's root is the hash of its header (`parentRef` for the parent). -/
def dgOf {n : Nat} (hash : Header Info → Nat) (g : Nat) : Digest (List (FG.Att n)) (Payload n) :=
  fun par slot x atts p =>
    match par with
    | none => g
    | some r => hash ⟨parentRef g (some r), slot, x, encodeInfo atts p⟩

/-- The digest of header `h` among the digests `hs` the engine passed. -/
def rootOf (hs : List (Header Info × Nat)) (h : Header Info) : Option Nat :=
  (hs.find? fun q => q.1 == h).map (·.2)

/-! ## The shape -/

variable (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))

/-- The public parameters of `sp`. -/
abbrev _root_.Consensus.Goldilocks.SA.SAParams.pub : Public := ⟨sp.n, sp.Δ, sp.toParams.hΔ⟩

/-- A node block of the Goldilocks node. -/
abbrev Blk := NodeBlock sp.toParams (Payload sp.n)

/-- The header of a non-genesis block (its root is the digest of this header). -/
def headerOf (B : Blk sp) : Header Info :=
  ⟨parentRef sp.genesisRoot B.parent, B.slot, B.input, encodeInfo B.fgPayload B.acPayload⟩

/-- The block of a header `h` with digest `d`, signed by `k`, with the decoded payloads. -/
def blockOf (d : Nat) (h : Header Info) (k : Fin sp.n) (atts : List (FG.Att sp.n))
    (p : Payload sp.n) : Blk sp :=
  ⟨d, parentRoot sp.genesisRoot h.parent, h.pos, k, h.input, atts, p⟩

/-- The skeleton at the proposer schedule `proposer` (an index reduced modulo `n`, as in
`Setup`): slots of `4Δ`, the schedule's proposer at every slot (the key `proposer s % n`; no key
when `n = 0`), everyone in the poll role, no committee kinds; two poll steps (the release of the
bodies queued since the last tick), the node's tick as the poll proposal step, the slot proposal,
then two poll steps (the FG update and the release of the tick's bodies); one poll step at every
delivery (the release of the vote the delivery emitted, if any; the FG update is never due at a
delivery). -/
def skeleton (pub : Public) (proposer : Nat → Nat) : Skeleton pub.n where
  grid := ⟨4 * pub.Δ, mul_pos (by decide) pub.Δ_pos⟩
  proposerSel := fun s => .fixed
    (Finset.univ.filter fun k : Fin pub.n => k.val = proposer s % pub.n)
  pollSel := .fixed Finset.univ
  Kind := Empty
  decKind := inferInstance
  kinds := []
  phase := fun k => k.elim
  kindSel := fun k => k.elim
  order := [.poll, .poll, .pollPropose, .propose, .poll, .poll]
  deliverOrder := [.poll]

/-- The shape's state: the own key, the node state `(Σ, 𝒜, Λ)`, the current time (set by the
clock), the bodies emitted or signed and not yet released, the admitted objects not yet relayed,
and whether the FG update of the current tick is due. -/
structure State where
  /-- The own validator index. -/
  self : Fin sp.n
  /-- The node state. -/
  node : NodeState (goldilocksNode sp ro)
  /-- The time of the last tick (or restart). -/
  now : Time
  /-- Bodies to sign and release, oldest first. -/
  outbox : List Body
  /-- Admitted objects to relay at the next gossip. -/
  relayBuf : List (Wire sp.n)
  /-- The FG update of this tick has not run yet. -/
  fgDue : Bool

variable {sp ro}

/-- The votes the cuts emit, as bodies to release. -/
def emitted (cs : List (Cut (goldilocksNode sp ro))) : List Body :=
  cs.flatMap fun
    | .ac ℓ => ℓ.emits.map fun e => .vote (encodeVote e.msg)
    | .fg _ => []

/-- The state after a handler's result: its node state, its emissions queued. -/
def apply (st : State sp ro)
    (r : NodeState (goldilocksNode sp ro) × List (Cut (goldilocksNode sp ro))) : State sp ro :=
  { st with node := r.1, outbox := st.outbox ++ emitted r.2 }

/-- Queue `o` for relay if `c`. -/
def relayIf (st : State sp ro) (c : Prop) [Decidable c] (o : Wire sp.n) : State sp ro :=
  if c then { st with relayBuf := st.relayBuf ++ [o] } else st

variable (sp) in
/-- The canonical object of a non-genesis block: its header as an item signed by its proposer in
its slot's proposer role, carrying its payload's objects. -/
def blockObj (B : Blk sp) : Wire sp.n :=
  .mk (.signed B.proposer (.proposer B.slot)) (.item (headerOf sp B))
    (payloadObjs B.fgPayload B.acPayload)

variable (sp) in
open Classical in
/-- The block a received object is the canonical object of, given the digests `hs` the engine
passed: a header signed in its slot's proposer role, whose indices decode, with a digest, not
naming genesis by digest, carrying its payload's objects, with well-formed attestations and a
valid AC payload. Such an object is `blockObj` of the block it decodes to. -/
noncomputable def decodeBlock (hs : List (Header Info × Nat)) : Wire sp.n → Option (Blk sp)
  | .mk (.signed k (.proposer s)) (.item h) cs =>
      match decodeInfo sp.n h.info, rootOf hs h with
      | some (atts, p), some d =>
          let B := blockOf sp d h k atts p
          if h.pos = s ∧ h.parent ≠ .digest sp.genesisRoot ∧ cs = payloadObjs atts p ∧
              (∀ a ∈ atts, a.WellFormed) ∧ SA.validPayload B then some B
          else none
      | _, _ => none
  | _ => none

variable (sp) in
/-- A signed forwarding wrapper. The optional exact parent wrapper precedes the canonical
child block, so recursive delivery processing replays the parent first. Construction alone
does not certify acceptance, freshness, or dependency readiness. -/
def forwardObj (origin : Fin sp.n) (acceptedAt : Time) (parent : Option (Wire sp.n))
    (B : Blk sp) : Wire sp.n :=
  .mk (.signed origin .poll) (.data (.forward acceptedAt))
    (parent.toList ++ [blockObj sp B])

variable (sp) in
open Classical in
/-- Parse a canonical authenticated forwarding chain, using the same engine digests for all
nested blocks. A parent wrapper has the same origin, an earlier slot and no later timestamp.
The genesis-root parent terminates the chain. These are wire checks only: actual acceptance
and first-release provenance must be established separately for honest origins. -/
noncomputable def decodeForward (hs : List (Header Info × Nat)) :
    Wire sp.n → Option (Fin sp.n × Time × Option (Wire sp.n) × Blk sp)
  | .mk (.signed origin .poll) (.data (.forward t)) [child] => do
      let B ← decodeBlock sp hs child
      if child = blockObj sp B ∧ B.parent = some sp.genesisRoot ∧
          0 ≤ t ∧ sp.toParams.slotTime B.slot ≤ t then
        some (origin, t, none, B)
      else none
  | .mk (.signed origin .poll) (.data (.forward t)) [parent, child] => do
      let B ← decodeBlock sp hs child
      let (parentOrigin, parentTime, _, A) ← decodeForward hs parent
      if child = blockObj sp B ∧ parentOrigin = origin ∧ B.parent = some A.root ∧
          A.root ≠ sp.genesisRoot ∧ A.slot < B.slot ∧ parentTime ≤ t ∧
          0 ≤ t ∧ sp.toParams.slotTime B.slot ≤ t then
        some (origin, t, some parent, B)
      else none
  | _ => none
termination_by o => sizeOf o

variable (sp) in
/-- The vote a received object is the canonical object of (`voteObj`): signed by its validator
in the `.poll` role, carrying nothing. -/
def decodeVoteObj : Wire sp.n → Option (Vote sp.n)
  | .mk (.signed k .poll) (.data (.vote w)) [] =>
      (decodeVote sp.n w).filter fun v => k = v.val
  | _ => none

variable (sp) in
/-- The well-formed attestation a received object is the canonical object of (`attObj`): signed
by its validator in the `.poll` role, carrying nothing. -/
def decodeAttObj : Wire sp.n → Option (FG.Att sp.n)
  | .mk (.signed k .poll) (.data (.att w)) [] =>
      (decodeAtt sp.n w).filter fun a => k = a.val ∧ a.WellFormed
  | _ => none

variable (sp ro) in
/-- The node's top-level event a received object stands for, given the digests `hs`: the block,
vote or attestation it is the canonical object of; none for anything else (dropped). -/
noncomputable def canonEvent (hs : List (Header Info × Nat)) (o : Wire sp.n) :
    Option (Node.Event (goldilocksNode sp ro)) :=
  match decodeBlock sp hs o, decodeVoteObj sp o, decodeAttObj sp o with
  | some B, _, _ => some (.block B)
  | none, some v, _ => some (.message v)
  | none, none, some a => some (.attestation a)
  | none, none, none => none

open Classical in
/-- Processing one received object: its `canonEvent` through the node's handler (`on_block`,
`on_ac_message`, `on_attestation`); anything else is dropped. An admitted object (a block the
tree holds after the call, a vote the pool holds, any attestation) is queued for relay. -/
noncomputable def processOne (hs : List (Header Info × Nat)) (st : State sp ro) (o : Wire sp.n) :
    State sp ro :=
  match canonEvent sp ro hs o with
  | some (.block B) =>
      let r := Node.onBlock st.self st.node st.now B
      relayIf (apply st r) (r.1.fg.blocks B.root = some B) o
  | some (.message v) =>
      let r := Node.onMessage st.self st.node st.now v
      relayIf (apply st r) (v ∈ r.1.ac.pool v.slot) o
  | some (.attestation a) => relayIf (apply st (Node.onAttestation st.node a)) True o
  | _ => st

variable (sp) in
/-- The objects a delivery processes, in preorder: the received object, then recursively every
carried object. Noncanonical wrappers make no node call. A canonical block is processed before
its payload votes and attestations, which receive their own message/attestation calls even if
the block is refused. Thus admitting a payload vote is followed by actual message processing
at the same delivery time, rather than merely adding it to the AC pool. -/
def delivered (o : Wire sp.n) : List (Wire sp.n) := o.parts

/-- Processing a delivered object: its `delivered` objects one by one through `processOne`. -/
noncomputable def process (st : State sp ro) (o : Wire sp.n) (hs : List (Header Info × Nat)) :
    State sp ro :=
  (delivered sp o).foldl (processOne hs) st

/-- Every forwarding shape requires its exact parent wrapper to be held before
the envelope. Raw blocks have no dependency. Parsing and honest provenance,
not this shape-only policy, establish same-origin acceptance and freshness. -/
def dependencies (n : Nat) : Model.DependencyPolicy (Wire n) where
  ready held o := o.parts.all fun part =>
    match forwardParent? part with
    | none => true
    | some parent => decide (parent ∈ held)
  mono := by
    intro held held' o hsub h
    simp only [List.all_eq_true] at h ⊢
    intro part hp
    specialize h part hp
    cases hi : forwardParent? part with
    | none => simp
    | some parent =>
      simp only [hi, decide_eq_true_eq] at h ⊢
      exact hsub h

/-- The node's cuts for the engine's delivery of the objects `os` to `y` at time `t`, given the
digests `hs`, from cut `j` to cut `j'`: in order, one top-level event (`canonEvent`) per
canonical object, its group at the next cut; nothing for a dropped object, nor for a canonical
object whose handler makes no cut (a future-slot block, which `onBlock` refuses silently). -/
inductive DeliverSeq (tr : GoldilocksTrace sp ro) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (y : Fin sp.n) (t : Time) :
    List (Wire sp.n) → Nat → Nat → Prop
  /-- No object, no cut. -/
  | nil (j : Nat) : DeliverSeq tr dg hs y t [] j j
  /-- A canonical object: its event's group starts at `j`, and the rest follow it. -/
  | event {o : Wire sp.n} {os : List (Wire sp.n)} {j j' : Nat}
      (e : Node.Event (goldilocksNode sp ro)) : canonEvent sp ro hs o = some e →
      tr.GroupAt dg y j t e →
      DeliverSeq tr dg hs y t os (j + (Node.exec dg y (tr.state y j) t e).2.length) j' →
      DeliverSeq tr dg hs y t (o :: os) j j'
  /-- A dropped object has no cut. -/
  | drop {o : Wire sp.n} {os : List (Wire sp.n)} {j j' : Nat} : canonEvent sp ro hs o = none →
      DeliverSeq tr dg hs y t os j j' → DeliverSeq tr dg hs y t (o :: os) j j'
  /-- A canonical object whose handler makes no cut (a future-slot block) is not an event of the
  run (`GroupAt` needs a cut), so it has no cut either. -/
  | noCut {o : Wire sp.n} {os : List (Wire sp.n)} {j j' : Nat}
      (e : Node.Event (goldilocksNode sp ro)) : canonEvent sp ro hs o = some e →
      (Node.exec dg y (tr.state y j) t e).2 = [] →
      DeliverSeq tr dg hs y t os j j' → DeliverSeq tr dg hs y t (o :: os) j j'

/-- Recording an own released object: the relay wrapper empties the relay queue; the own block
(now with its digest) goes through the own `on_block`, as `propose_block` does; a released vote
or attestation was admitted when emitted or signed. -/
noncomputable def recordOwn (st : State sp ro) (o : Wire sp.n) (hs : List (Header Info × Nat)) :
    State sp ro :=
  match o with
  | .mk .none (.data .relay) _ => { st with relayBuf := [] }
  | .mk (.signed k (.proposer _)) (.item h) _ =>
      match decodeInfo sp.n h.info, rootOf hs h with
      | some (atts, p), some d =>
          apply st (Node.onBlock st.self st.node st.now (blockOf sp d h k atts p))
      | _, _ => st
  | _ => st

open Classical in
/-- The node's tick at a public time: `ac_on_tick`, its votes queued, the FG update made due. -/
noncomputable def nodeTick (st : State sp ro) : State sp ro :=
  if sp.toParams.IsPublic st.now then
    let r := Node.acCall st.self st.node st.now .tick
    { apply st (r.1, [r.2]) with fgDue := true }
  else st

/-- The slot proposal of the slot's proposer: `ac_proposal`; the header names the head and
carries the proposal's attestations (`proposal_attestations`) and the AC payload. The engine
writes the slot and the input and signs; the own `on_block` runs in `recordOwn`. -/
noncomputable def propose (st : State sp ro) (s : Slot) :
    State sp ro × Option (ParentRef × Info × List (Wire sp.n)) :=
  if sp.toParams.proposer s = st.self then
    let r := Node.acProposal st.node st.now
    let st' := { st with node := r.1 }
    match r.2.2 with
    | none => (st', none)
    | some (d, p) =>
        let atts := r.1.fg.proposalAttestations d.head
        (st', some (parentRef sp.genesisRoot (some d.head.root), encodeInfo atts p,
          payloadObjs atts p))
  else (st, none)

/-- The FG update: `ac_to_fg`, then `attest(C)` at the source `C` it returns (`fg_attest`; when
it signs, the new record, the own `on_attestation` and the attestation queued), as
`Node.tickStep … .fgUpdate`. -/
noncomputable def fgUpdate (st : State sp ro) : State sp ro :=
  let r := Node.acToFG st.node st.now
  let st₁ := { st with node := r.1, fgDue := false }
  match r.2.2.1 with
  | none => st₁
  | some C =>
      match r.1.fg.attest r.1.record st.self C with
      | none => st₁
      | some (a, Λ') =>
          { st₁ with node := (Node.onAttestation { r.1 with record := Λ' } a).1,
                     outbox := st₁.outbox ++ [.att (encodeAtt a)] }

/-- A poll step: the FG update when due, then the oldest queued body is released. -/
noncomputable def poll (st : State sp ro) (_ : Time) :
    State sp ro × Option (Body × List (Wire sp.n)) :=
  let st₁ := if st.fgDue then fgUpdate st else st
  match st₁.outbox with
  | [] => (st₁, none)
  | b :: rest => ({ st₁ with outbox := rest }, some (b, []))

/-- The chain of headers from genesis (excluded) to `B`, oldest first, by parent walk in the
held blocks `blocks`, with `fuel` steps at most. -/
noncomputable def chainTo (blocks : Nat → Option (Blk sp)) : Nat → Blk sp → Chain Info
  | 0, _ => []
  | fuel + 1, B =>
      if B.root = sp.genesisRoot then []
      else
        (match B.parent.bind blocks with
          | some Bp => chainTo blocks fuel Bp
          | none => []) ++ [headerOf sp B]

/-- The output chains of a node state at time `t`: `finalized` is `Σ.F`, `confirmed` is
`ac_confirmed(𝒜, fg_to_ac(Σ), t)`; each as the chain of headers up to it (fuel: the slot, which
bounds the height). -/
noncomputable def outOf (st : NodeState (goldilocksNode sp ro)) (t : Time) : Out → Chain Info
  | .finalized => chainTo st.fg.blocks (st.fg.F.slot + 1) st.fg.F
  | .confirmed =>
    let C := (goldilocksNode sp ro).confirmed st.ac (Node.frame st) t
    chainTo st.fg.blocks (C.slot + 1) C

/-- A restart at time `t`: `ac_restart` (its emissions queued), the time set, no FG update due;
`Σ`, `𝒜`, `Λ`, the queued bodies and the relay queue are kept. -/
noncomputable def restore (k : Fin sp.n) (d : State sp ro) (t : Time) : State sp ro :=
  let r := Node.restart k d.node t
  { apply { d with self := k, now := t } r with fgDue := false }

variable (sp ro) in
/-- The Goldilocks node as a chain shape over its public parameters. -/
noncomputable def goldilocksShape : ChainShape sp.pub Out Info where
  skel := skeleton sp.pub fun s => (sp.toParams.proposer s).val
  State := State sp ro
  Body := Body
  Durable := State sp ro
  decBody := inferInstance
  init k := ⟨k, Node.init (goldilocksNode sp ro), 0, [], [], false⟩
  clock st t := { st with now := t }
  propose := propose
  act := fun _ _ k => k.elim
  pollPropose st _ := (nodeTick st, none)
  poll := poll
  gossip st _ :=
    match st.relayBuf with
    | [] => []
    | cs => [(.data .relay, cs)]
  process := process
  dependencies := dependencies sp.n
  recordOwn := recordOwn
  durable := id
  restore := restore
  out g st := outOf st.node st.now g
  conflicts := conflicts

/-! ## The family -/

/-- The parameters of the Goldilocks node not fixed by the public parameters: the proposer
schedule (reduced modulo `n`), the genesis root, the FG timeout `δ_t`, the lock window `k`, and
the restart replay order at every parameter set. -/
structure Setup where
  /-- The proposer of slot `s`, as an index reduced modulo `n`. -/
  proposer : Nat → Nat
  /-- The genesis root. -/
  genesisRoot : Nat
  /-- The FG timeout parameter `δ_t`. -/
  δt : Nat
  /-- The lock window `k ≥ 2`. -/
  k : Nat
  two_le_k : 2 ≤ k
  /-- The restart replay order of the SA. -/
  ro : (sp : SAParams) → ReplayOrder sp (List (FG.Att sp.n))

/-- The SA parameters at the public parameters `pub` (with `n ≥ 1`): slots of `4Δ`, the
proposer schedule modulo `n`. -/
def Setup.params (S : Setup) (pub : Public) (hn : 1 ≤ pub.n) : SAParams where
  toParams :=
    { n := pub.n
      hn := hn
      Δ := pub.Δ
      hΔ := pub.Δ_pos
      slotTime := fun s => 4 * pub.Δ * s
      slotTime_zero := by simp
      slotTime_strictMono := fun a b h =>
        mul_lt_mul_of_pos_left (by exact_mod_cast h) (by have := pub.Δ_pos; linarith)
      slotTime_public := fun s => ⟨4 * s, by ring⟩
      proposer := fun s => ⟨S.proposer s % pub.n, Nat.mod_lt _ hn⟩
      genesisRoot := S.genesisRoot
      δt := S.δt }
  slotTime_eq := fun _ => rfl
  k := S.k
  two_le_k := S.two_le_k

/-- The shape's state at the public parameters `pub`: a Goldilocks state at every proof that
`pub` has a validator. The dependence on `1 ≤ n` (which `Params` needs) is thus in the state's
*values*, never in the family's types: `(family S pub).State` is this function type, `.Body`
is `Body`, `.skel.Kind` is `Empty`, and a run's state at `hn` is `st hn : State …` without a
cast. Without a validator there are no keys, no duties with an effect and no outputs. -/
def FamilyState (S : Setup) (pub : Public) : Type :=
  (hn : 1 ≤ pub.n) → State (S.params pub hn) (S.ro _)

/-- The Goldilocks family: `goldilocksShape` at `S.params pub hn` for every `hn`, through
`FamilyState`; the steps that output something (a proposal, a poll body, the gossip, the
output chains) output it at some proof of `1 ≤ n` and nothing without one. -/
noncomputable def family (S : Setup) : ShapeFamily schema Info := fun pub =>
  let G := fun hn : 1 ≤ pub.n => goldilocksShape (S.params pub hn) (S.ro _)
  { skel := skeleton pub S.proposer
    State := FamilyState S pub
    Body := Body
    Durable := FamilyState S pub
    decBody := inferInstance
    init := fun k hn => (G hn).init k
    clock := fun st t hn => (G hn).clock (st hn) t
    propose := fun st s =>
      if hn : 1 ≤ pub.n then (fun _ => ((G hn).propose (st hn) s).1, ((G hn).propose (st hn) s).2)
      else (st, none)
    act := fun _ _ k => k.elim
    pollPropose := fun st t =>
      if hn : 1 ≤ pub.n then
        (fun _ => ((G hn).pollPropose (st hn) t).1, ((G hn).pollPropose (st hn) t).2)
      else (st, none)
    poll := fun st t =>
      if hn : 1 ≤ pub.n then (fun _ => ((G hn).poll (st hn) t).1, ((G hn).poll (st hn) t).2)
      else (st, none)
    gossip := fun st t => if hn : 1 ≤ pub.n then (G hn).gossip (st hn) t else []
    process := fun st o hs hn => (G hn).process (st hn) o hs
    dependencies := dependencies pub.n
    recordOwn := fun st o hs hn => (G hn).recordOwn (st hn) o hs
    durable := id
    restore := fun k d t hn => (G hn).restore k (d hn) t
    out := fun g st => if hn : 1 ≤ pub.n then (G hn).out g (st hn) else []
    conflicts := conflicts }

end Consensus.Goldilocks.Refinement

end
