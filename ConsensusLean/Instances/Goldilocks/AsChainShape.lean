module
public import ConsensusLean.Spec.Shape.Compile
public import ConsensusLean.Instances.Goldilocks.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Spec.Node.Handlers
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # The Goldilocks node as a chain shape (definitions)

The Goldilocks protocol of `Spec/Run/Goldilocks` (the node of `Spec/Node` over `goldilocksSA`),
written as a generic `ChainShape` so that the engine (`Spec/Model/Run`) runs it and the generic
L1 theorems (`System.NonFraming`, …) apply to it. The simulation statements
(`Lemmas/Simulation/Interface`) say that every engine run of `compile (goldilocksShape sp ro)` is
simulated by a `GoldilocksRun` (claims C0.4 kept) and bind the evidence (G1.5). Decisions
(`docs/decisions.md` §"Goldilocks model choices"):

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
* **Digest.** The engine hashes the header; the node's digest is `dgOf hash g`
  (`dgOf`, `Lemmas/Simulation/TraceDefs`): `none ↦ g` (the genesis root is a parameter) and
  `some r ↦ taggedRoot g (hash header)`. The injective tag
  reserves `g` for genesis; `parentRef` decodes other node roots to raw engine digests.
  In particular, `.digest g` names a non-genesis block, not a second genesis representation.
  Every admitted block satisfies `RootOk` without the shape evaluating the hash.
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
* **Relay.** An admitted block or attestation is relayed at the gossip of its event as
  a carried object of an unsigned `.relay` wrapper; a delivery's emission and relay leave at the
  delivery's own time (`Model.Run.deliver`), as the spec's relay rule sends them.
  Fresh vote insertions instead queue `.voteForward` envelopes, signed by the admitting node
  and stamped with its admission time. The envelope carries the canonical vote, which recursive
  delivery visits again. Restart replay does not create vote envelopes.
  Separately, successful block acceptance cuts queue fresh signed `.forward` wrappers, including
  own proposals. The durable node-root map supplies exact same-origin parent wrappers. A selected
  `pollBatch` emits its ordinary body, block wrappers in acceptance order, then vote envelopes;
  `releaseAll` checks each against actual prefix holdings. Duplicate/refused calls do not mint
  wrappers. Unsigned compatibility relay is retained, but certifies no acceptance timestamp.
* **Restart.** `durable` keeps the whole state and `restore` applies `ac_restart`: as in the
  spec (composition.tex §"State"), `Σ` and `Λ` are kept and `𝒜` is replaced by
  `ac_restart(𝒜, Φ, t)`, which keeps only the locks and the latest confirmation. The queued
  bodies are kept and leave at the tick that follows the restart at the wake time.
* **Outputs.** `confirmed` is `ac_confirmed`, `finalized` is `Σ.F`, each as the chain of
  headers from genesis (excluded) to the block, read from `Σ.T` by parent walk (fuel: the slot).
* **Slashing rule.** `conflicts` is `FG.slashable` on two canonical attestation objects.
* **Family.** `goldilocks S` fixes the public parameters from `pub` (`ΔAC`, `n`) and the rest from a
  `Setup`. `Params` needs `1 ≤ n`; the family keeps that dependence out of its types
  (`PubState`), so that a run's state is a Goldilocks state at any proof of `1 ≤ n`. -/

namespace Consensus.Goldilocks.AsChainShape

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
  /-- A fresh vote admission, authenticated by the enclosing poll signer rather than the
  vote's author. The carried canonical vote is processed recursively. -/
  | voteForward (admittedAt : Time) (vote : WireVote)
  deriving DecidableEq

/-- The historical roles and public selection used by available-chain votes. -/
structure VoteBinding where
  /-- Signing kinds, independent of scheduled actions. -/
  Kind : Type
  decKind : DecidableEq Kind
  /-- Public selection specification for each kind. -/
  kindSel : (pub : Public) → Kind → SelSpec pub.n
  /-- The kind observed by available-chain participation. -/
  participationKind : Option Kind
  /-- Every kind's selection is nonempty at a nonempty population: a sized selection asks for at
  least one key, a fixed one names at least one. -/
  committeeSize_pos : ∀ (pub : Public) (k : Kind), 0 < pub.n →
    match kindSel pub k with
    | .sized m => 1 ≤ m
    | .fixed keys => keys.Nonempty

attribute [instance] VoteBinding.decKind

/-- Vote authentication uses the same kind as public participation. -/
def VoteBinding.voteRole (B : VoteBinding) (s : Slot) : ShapeRole B.Kind :=
  match B.participationKind with
  | none => .poll
  | some k => .duty s k

/-- The available-chain denominator is the size admitted by the participation selection. -/
def VoteBinding.committeeSize (B : VoteBinding) (pub : Public) : Nat :=
  match B.participationKind with
  | none => pub.n
  | some k => match B.kindSel pub k with
    | .sized m => min m pub.n
    | .fixed keys => keys.card

/-- Population-wide votes retain the poll role and the original empty kind. -/
def stock : VoteBinding where
  Kind := Empty
  decKind := inferInstance
  kindSel := fun _ k => k.elim
  participationKind := none
  committeeSize_pos := fun _ k => k.elim

/-- The historical committee vote role; no additional scheduled action is needed. -/
inductive VoteKind where
  | vote
  deriving DecidableEq

/-- A committee uses the same codec and state machine as the population binding. Its selection is
nonempty at every nonempty population (`hsel`). -/
def committee (selection : (pub : Public) → SelSpec pub.n)
    (hsel : ∀ pub : Public, 0 < pub.n →
      match selection pub with
      | .sized m => 1 ≤ m
      | .fixed keys => keys.Nonempty) : VoteBinding where
  Kind := VoteKind
  decKind := inferInstance
  kindSel := fun pub _ => selection pub
  participationKind := some .vote
  committeeSize_pos := fun pub _ => hsel pub

/-- Classify historical votes; other bodies retain their duty's signing role.
The population binding leaves all signing to the original duty classifier. -/
def VoteBinding.candidateRole (B : VoteBinding) (n : Nat)
    (_ : ShapeDuty B.Kind) : Msg (Header Info) Body → Option (ShapeRole B.Kind) :=
  match B.participationKind with
  | none => fun _ => none
  | some _ => fun
    | .data (.vote w) => (decodeVote n w).map fun v => B.voteRole v.slot
    | _ => none

/-- Install historical own-role permission only for the committee binding.
Restart keeps this stored permission through `acRestart`. -/
def VoteBinding.installVote (B : VoteBinding) {n : Nat}
    (p : ShapeRole B.Kind → Bool) (a : SA.SAState n) : SA.SAState n :=
  match B.participationKind with
  | none => a
  | some _ => { a with mayVote := fun s => p (B.voteRole s) }

/-- A committee vote candidate names exactly its historical signing role. -/
theorem VoteBinding.candidateRole_vote (B : VoteBinding)
    (h : B.participationKind ≠ none) {n : Nat} (d : ShapeDuty B.Kind) (v : Vote n) :
    B.candidateRole n d (.data (.vote (encodeVote v))) = some (B.voteRole v.slot) := by
  cases hp : B.participationKind with
  | none => exact False.elim (h hp)
  | some k => simp [VoteBinding.candidateRole, hp, decodeVote, encodeVote, v.val.isLt]

/-- Stock poll emissions keep the poll role after the optional override is resolved. -/
theorem stock_candidateRole_poll (n t : Nat) (m : Msg (Header Info) Body) :
    (stock.candidateRole n (.poll t) m).getD (.poll : ShapeRole stock.Kind) = .poll := by rfl

/-- Resolving the optional override on a poll gives the vote's role for every binding. -/
theorem VoteBinding.candidateRole_poll_vote (B : VoteBinding) {n : Nat} (t : Nat) (v : Vote n) :
    (B.candidateRole n (.poll t) (.data (.vote (encodeVote v)))).getD .poll =
      B.voteRole v.slot := by
  cases hp : B.participationKind with
  | none => simp [VoteBinding.candidateRole, VoteBinding.voteRole, hp]
  | some k =>
    simp [VoteBinding.candidateRole, VoteBinding.voteRole, hp, decodeVote, encodeVote, v.val.isLt]

/-- Non-vote poll bodies retain the poll role for every binding (F3′). -/
theorem VoteBinding.candidateRole_poll_nonvote (B : VoteBinding) (n t : Nat) (b : Body)
    (h : ∀ w, b ≠ .vote w) :
    (B.candidateRole n (.poll t) (.data b)).getD .poll = .poll := by
  cases b with
  | vote w => exact False.elim (h w rfl)
  | att a => cases hp : B.participationKind <;> simp [VoteBinding.candidateRole, hp]
  | relay => cases hp : B.participationKind <;> simp [VoteBinding.candidateRole, hp]
  | forward time => cases hp : B.participationKind <;> simp [VoteBinding.candidateRole, hp]
  | voteForward time w => cases hp : B.participationKind <;> simp [VoteBinding.candidateRole, hp]

/-- Committee initialization installs the supplied own-role permission. -/
theorem VoteBinding.installVote_mayVote (B : VoteBinding) (h : B.participationKind ≠ none)
    {n : Nat} (p : ShapeRole B.Kind → Bool) (a : SA.SAState n) (s : Slot) :
    (B.installVote p a).mayVote s = p (B.voteRole s) := by
  cases hp : B.participationKind with
  | none => exact False.elim (h hp)
  | some k => simp only [VoteBinding.installVote, hp]

/-- The single wire carrier, parameterised by the vote binding. -/
abbrev Wire (n : Nat) (binding : VoteBinding := stock) := ShapeObj n binding.Kind Info Body

/-- The exact dependency reference of a parent-bearing forwarding shape. This computable
projection needs no protocol parameters or digests and certifies no validity or provenance.
Raw blocks and genesis-wrapper shapes have no dependency reference. -/
def forwardParent? {binding : optParam VoteBinding stock} {n : Nat} :
    Wire n (binding := binding) → Option (Wire n (binding := binding))
  | .mk (.signed _ .poll) (.data (.forward _)) [parent, _] => some parent
  | _ => none

/-- The canonical object of a vote: signed by its validator in the binding's effective vote role,
carrying nothing. -/
def voteObj {binding : optParam VoteBinding stock} {n : Nat} (v : Vote n) :
    Wire n (binding := binding) :=
  .mk (.signed v.val (binding.voteRole v.slot)) (.data (.vote (encodeVote v))) []

/-- The canonical object of an attestation: signed by its validator in its effective role (`.poll`),
carrying nothing. -/
def attObj {binding : optParam VoteBinding stock} {n : Nat} (a : FG.Att n) :
    Wire n (binding := binding) :=
  .mk (.signed a.val .poll) (.data (.att (encodeAtt a))) []

/-- The objects a block carries: the canonical objects of its attestations, then of its votes
and support votes. -/
def payloadObjs {binding : optParam VoteBinding stock} {n : Nat}
    (atts : List (FG.Att n)) (p : Payload n) : List (Wire n (binding := binding)) :=
  atts.map (attObj (binding := binding)) ++ (p.1 ++ p.2).map (voteObj (binding := binding))

/-- A standalone attestation object: an attestation body signed in the `.poll` role, carrying
nothing (the shape of `attObj`, whether or not its body decodes). -/
def IsAttObj {binding : optParam VoteBinding stock} {n : Nat} : Wire n (binding := binding) → Prop
  | .mk (.signed _ .poll) (.data (.att _)) [] => True
  | _ => False

/-- **The FG attestation objects** (`Model.Protocol.isFGAtt`, delivered strictly before the FG
delay `ΔFG`): a standalone attestation (`IsAttObj`), and an unsigned relay wrapper whose carried
list is nonempty and consists of standalone attestations only. Every other object is delivered
strictly before `ΔAC`: blocks (with the attestations they carry), votes, `.forward` and
`.voteForward` wrappers, the empty relay wrapper, and a mixed relay wrapper (attestations relayed
together with a block or a vote).

Model choice (`docs/decisions.md` §"Network and delivery"): attestations bundled with a block or
a vote in one relay wrapper are delivered strictly before `ΔAC`, the bound of the bundle; so such
attestations reach the other nodes strictly before `ΔAC` instead of `ΔFG` (faster than a standalone
attestation whenever `ΔAC < ΔFG`). -/
def isFGAtt {binding : optParam VoteBinding stock} {n : Nat} : Wire n (binding := binding) → Prop
  | .mk .none (.data .relay) cs => cs ≠ [] ∧ ∀ c ∈ cs, IsAttObj (binding := binding) c
  | o => IsAttObj (binding := binding) o

/-- The slashing rule: two canonical attestation objects whose attestations are `slashable`
(E1/E2 of fg.tex). -/
def conflicts {binding : optParam VoteBinding stock} {n : Nat} :
    Wire n (binding := binding) → Wire n (binding := binding) → Bool
  | .mk (.signed k .poll) (.data (.att w)) [], .mk (.signed k' .poll) (.data (.att w')) [] =>
      match decodeAtt n w, decodeAtt n w' with
      | some a, some b => decide (k = a.val ∧ k' = b.val ∧ FG.slashable a b)
      | _, _ => false
  | _, _ => false

/-- Embed a raw digest among node roots, reserving `g` exclusively for genesis. -/
def taggedRoot (g h : Nat) : Nat := if h < g then h else h + 1

/-- Inverse of `taggedRoot` on non-genesis roots. -/
def rawRoot (g r : Nat) : Nat := if r < g then r else r - 1

/-- The header's parent reference: genesis is `.root`, other node roots decode
to raw engine digests. -/
def parentRef (g : Nat) : Option Nat → ParentRef
  | none => .root
  | some r => if r = g then .root else .digest (rawRoot g r)

/-- The block parent (by root) a header's parent reference names, with genesis root `g`. -/
def parentRoot (g : Nat) : ParentRef → Option Nat
  | .root => some g
  | .digest r => some (taggedRoot g r)

/-- The digest of header `h` among the digests `hs` the engine passed. -/
def rootOf (hs : List (Header Info × Nat)) (h : Header Info) : Option Nat :=
  (hs.find? fun q => q.1 == h).map (·.2)

/-! ## The shape -/

variable (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))

/-- The public parameters of `sp`: the type index of `goldilocksShape`. Only `n` (keys and
objects) and `ΔAC` (`skeleton`'s grid, overridden by `goldilocksShape`) are read from it; its FG
delay is set to `sp.Δ` only to fill the field and is read by no definition. The run's FG delay
is the family's `Public.ΔFG`. -/
abbrev _root_.Consensus.Goldilocks.SA.SAParams.pub : Public :=
  ⟨sp.n, sp.Δ, sp.toParams.hΔ, sp.Δ, sp.toParams.hΔ⟩

/-- A node block of the Goldilocks node. -/
abbrev Blk := NodeBlock sp.toParams (Payload sp.n)

/-- The header of a non-genesis block (its root is the digest of this header). -/
def headerOf (B : Blk sp) : Header Info :=
  ⟨parentRef sp.genesisRoot B.parent, B.slot, B.input, encodeInfo B.fgPayload B.acPayload⟩

/-- The block of a header `h` with digest `d`, signed by `k`, with the decoded payloads. -/
def blockOf (d : Nat) (h : Header Info) (k : Fin sp.n) (atts : List (FG.Att sp.n))
    (p : Payload sp.n) : Blk sp :=
  ⟨taggedRoot sp.genesisRoot d, parentRoot sp.genesisRoot h.parent, h.pos, k, h.input, atts, p⟩

/-- The skeleton uses protocol delay `Δ_p = pub.ΔAC`, selecting one proposer per `4Δ_p`, with
everyone in the poll role and no committee kinds; two poll steps (the release of the
bodies queued since the last tick), the node's tick as the poll proposal step, the slot proposal,
then two poll steps (the FG update and the release of the tick's bodies); one poll step at every
delivery (the release of the vote the delivery emitted, if any; the FG update is never due at a
delivery). -/
def skeleton (pub : Public) (binding : VoteBinding := stock) : Skeleton pub.n where
  grid := ⟨4 * pub.ΔAC, mul_pos (by decide) pub.ΔAC_pos⟩
  proposerSel := fun _ => .sized 1
  pollSel := .fixed Finset.univ
  Kind := binding.Kind
  decKind := binding.decKind
  kinds := []
  phase := fun _ => 0
  kindSel := binding.kindSel pub
  participationKind := binding.participationKind
  order := [.poll, .poll, .pollPropose, .propose, .poll, .poll]
  deliverOrder := [.poll]

/-- The shape's state: the own key, the node state `(Σ, 𝒜, Λ)`, the current time (set by the
clock), the bodies emitted or signed and not yet released, the admitted objects not yet relayed,
and whether the FG update of the current tick is due. -/
structure State (binding : VoteBinding := stock) where
  /-- The own validator index. -/
  self : Fin sp.n
  /-- The node state. -/
  node : NodeState (goldilocksNode sp ro)
  /-- The time of the last tick (or restart). -/
  now : Time
  /-- Bodies to sign and release, oldest first. -/
  outbox : List Body
  /-- Admitted objects to relay at the next gossip. -/
  relayBuf : List (Wire sp.n (binding := binding))
  /-- The FG update of this tick has not run yet. -/
  fgDue : Bool
  /-- Exact locally created wrappers, indexed by node root and retained across restarts. -/
  wrappers : Nat → Option (Wire sp.n (binding := binding)) := fun _ => none
  /-- Signed forwarding bodies awaiting the next selected poll, in acceptance order. -/
  forwards : List (Time × List (Wire sp.n (binding := binding))) := []
  /-- Fresh vote admissions awaiting signed poll publication, retained across restarts. -/
  voteForwards : List (Time × Vote sp.n) := []

variable {sp ro}

/-- The votes the cuts emit, as bodies to release. -/
def emitted (cs : List (Cut (goldilocksNode sp ro))) : List Body :=
  cs.flatMap fun
    | .ac ℓ => ℓ.emits.map fun e => .vote (encodeVote e.msg)
    | .fg _ => []

/-- Queue `o` for relay if `c`. -/
def relayIf {binding : optParam VoteBinding stock} (st : State sp ro (binding := binding))
    (c : Prop) [Decidable c] (o : Wire sp.n (binding := binding)) :
    State sp ro (binding := binding) :=
  if c then { st with relayBuf := st.relayBuf ++ [o] } else st

variable (sp) in
/-- The canonical object of a non-genesis block: its header as an item signed by its proposer in
its slot's proposer role, carrying its payload's objects. -/
def blockObj {binding : optParam VoteBinding stock} (B : Blk sp) : Wire sp.n (binding := binding) :=
  .mk (.signed B.proposer (.proposer B.slot)) (.item (headerOf sp B))
    (payloadObjs (binding := binding) B.fgPayload B.acPayload)

variable (sp) in
open Classical in
/-- The block a received object is the canonical object of, given the digests `hs` the engine
passed: a header signed in its slot's proposer role, whose indices decode, with a raw digest,
carrying its payload's objects, with well-formed attestations and a
valid AC payload. Such an object is `blockObj` of the block it decodes to. -/
noncomputable def decodeBlock {binding : optParam VoteBinding stock}
    (hs : List (Header Info × Nat)) :
    Wire sp.n (binding := binding) → Option (Blk sp)
  | .mk (.signed k (.proposer s)) (.item h) cs =>
      match decodeInfo sp.n h.info, rootOf hs h with
      | some (atts, p), some d =>
          let B := blockOf sp d h k atts p
          if h.pos = s ∧ cs = payloadObjs (binding := binding) atts p ∧
              (∀ a ∈ atts, a.WellFormed) ∧ SA.validPayload B then some B
          else none
      | _, _ => none
  | _ => none

variable (sp) in
/-- A signed forwarding wrapper. The optional exact parent wrapper precedes the canonical
child block, so recursive delivery processing replays the parent first. Construction alone
does not certify acceptance, freshness, or dependency readiness. -/
def forwardObj {binding : optParam VoteBinding stock} (origin : Fin sp.n) (acceptedAt : Time)
    (parent : Option (Wire sp.n (binding := binding)))
    (B : Blk sp) : Wire sp.n (binding := binding) :=
  .mk (.signed origin .poll) (.data (.forward acceptedAt))
    (parent.toList ++ [blockObj sp (binding := binding) B])

/-- Queue a wrapper only for an actual successful block cut. Parent lookup uses node roots;
the wire encoding stays in `blockObj`. A missing non-genesis parent leaves the queue unchanged:
the reachable-state invariant must rule out that case, rather than minting an orphan wrapper. -/
def queueAccepted {binding : optParam VoteBinding stock} (st : State sp ro (binding := binding))
    (B : Blk sp) : State sp ro (binding := binding) :=
  match B.parent with
  | none => st
  | some root =>
      let parent := if root = sp.genesisRoot then some none else (st.wrappers root).map some
      match parent with
      | none => st
      | some p =>
          { st with
            wrappers := Function.update st.wrappers B.root
              (some (forwardObj sp (binding := binding) st.self st.now p B))
            forwards := st.forwards ++
              [(st.now, p.toList ++ [blockObj sp (binding := binding) B])] }

/-- Record handler state and emissions, then queue successful acceptances and fresh vote
insertions. Candidate votes come from message/block calls and own emissions, not restart
replay. The pool difference preserves admission's duplicate and two-vote-cap checks. -/
def apply {binding : optParam VoteBinding stock} (st : State sp ro (binding := binding))
    (r : NodeState (goldilocksNode sp ro) × List (Cut (goldilocksNode sp ro))) :
    State sp ro (binding := binding) :=
  let publications := r.2.foldl (fun s c => match c with
    | .fg (.block B true) => queueAccepted s B
    | _ => s) st
  let candidates := r.2.flatMap fun
    | .fg _ => []
    | .ac ℓ =>
        (match ℓ.call with
          | .message v => [v]
          | .block B => SA.blockVotes B
          | _ => []) ++ ℓ.emits.map (·.msg)
  let admitted := candidates.dedup.filter fun v =>
    v ∉ st.node.ac.pool v.slot ∧ v ∈ r.1.ac.pool v.slot
  { st with
    node := r.1
    outbox := st.outbox ++ emitted r.2
    wrappers := publications.wrappers
    forwards := publications.forwards
    voteForwards := st.voteForwards ++ admitted.map (st.now, ·) }

variable (sp) in
/-- The vote a received object is the canonical object of (`voteObj`): signed by its validator
in the `.poll` role, carrying nothing. -/
def decodeVoteObj {binding : optParam VoteBinding stock} :
    Wire sp.n (binding := binding) → Option (Vote sp.n) :=
  match binding.participationKind with
  | none => fun
    | .mk (.signed k .poll) (.data (.vote w)) [] =>
        (decodeVote sp.n w).filter fun v => k = v.val
    | _ => none
  | some _ => fun
    | .mk (.signed k r) (.data (.vote w)) [] =>
        (decodeVote sp.n w).filter fun v => k = v.val ∧ r = binding.voteRole v.slot
    | _ => none

variable (sp) in
/-- The well-formed attestation a received object is the canonical object of (`attObj`): signed
by its validator in the `.poll` role, carrying nothing. -/
def decodeAttObj {binding : optParam VoteBinding stock} :
    Wire sp.n (binding := binding) → Option (FG.Att sp.n)
  | .mk (.signed k .poll) (.data (.att w)) [] =>
      (decodeAtt sp.n w).filter fun a => k = a.val ∧ a.WellFormed
  | _ => none

variable (sp ro) in
/-- The node's top-level event a received object stands for, given the digests `hs`: the block,
vote or attestation it is the canonical object of; none for anything else (dropped). -/
noncomputable def canonEvent {binding : optParam VoteBinding stock}
    (hs : List (Header Info × Nat)) (o : Wire sp.n (binding := binding)) :
    Option (Node.Event (goldilocksNode sp ro)) :=
  match decodeBlock sp (binding := binding) hs o, decodeVoteObj sp (binding := binding) o,
      decodeAttObj sp (binding := binding) o with
  | some B, _, _ => some (.block B)
  | none, some v, _ => some (.message v)
  | none, none, some a => some (.attestation a)
  | none, none, none => none

open Classical in
/-- Processing one received object through its canonical node handler. Blocks held after
the call and attestations use unsigned relay; fresh vote insertions use the signed queue in
`apply`. Noncanonical wrappers make no call; their carried objects are processed separately. -/
noncomputable def processOne {binding : optParam VoteBinding stock} (hs : List (Header Info × Nat))
    (st : State sp ro (binding := binding)) (o : Wire sp.n (binding := binding)) :
    State sp ro (binding := binding) :=
  match canonEvent sp ro (binding := binding) hs o with
  | some (.block B) =>
      let r := Node.onBlock st.self st.node st.now B
      relayIf (apply st r) (r.1.fg.blocks B.root = some B) o
  | some (.message v) =>
      let r := Node.onMessage st.self st.node st.now v
      apply st r
  | some (.attestation a) => relayIf (apply st (Node.onAttestation st.node a)) True o
  | _ => st

variable (sp) in
/-- The objects a delivery processes, in preorder: the received object, then recursively every
carried object. Noncanonical wrappers make no node call. A canonical block is processed before
its payload votes and attestations, which receive their own message/attestation calls even if
the block is refused. Thus admitting a payload vote is followed by actual message processing
at the same delivery time, rather than merely adding it to the AC pool. -/
def delivered {binding : optParam VoteBinding stock} (o : Wire sp.n (binding := binding)) :
    List (Wire sp.n (binding := binding)) := o.parts

/-- Processing a delivered object: its `delivered` objects one by one through `processOne`. -/
noncomputable def process {binding : optParam VoteBinding stock}
    (st : State sp ro (binding := binding))
    (o : Wire sp.n (binding := binding)) (hs : List (Header Info × Nat)) :
    State sp ro (binding := binding) :=
  (delivered sp (binding := binding) o).foldl (processOne hs) st

/-- Releasing a forwarding shape requires its exact parent wrapper to be held before
the envelope. Raw blocks have no release dependency. This policy does not restrict arrivals:
`process` traverses carried objects. Parsing and honest provenance, not this shape-only
release policy, establish same-origin acceptance and freshness. -/
def dependencies (n : Nat) {binding : optParam VoteBinding stock} :
    Model.DependencyPolicy (Wire n (binding := binding)) where
  ready held o := o.parts.all fun part =>
    match forwardParent? (binding := binding) part with
    | none => true
    | some parent => decide (parent ∈ held)
  mono := by
    intro held held' o hsub h
    simp only [List.all_eq_true] at h ⊢
    intro part hp
    specialize h part hp
    cases hi : forwardParent? (binding := binding) part with
    | none => simp
    | some parent =>
      simp only [hi, decide_eq_true_eq] at h ⊢
      exact hsub h

/-- Recording an own released object: the relay wrapper empties the relay queue; the own block
(now with its digest) goes through the own `on_block`, as `propose_block` does; a released vote
or attestation was admitted when emitted or signed. -/
noncomputable def recordOwn {binding : optParam VoteBinding stock}
    (st : State sp ro (binding := binding))
    (o : Wire sp.n (binding := binding)) (hs : List (Header Info × Nat)) :
    State sp ro (binding := binding) :=
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
noncomputable def nodeTick {binding : optParam VoteBinding stock}
    (st : State sp ro (binding := binding)) :
    State sp ro (binding := binding) :=
  if sp.toParams.IsPublic st.now then
    let r := Node.acCall st.self st.node st.now .tick
    { apply st (r.1, [r.2]) with fgDue := true }
  else st

/-- The slot proposal of the slot's proposer: `ac_proposal`; the header names the head and
carries the proposal's attestations (`proposal_attestations`) and the AC payload. The engine
writes the slot and the input and signs; the own `on_block` runs in `recordOwn`. -/
noncomputable def propose {binding : optParam VoteBinding stock}
    (st : State sp ro (binding := binding))
    (_s : Slot) : State sp ro (binding := binding) ×
      Option (ParentRef × Info × List (Wire sp.n (binding := binding))) :=
  let r := Node.acProposal st.node st.now
  let st' := { st with node := r.1 }
  match r.2.2 with
  | none => (st', none)
  | some (d, p) =>
      let atts := r.1.fg.proposalAttestations d.head
      (st', some (parentRef sp.genesisRoot (some d.head.root), encodeInfo atts p,
        payloadObjs (binding := binding) atts p))

/-- The FG update: `ac_to_fg`, then `attest(C)` at the source `C` it returns (`fg_attest`; when
it signs, the new record, the own `on_attestation` and the attestation queued), as
`Node.tickStep … .fgUpdate`. -/
noncomputable def fgUpdate {binding : optParam VoteBinding stock}
    (st : State sp ro (binding := binding)) :
    State sp ro (binding := binding) :=
  let r := Node.acToFG st.node st.now
  let st₁ := { st with node := r.1, fgDue := false }
  match r.2.2 with
  | none => st₁
  | some C =>
      match r.1.fg.attest r.1.record st.self C with
      | none => st₁
      | some (a, Λ') =>
          { st₁ with node := (Node.onAttestation { r.1 with record := Λ' } a).1,
                     outbox := st₁.outbox ++ [.att (encodeAtt a)] }

/-- A poll step: the FG update when due, then the oldest queued ordinary body.
Clear the forwarding queue; `pollBatch` captures its contents before this step. -/
noncomputable def poll {binding : optParam VoteBinding stock}
    (st : State sp ro (binding := binding))
    (_ : Time) : State sp ro (binding := binding) ×
      Option (Body × List (Wire sp.n (binding := binding))) :=
  let st₁ := if st.fgDue then fgUpdate st else st
  match st₁.outbox with
  | [] => ({ st₁ with forwards := [], voteForwards := [] }, none)
  | b :: rest => ({ st₁ with outbox := rest, forwards := [], voteForwards := [] }, some (b, []))

/-- Keep the ordinary emission and parent-first block wrappers at their original offsets,
then drain vote envelopes. Both queues are read before polling; the FG update admits no votes.
The engine signs the list and checks each candidate against its actual release prefix. -/
noncomputable def pollBatch {binding : optParam VoteBinding stock}
    (st : State sp ro (binding := binding))
    (t : Time) : State sp ro (binding := binding) ×
      List (Body × List (Wire sp.n (binding := binding))) :=
  let r := poll st t
  (r.1, r.2.toList ++ (st.forwards.map fun p => (.forward p.1, p.2)) ++
    (st.voteForwards.map fun p =>
      (.voteForward p.1 (encodeVote p.2), [voteObj (binding := binding) p.2])))

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

/-- A restart at time `t`: `𝒜` becomes `ac_restart(𝒜, Φ, t)` (only the locks and the latest
confirmation persist; its emissions are queued), the time is set, no FG update is due. `Σ`, `Λ`,
the queued bodies, the relay queue and the forwarding state are kept. -/
noncomputable def restore {binding : optParam VoteBinding stock} (k : Fin sp.n)
    (d : State sp ro (binding := binding)) (t : Time) : State sp ro (binding := binding) :=
  let r := Node.restart k d.node t
  { apply { d with self := k, now := t } r with fgDue := false }

variable (sp ro) in
/-- The Goldilocks node as a chain shape over already chosen protocol parameters.
Its grid uses `sp.Δ` directly: only `Setup.params` converts the engine delay to protocol delay. -/
noncomputable def goldilocksShape (binding : VoteBinding := stock) :
    ChainShape sp.pub Out Info where
  skel := { skeleton sp.pub (binding := binding) with
    grid := ⟨4 * sp.Δ, mul_pos (by decide) sp.toParams.hΔ⟩ }
  State := State sp ro (binding := binding)
  Body := Body
  Durable := State sp ro (binding := binding)
  decBody := inferInstance
  candidateRole := binding.candidateRole sp.n
  init k p := ⟨k, Node.initWith (goldilocksNode sp ro)
    (binding.installVote p (goldilocksNode sp ro).initial),
    0, [], [], false, fun _ => none, [], []⟩
  clock st t := { st with now := t }
  propose := propose
  act := fun st _ _ => (st, none)
  pollPropose st _ := (nodeTick st, none)
  poll := poll
  pollBatch := pollBatch
  gossip st _ :=
    match st.relayBuf with
    | [] => []
    | cs => [(.data .relay, cs)]
  process := process
  dependencies := dependencies sp.n (binding := binding)
  recordOwn := recordOwn
  durable := id
  restore := restore
  out g st := outOf st.node st.now g
  conflicts := conflicts (binding := binding)
  isFGAtt := isFGAtt (binding := binding)

/-! ## The family -/

/-- The parameters of the Goldilocks node not fixed by the public parameters:
the genesis root, the FG timeout `δ_t`, the lock window `k`, the fast increment `c`, and
the restart replay order at every parameter set. -/
structure Setup where
  /-- The genesis root. -/
  genesisRoot : Nat
  /-- The FG timeout parameter `δ_t`. -/
  δt : Nat
  /-- The lock window `k ≥ 2`. -/
  k : Nat
  two_le_k : 2 ≤ k
  /-- The fast increment `c ≥ 2` (`SAParams.c`). -/
  c : Nat
  two_le_c : 2 ≤ c
  /-- The restart replay order depends on the validator count and fixed genesis root,
  not on a proposer schedule or timing parameters. -/
  ro : (n : Nat) → SA.ReplayOrderData n genesisRoot (List (FG.Att n))

/-- A vote binding for the generic instance, without enlarging the stock setup's quantifier. -/
structure BoundSetup extends Setup where
  /-- Historical vote authentication, permission and threshold denominator. -/
  vote : VoteBinding

/-- The SA parameters use protocol delay `pub.ΔAC` and slots of four protocol delays: L0 delivers
strictly before the bound (`CommLog.PSync`), which is the node's deadline `[τ, max(τ, w) + Δ)`.
The run's proposer selection is independent of these runtime parameters. -/
abbrev Setup.params (S : Setup) (pub : Public) (hn : 1 ≤ pub.n)
    (binding : VoteBinding := stock) : SAParams where
  toParams :=
    { n := pub.n
      hn := hn
      Δ := pub.ΔAC
      hΔ := pub.ΔAC_pos
      slotTime := fun s => 4 * pub.ΔAC * s
      slotTime_zero := by simp
      slotTime_strictMono := fun a b h =>
        mul_lt_mul_of_pos_left (by exact_mod_cast h) (by have := pub.ΔAC_pos; linarith)
      slotTime_public := fun s => ⟨4 * s, by ring⟩
      genesisRoot := S.genesisRoot
      δt := S.δt }
  slotTime_eq := fun _ => rfl
  k := S.k
  two_le_k := S.two_le_k
  c := S.c
  two_le_c := S.two_le_c
  committeeSize := binding.committeeSize pub

/-- The shape's state at the public parameters `pub`: a Goldilocks state at every proof that
`pub` has a validator. The dependence on `1 ≤ n` (which `Params` needs) is thus in the state's
*values*, never in the family's types: `(goldilocks S pub).State` is this function type, `.Body`
is `Body`, `.skel.Kind` is `binding.Kind`, and a run's state at `hn` is `st hn : State …` without a
cast. Without a validator there are no keys, no duties with an effect and no outputs. -/
def PubState (S : Setup) (pub : Public) (binding : VoteBinding := stock) : Type :=
  (hn : 1 ≤ pub.n) → State (S.params pub hn (binding := binding)) (S.ro _) (binding := binding)

/-- The Goldilocks family: `goldilocksShape` at `S.params pub hn` for every `hn`, through
`PubState`; the steps that output something (a proposal, a poll body, the gossip, the
output chains) output it at some proof of `1 ≤ n` and nothing without one. -/
noncomputable def goldilocksWith (S : BoundSetup) :
    ChainShapeFamily schema Info := fun pub =>
  let binding := S.vote
  let G := fun hn : 1 ≤ pub.n =>
    goldilocksShape (S.toSetup.params pub hn (binding := binding)) (S.ro _) (binding := binding)
  { skel := skeleton pub (binding := binding)
    State := PubState S.toSetup pub (binding := binding)
    Body := Body
    Durable := PubState S.toSetup pub (binding := binding)
    decBody := inferInstance
    candidateRole := binding.candidateRole pub.n
    init := fun k p hn => (G hn).init k p
    clock := fun st t hn => (G hn).clock (st hn) t
    propose := fun st s =>
      if hn : 1 ≤ pub.n then (fun _ => ((G hn).propose (st hn) s).1, ((G hn).propose (st hn) s).2)
      else (st, none)
    act := fun st _ _ => (st, none)
    pollPropose := fun st t =>
      if hn : 1 ≤ pub.n then
        (fun _ => ((G hn).pollPropose (st hn) t).1, ((G hn).pollPropose (st hn) t).2)
      else (st, none)
    poll := fun st t =>
      if hn : 1 ≤ pub.n then (fun _ => ((G hn).poll (st hn) t).1, ((G hn).poll (st hn) t).2)
      else (st, none)
    pollBatch := fun st t =>
      if hn : 1 ≤ pub.n then
        (fun _ => ((G hn).pollBatch (st hn) t).1, ((G hn).pollBatch (st hn) t).2)
      else (st, [])
    gossip := fun st t => if hn : 1 ≤ pub.n then (G hn).gossip (st hn) t else []
    process := fun st o hs hn => (G hn).process (st hn) o hs
    dependencies := dependencies pub.n (binding := binding)
    recordOwn := fun st o hs hn => (G hn).recordOwn (st hn) o hs
    durable := id
    restore := fun k d t hn => (G hn).restore k (d hn) t
    out := fun g st => if hn : 1 ≤ pub.n then (G hn).out g (st hn) else []
    conflicts := conflicts (binding := binding)
    isFGAtt := isFGAtt (binding := binding) }

/-- The population-wide instance is the stock vote binding.

The `@[reducible]` is an interim build scaffold, removed at D2 together with the stock
`Coe Setup BoundSetup` instance: it lets stock callers unify `goldilocks S` with the
binding-generic layer's `goldilocksWith ⟨S, stock⟩`. -/
@[reducible] noncomputable def goldilocks (S : Setup) : ChainShapeFamily schema Info :=
  goldilocksWith ⟨S, stock⟩

/-- The family installs the actual own-role predicate in the committee node's initial AC state. -/
theorem goldilocksWith_init_mayVote (S : BoundSetup) (pub : Public) (hn : 1 ≤ pub.n)
    (h : S.vote.participationKind ≠ none) (key : Fin pub.n)
    (p : ShapeRole S.vote.Kind → Bool) (s : Slot) :
    (((goldilocksWith S pub).init key p hn).node.ac).mayVote s = p (S.vote.voteRole s) := by
  exact S.vote.installVote_mayVote h p _ s

end Consensus.Goldilocks.AsChainShape

end
