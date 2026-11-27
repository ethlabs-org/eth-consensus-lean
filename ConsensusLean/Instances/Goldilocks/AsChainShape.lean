module
public import ConsensusLean.Instances.Goldilocks.NodeAsChainShape
public import ConsensusLean.Instances.Goldilocks.Spec.Run.Goldilocks
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # The Goldilocks node as a chain shape (definitions)

The Goldilocks protocol of `Spec/Run/Goldilocks` (the node of `Spec/Node` over `goldilocksAC`),
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
  canonical objects of its attestations (`payloadObjs`), so a node can later carry them on in its
  own blocks (the engine releases only carried objects it has seen). Its declared head votes are
  header data, not carried objects: a block carries no vote. A received object is processed
  only in a canonical form (`blockObj`, `voteObj`, `attObj`; read back by `decodeBlock`,
  `decodeVoteObj`, `decodeAttObj`, together `canonEvent`), anything else is dropped. A delivery
  processes the received object and, recursively, what it carries (`delivered`), except what a
  block-shaped object carries when it fails the wire checks, when the node drops it as of a future
  slot, or when the FG refuses it (`Refuses`; composition.tex §"Blocks").
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
  attestation, or holds it when the setup's release schedule refuses release at the tick's time
  (`held`); the two trailing polls drain the tick's at most one vote and one attestation. The
  record changes at the signing. When the schedule allows release at the signing time, the own
  `on_attestation` runs at once and the attestation joins the outbox queue (released by a poll
  of that time, after any body ahead of it); otherwise it is held: not in the node's pool, so no
  proposal carries it. The first poll after the tick step of its time (`ticked`) at which the
  schedule allows release processes every held attestation, oldest first, before that poll's FG
  update, and releases them at the end of its batch, after the batch's other candidates. The
  pool is in admission order, which can differ from signing order and from release order. Votes
  never wait for held attestations.
* **Relay.** A newly accepted block or an attestation is relayed at the gossip of its event as
  a carried object of an unsigned `.relay` wrapper; a delivery's emission and relay leave at the
  delivery's own time (`Model.Run.deliver`), as the spec's relay rule sends them.
  Fresh vote insertions instead queue `.voteForward` envelopes, signed by the admitting node
  and stamped with its admission time. The envelope carries the canonical vote, which recursive
  delivery visits again. Restart replay does not create vote envelopes.
  Separately, successful block acceptance cuts queue fresh signed `.forward` wrappers, including
  own proposals. The durable node-root map supplies exact same-origin parent wrappers. A selected
  `pollBatch` emits its ordinary body, block wrappers in acceptance order, then vote envelopes;
  `releaseAll` checks each against actual prefix holdings. Duplicate/refused calls neither mint
  wrappers nor relay the block. Unsigned compatibility relay is retained, but certifies no
  acceptance timestamp.
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
open AC (ACParams ReplayOrder goldilocksAC Vote Payload)

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

/-- A vote on the wire: `AC.Vote` with the validator index as a number. -/
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
  /-- A head vote (an AC message) with its authentication evidence `z`, signed together. -/
  | vote (v : WireVote) (z : Nat)
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
    | .data (.vote w _) => (decodeVote n w).map fun v => B.voteRole v.slot
    | _ => none

/-- Install historical own-role permission only for the committee binding.
Restart keeps this stored permission through `acRestart`. -/
def VoteBinding.installVote (B : VoteBinding) {n : Nat}
    (p : ShapeRole B.Kind → Bool) (a : AC.ACState n) : AC.ACState n :=
  match B.participationKind with
  | none => a
  | some _ => { a with mayVote := fun s => p (B.voteRole s) }

/-- Installing the own-role vote permission changes no field of the state other than `mayVote`. -/
theorem VoteBinding.installVote_eq_mayVote (B : VoteBinding) {n : Nat}
    (p : ShapeRole B.Kind → Bool) (a : AC.ACState n) :
    B.installVote p a = { a with mayVote := (B.installVote p a).mayVote } := by
  unfold VoteBinding.installVote
  cases B.participationKind <;> rfl

/-- Resolving the optional override on a poll gives the vote's role for every binding. -/
theorem VoteBinding.candidateRole_poll_vote (B : VoteBinding) {n : Nat} (t : Nat) (v : Vote n)
    (z : Nat) :
    (B.candidateRole n (.poll t) (.data (.vote (encodeVote v) z))).getD .poll =
      B.voteRole v.slot := by
  cases hp : B.participationKind with
  | none => simp [VoteBinding.candidateRole, VoteBinding.voteRole, hp]
  | some k =>
    simp [VoteBinding.candidateRole, VoteBinding.voteRole, hp, decodeVote, encodeVote, v.val.isLt]

/-- Non-vote poll bodies retain the poll role for every binding. -/
theorem VoteBinding.candidateRole_poll_nonvote (B : VoteBinding) (n t : Nat) (b : Body)
    (h : ∀ w z, b ≠ .vote w z) :
    (B.candidateRole n (.poll t) (.data b)).getD .poll = .poll := by
  cases b with
  | vote w z => exact False.elim (h w z rfl)
  | att a => cases hp : B.participationKind <;> simp [VoteBinding.candidateRole, hp]
  | relay => cases hp : B.participationKind <;> simp [VoteBinding.candidateRole, hp]
  | forward time => cases hp : B.participationKind <;> simp [VoteBinding.candidateRole, hp]
  | voteForward time w => cases hp : B.participationKind <;> simp [VoteBinding.candidateRole, hp]

/-- Committee initialization installs the supplied own-role permission. -/
theorem VoteBinding.installVote_mayVote (B : VoteBinding) (h : B.participationKind ≠ none)
    {n : Nat} (p : ShapeRole B.Kind → Bool) (a : AC.ACState n) (s : Slot) :
    (B.installVote p a).mayVote s = p (B.voteRole s) := by
  cases hp : B.participationKind with
  | none => exact False.elim (h hp)
  | some k => simp only [VoteBinding.installVote, hp]

/-- The single wire carrier, parameterised by the vote binding. -/
abbrev Wire (n : Nat) (binding : VoteBinding := stock) := ShapeObj n binding.Kind Info Body

variable (sp : ACParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
  {binding : optParam VoteBinding stock}

/-- The exact dependency reference of a parent-bearing forwarding shape. This computable
projection needs no protocol parameters or digests and certifies no validity or provenance.
Raw blocks and genesis-wrapper shapes have no dependency reference. -/
def forwardParent? {n : Nat} :
    Wire n (binding := binding) → Option (Wire n (binding := binding))
  | .mk (.signed _ .poll) (.data (.forward _)) [parent, _] => some parent
  | _ => none

/-- The canonical object of a vote with evidence `z`: signed by its validator in the binding's
effective vote role, carrying nothing. -/
def voteObj {n : Nat} (v : Vote n) (z : Nat) :
    Wire n (binding := binding) :=
  .mk (.signed v.val (binding.voteRole v.slot)) (.data (.vote (encodeVote v) z)) []

/-- The vote data a vote body claims: its decoded signer, in the binding's vote role of its
slot. -/
def voteClaim (n : Nat) (w : WireVote) : Option (Fin n × ShapeRole binding.Kind) :=
  (decodeVote n w).map fun v => (v.val, binding.voteRole v.slot)

/-- The delegated vote bodies: the standalone head vote, and nothing else. -/
def voteBody : Body → Bool
  | .vote _ _ => true
  | _ => false

/-- **The presented signed vote** of a received object: a head-vote body signed by its decoded
validator in the binding's vote role of its slot, carrying nothing, with its claimed signer, role,
vote data and evidence. A parser, not a membership test; `none` for anything else. -/
def presented {n : Nat} :
    Wire n (binding := binding) →
      Option ((Fin n × ShapeRole binding.Kind × WireVote) × Nat)
  | .mk (.signed k r) (.data (.vote w z)) [] =>
      match decodeVote n w with
      | some v => if k = v.val ∧ r = binding.voteRole v.slot then some ((k, r, w), z) else none
      | none => none
  | _ => none

/-- The vote authentication a Goldilocks node holds. -/
abbrev VoteAuth (n : Nat) (binding : VoteBinding := stock) :=
  Model.VoteIO Nat (ShapeRole binding.Kind) WireVote n

/-- The canonical object of an attestation: signed by its validator in its effective role (`.poll`),
carrying nothing. -/
def attObj {n : Nat} (a : FG.Att n) :
    Wire n (binding := binding) :=
  .mk (.signed a.val .poll) (.data (.att (encodeAtt a))) []

/-- The objects a block carries: the canonical objects of its attestations. Its AC payload, the
declared head votes and their support list, carries no vote object. -/
def payloadObjs {n : Nat}
    (atts : List (FG.Att n)) (_p : Payload n) : List (Wire n (binding := binding)) :=
  atts.map (attObj (binding := binding))

/-- A standalone attestation object: an attestation body signed in the `.poll` role, carrying
nothing (the shape of `attObj`, whether or not its body decodes). -/
def IsAttObj {n : Nat} : Wire n (binding := binding) → Prop
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
def isFGAtt {n : Nat} : Wire n (binding := binding) → Prop
  | .mk .none (.data .relay) cs => cs ≠ [] ∧ ∀ c ∈ cs, IsAttObj (binding := binding) c
  | o => IsAttObj (binding := binding) o

/-- The slashing rule: two canonical attestation objects whose attestations are `slashable`
(E1/E2 of fg.tex). -/
def conflicts {n : Nat} :
    Wire n (binding := binding) → Wire n (binding := binding) → Bool
  | .mk (.signed k .poll) (.data (.att w)) [], .mk (.signed k' .poll) (.data (.att w')) [] =>
      match decodeAtt n w, decodeAtt n w' with
      | some a, some b => decide (k = a.val ∧ k' = b.val ∧ FG.slashable a b)
      | _, _ => false
  | _, _ => false

/-- Embed a raw digest among node roots, reserving `g` exclusively for genesis. -/
def taggedRoot (g h : Nat) : Nat := NodeAsChainShape.taggedRoot g h

/-- Inverse of `taggedRoot` on non-genesis roots. -/
def rawRoot (g r : Nat) : Nat := NodeAsChainShape.rawRoot g r

/-- The header's parent reference: genesis is `.root`, other node roots decode
to raw engine digests. -/
def parentRef (g : Nat) : Option Nat → ParentRef := NodeAsChainShape.parentRef g

/-- The block parent (by root) a header's parent reference names, with genesis root `g`. -/
def parentRoot (g : Nat) : ParentRef → Option Nat := NodeAsChainShape.parentRoot g

/-- The digest of header `h` among the digests `hs` the engine passed. -/
def rootOf (hs : List (Header Info × Nat)) (h : Header Info) : Option Nat :=
  NodeAsChainShape.rootOf hs h

/-! ## The shape -/

/-- The public parameters of `sp`: the type index of `goldilocksShape`. Only `n` (keys and
objects) and `ΔAC` (`skeleton`'s grid, overridden by `goldilocksShape`) are read from it; its FG
delay is set to `sp.Δ` only to fill the field and is read by no definition. The run's FG delay
is the family's `Public.ΔFG`. -/
abbrev _root_.Consensus.Goldilocks.AC.ACParams.pub : Public :=
  ⟨sp.n, sp.Δ, sp.toParams.hΔ, sp.Δ, sp.toParams.hΔ⟩

/-- A node block of the Goldilocks node. -/
abbrev Blk := NodeBlock sp.toParams (Payload sp.n)

/-- The header of a non-genesis block (its root is the digest of this header). -/
def headerOf (B : Blk sp) : Header Info :=
  NodeAsChainShape.headerOf (P := sp.toParams) encodeInfo B

/-- The block of a header `h` with digest `d`, signed by `k`, with the decoded payloads. -/
def blockOf (d : Nat) (h : Header Info) (k : Fin sp.n) (atts : List (FG.Att sp.n))
    (p : Payload sp.n) : Blk sp :=
  NodeAsChainShape.blockOf (P := sp.toParams) d h k atts p

/-- The skeleton uses protocol delay `Δ_p = pub.ΔAC`, selecting one proposer per `4Δ_p`, with
everyone in the poll role and no scheduled committee duties (`kinds` is empty; the binding supplies
its historical vote kind, that kind's selection and the participation kind); two poll steps (the
release of the bodies queued since the last tick), the node's tick as the poll proposal step, the
slot proposal, then two poll steps (the FG update and the release of the tick's bodies); one poll
step at every delivery (the release of the vote the delivery emitted, if any; the FG update is
never due at a delivery). -/
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
  /-- Fresh vote admissions awaiting signed poll publication, retained across restarts: the
  admission time, the vote and its exact signed object (as received, or the own one). -/
  voteForwards : List (Time × Vote sp.n × Wire sp.n (binding := binding)) := []
  /-- The node's vote authentication, installed at `init`, retained across restarts. -/
  voteIO : VoteAuth sp.n binding := ⟨fun _ _ _ _ => false, fun _ _ => none⟩
  /-- Own signed attestations not yet released, oldest first: the release schedule refused
  release at their signing time and at every poll since. Retained across restarts. -/
  held : List (FG.Att sp.n) := []
  /-- The tick step of the current time has run (set by the poll proposal step, cleared by the
  clock): held attestations are released and processed only after it. -/
  ticked : Bool := false

variable {sp ro}

/-- The own evidence for an own vote: the node's issuer in the vote's role. -/
def ownToken (io : VoteAuth sp.n binding) (v : Vote sp.n) : Option Nat :=
  io.own (binding.voteRole v.slot) (encodeVote v)

/-- The votes the cuts emit, as bodies to release, each with its own evidence; a vote without
evidence is not released. -/
def emitted (io : VoteAuth sp.n binding) (cs : List (Cut (goldilocksNode sp ro))) : List Body :=
  cs.flatMap fun
    | .ac ℓ => ℓ.emits.filterMap fun e =>
        (ownToken (binding := binding) io e.msg).map fun z => .vote (encodeVote e.msg) z
    | .fg _ => []

/-- Queue `o` for relay if `c`. -/
def relayIf (st : State sp ro (binding := binding))
    (c : Prop) [Decidable c] (o : Wire sp.n (binding := binding)) :
    State sp ro (binding := binding) :=
  if c then { st with relayBuf := st.relayBuf ++ [o] } else st

variable (sp) in
/-- The canonical object of a non-genesis block: its header as an item signed by its proposer in
its slot's proposer role, carrying its payload's objects. -/
def blockObj (B : Blk sp) : Wire sp.n (binding := binding) :=
  NodeAsChainShape.blockObj (P := sp.toParams) encodeInfo (payloadObjs (binding := binding)) B

variable (sp) in
open Classical in
/-- The block a received object is the canonical object of, given the digests `hs` the engine
passed: a header signed in its slot's proposer role, whose indices decode, with a raw digest,
carrying its payload's objects, with well-formed attestations and a
valid AC payload. Such an object is `blockObj` of the block it decodes to. -/
noncomputable def decodeBlock
    (hs : List (Header Info × Nat)) :
    Wire sp.n (binding := binding) → Option (Blk sp) :=
  NodeAsChainShape.decodeBlock (P := sp.toParams) (decodeInfo sp.n)
    (payloadObjs (binding := binding)) AC.validPayload hs

variable (sp) in
/-- A signed forwarding wrapper. The optional exact parent wrapper precedes the canonical
child block, so recursive delivery processing replays the parent first. Construction alone
does not certify acceptance, freshness, or dependency readiness. -/
def forwardObj (origin : Fin sp.n) (acceptedAt : Time)
    (parent : Option (Wire sp.n (binding := binding)))
    (B : Blk sp) : Wire sp.n (binding := binding) :=
  .mk (.signed origin .poll) (.data (.forward acceptedAt))
    (parent.toList ++ [blockObj sp (binding := binding) B])

/-- Queue a wrapper only for an actual successful block cut. Parent lookup uses node roots;
the wire encoding stays in `blockObj`. A missing non-genesis parent leaves the queue unchanged:
the reachable-state invariant must rule out that case, rather than minting an orphan wrapper. -/
def queueAccepted (st : State sp ro (binding := binding))
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
insertions. Candidate votes come from message calls and own emissions (a block call admits no
vote, and neither does restart replay). The pool difference preserves admission's duplicate and
two-vote-cap checks. A fresh received vote is queued with the exact object it arrived in
(`origin`); a fresh own vote with its own signed object and the same evidence as its release. -/
def apply (st : State sp ro (binding := binding))
    (origin : Option (Wire sp.n (binding := binding)))
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
          | _ => []) ++ ℓ.emits.map (·.msg)
  let own := r.2.flatMap fun
    | .fg _ => []
    | .ac ℓ => ℓ.emits.map (·.msg)
  let objOf : Vote sp.n → Option (Wire sp.n (binding := binding)) := fun v =>
    if v ∈ own then (ownToken (binding := binding) st.voteIO v).map (voteObj (binding := binding) v)
    else origin
  let admitted := candidates.dedup.filter fun v =>
    v ∉ st.node.ac.pool v.slot ∧ v ∈ r.1.ac.pool v.slot
  { st with
    node := r.1
    outbox := st.outbox ++ emitted (binding := binding) st.voteIO r.2
    wrappers := publications.wrappers
    forwards := publications.forwards
    voteForwards := st.voteForwards ++ admitted.filterMap fun v => (objOf v).map (st.now, v, ·) }

variable (sp) in
/-- The vote a received object is the canonical object of (`voteObj`), when the node's verifier
accepts its evidence: the presented signed vote (`presented`), checked by `io.check`. A vote that
fails the check makes no message call. -/
def decodeVoteObj (io : VoteAuth sp.n binding) (o : Wire sp.n (binding := binding)) :
    Option (Vote sp.n) :=
  match presented (binding := binding) o with
  | some ((k, r, w), z) => if io.check k r w z = true then decodeVote sp.n w else none
  | none => none

variable (sp) in
/-- The well-formed attestation a received object is the canonical object of (`attObj`): signed
by its validator in the `.poll` role, carrying nothing. -/
def decodeAttObj :
    Wire sp.n (binding := binding) → Option (FG.Att sp.n)
  | .mk (.signed k .poll) (.data (.att w)) [] =>
      (decodeAtt sp.n w).filter fun a => k = a.val ∧ a.WellFormed
  | _ => none

/-- The Goldilocks header payload and carried objects, with vote and attestation decoding. -/
def wireCodec (sp : ACParams) (ro : ReplayOrder sp (List (FG.Att sp.n))) (binding : VoteBinding)
    (io : VoteAuth sp.n binding) :
    NodeAsChainShape.WireCodec (goldilocksNode sp ro) binding.Kind Info Body where
  encode := encodeInfo
  decode := decodeInfo sp.n
  carried := payloadObjs (binding := binding)
  message := decodeVoteObj sp (binding := binding) io
  attestation := decodeAttObj sp (binding := binding)

/-- Connect node handlers to the Goldilocks clock, duty flag and publication queues. -/
noncomputable def nodeAdapter (sp : ACParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (binding : VoteBinding)
    (sign : Fin sp.n → Time → Bool := fun _ _ => true)
    (release : Fin sp.n → Time → Bool := fun _ _ => true) :
    NodeAsChainShape.Adapter (goldilocksNode sp ro) binding.Kind Info Body
      (State sp ro binding) where
  self := State.self
  node := State.node
  now := State.now
  setNode st node := { st with node }
  setDue st fgDue := { st with fgDue }
  wake st self now := { st with self, now }
  applyCuts := apply
  relayIf := relayIf
  attest st node a :=
    if release st.self st.now then
      { st with node := (Node.onAttestation node a).1, outbox := st.outbox ++ [.att (encodeAtt a)] }
    else { st with node, held := st.held ++ [a] }
  sign := sign

variable (sp ro) in
/-- The node's top-level event a received object stands for, given the digests `hs`: the block,
vote or attestation it is the canonical object of; none for anything else (dropped). -/
noncomputable def canonEvent
    (io : VoteAuth sp.n binding)
    (hs : List (Header Info × Nat)) (o : Wire sp.n (binding := binding)) :
    Option (Node.Event (goldilocksNode sp ro)) :=
  NodeAsChainShape.canonEvent (wireCodec sp ro binding io) hs o

open Classical in
/-- Processing one received object through its canonical node handler. A block the call newly
accepts (not held before the call, held after it) and attestations use unsigned relay; a refused
receipt, including a block already held, is not relayed (composition.tex §"Model"); fresh vote
insertions use the signed queue in `apply`. Noncanonical wrappers make no call; their carried
objects are processed separately. -/
noncomputable def processOne (io : VoteAuth sp.n binding) (hs : List (Header Info × Nat))
    (st : State sp ro (binding := binding)) (o : Wire sp.n (binding := binding)) :
    State sp ro (binding := binding) :=
  NodeAsChainShape.processOne (wireCodec sp ro binding io) (nodeAdapter sp ro binding) hs st o

/-- A block-shaped object: one that says a header item, as a block's canonical object does
(`blockObj`). Every other object is a vote, an attestation or a wrapper body. -/
def BlockShaped : Wire sp.n (binding := binding) → Prop := NodeAsChainShape.BlockShaped

/-- Processing `o` at `st` refuses a block: `o` is block-shaped and either fails the wire checks
(it is no canonical block: `decodeBlock` rejects its signature role, slot, indices, carried
objects, attestations or AC payload), or is a canonical block that `on_block` drops as of a
future slot or that the FG refuses (composition.tex §"Blocks"). -/
def Refuses (io : VoteAuth sp.n binding) (hs : List (Header Info × Nat))
    (st : State sp ro (binding := binding)) (o : Wire sp.n (binding := binding)) : Prop :=
  NodeAsChainShape.Refuses (wireCodec sp ro binding io) (nodeAdapter sp ro binding) hs st o

/-- The objects a delivery of `o` at `st` processes, in preorder, with the state after them: `o`,
then, unless processing `o` refuses a block (`Refuses`), recursively every object it carries, each
from the state its predecessors leave. No handler runs for what a refused block carries, nor for
what a block-shaped object that fails the wire checks carries (composition.tex §"Blocks": the
check drops it with no effect); a later delivery can carry those objects again. Wrappers make no
node call, and their carried objects are processed. A canonical block is
processed before its payload votes and attestations, which receive their own message/attestation
calls when the block is accepted. Thus admitting a payload vote is followed by actual message
processing at the same delivery time, rather than merely adding it to the AC pool. -/
noncomputable def visit (io : VoteAuth sp.n binding) (hs : List (Header Info × Nat)) :
    State sp ro (binding := binding) → Wire sp.n (binding := binding) →
      List (Wire sp.n (binding := binding)) × State sp ro (binding := binding) :=
  NodeAsChainShape.visit (wireCodec sp ro binding io) (nodeAdapter sp ro binding) hs

/-- `visit` of a list of carried objects, one after the other. -/
noncomputable def visitList (io : VoteAuth sp.n binding) (hs : List (Header Info × Nat)) :
    State sp ro (binding := binding) → List (Wire sp.n (binding := binding)) →
      List (Wire sp.n (binding := binding)) × State sp ro (binding := binding) :=
  NodeAsChainShape.visitList (wireCodec sp ro binding io) (nodeAdapter sp ro binding) hs

/-- The objects a delivery of `o` at `st` processes (`visit`). -/
noncomputable def delivered (io : VoteAuth sp.n binding) (hs : List (Header Info × Nat))
    (st : State sp ro (binding := binding)) (o : Wire sp.n (binding := binding)) :
    List (Wire sp.n (binding := binding)) :=
  NodeAsChainShape.delivered (wireCodec sp ro binding io) (nodeAdapter sp ro binding) hs st o

/-- Processing a delivered object: its `delivered` objects one by one through `processOne`. -/
noncomputable def process
    (st : State sp ro (binding := binding))
    (o : Wire sp.n (binding := binding)) (hs : List (Header Info × Nat)) :
    State sp ro (binding := binding) :=
  NodeAsChainShape.process (wireCodec sp ro binding st.voteIO) (nodeAdapter sp ro binding) st o hs

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
noncomputable def recordOwn
    (st : State sp ro (binding := binding))
    (o : Wire sp.n (binding := binding)) (hs : List (Header Info × Nat)) :
    State sp ro (binding := binding) :=
  match o with
  | .mk .none (.data .relay) _ => { st with relayBuf := [] }
  | .mk (.signed k (.proposer _)) (.item h) _ =>
      NodeAsChainShape.recordBlock (wireCodec sp ro binding st.voteIO) (nodeAdapter sp ro binding)
        st k h hs
  | _ => st

/-- The public tick queues `ac_on_tick` votes and sets the FG duty from the signing calendar. -/
noncomputable def nodeTick
    (st : State sp ro (binding := binding)) (sign : Fin sp.n → Time → Bool := fun _ _ => true) :
    State sp ro (binding := binding) :=
  NodeAsChainShape.nodeTick (nodeAdapter sp ro binding sign) st

/-- The slot proposal of the slot's proposer: `ac_proposal`; the header names the head and
carries the proposal's attestations (`proposal_attestations`) and the AC payload. The engine
writes the slot and the input and signs; the own `on_block` runs in `recordOwn`. -/
noncomputable def propose
    (st : State sp ro (binding := binding))
    (_s : Slot) : State sp ro (binding := binding) ×
      Option (ParentRef × Info × List (Wire sp.n (binding := binding))) :=
  NodeAsChainShape.propose (wireCodec sp ro binding st.voteIO) (nodeAdapter sp ro binding) st _s

/-- The FG update: `ac_to_fg`, then `attest(C)` at the source `C` it returns (`fg_attest`; when
it signs, the new record, the own `on_attestation` and the attestation queued), as
`Node.tickStep … .fgUpdate`. -/
noncomputable def fgUpdate
    (st : State sp ro (binding := binding))
    (release : Fin sp.n → Time → Bool := fun _ _ => true) :
    State sp ro (binding := binding) :=
  NodeAsChainShape.fgUpdate (nodeAdapter sp ro binding (release := release)) st

/-- A poll step: the FG update when due (its attestation queued or held by `release`), then the
oldest queued ordinary body.
Clear the forwarding queue; `pollBatch` captures its contents before this step. -/
noncomputable def poll
    (st : State sp ro (binding := binding))
    (_ : Time) (release : Fin sp.n → Time → Bool := fun _ _ => true) :
    State sp ro (binding := binding) ×
      Option (Body × List (Wire sp.n (binding := binding))) :=
  let st₁ := if st.fgDue then fgUpdate st release else st
  match st₁.outbox with
  | [] => ({ st₁ with forwards := [], voteForwards := [] }, none)
  | b :: rest => ({ st₁ with outbox := rest, forwards := [], voteForwards := [] }, some (b, []))

/-- Keep the ordinary emission and parent-first block wrappers at their original offsets,
then drain vote envelopes, then, after the tick step of the node's time and when the release
schedule allows it then, every held attestation, oldest first; these are processed by the
own `on_attestation`, in that order, before the poll's FG update. The queues are read before
polling; the FG update admits no votes. The engine signs the list and checks each candidate
against its actual release prefix. -/
noncomputable def pollBatch
    (st : State sp ro (binding := binding))
    (t : Time) (release : Fin sp.n → Time → Bool := fun _ _ => true) :
    State sp ro (binding := binding) ×
      List (Body × List (Wire sp.n (binding := binding))) :=
  let flush := release st.self st.now && st.ticked
  let r := poll (if flush then
      { st with held := [], node := st.held.foldl (fun n a => (Node.onAttestation n a).1) st.node }
    else st) t release
  (r.1, r.2.toList ++ (st.forwards.map fun p => (.forward p.1, p.2)) ++
    (st.voteForwards.map fun p => (.voteForward p.1 (encodeVote p.2.1), [p.2.2])) ++
    (if flush then st.held.map fun a => (.att (encodeAtt a), []) else []))

/-- The chain of headers from genesis (excluded) to `B`, oldest first, by parent walk in the
held blocks `blocks`, with `fuel` steps at most. -/
noncomputable def chainTo (blocks : Nat → Option (Blk sp)) : Nat → Blk sp → Chain Info :=
  NodeAsChainShape.chainTo (P := sp.toParams) (headerOf sp) blocks

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
noncomputable def restore (k : Fin sp.n)
    (d : State sp ro (binding := binding)) (t : Time) : State sp ro (binding := binding) :=
  NodeAsChainShape.restore (nodeAdapter sp ro binding) k d t

variable (sp ro) in
/-- The Goldilocks engine operations at fixed protocol parameters and voting roles. -/
noncomputable def nodeOps (binding : VoteBinding)
    (sign : Fin sp.n → Time → Bool := fun _ _ => true)
    (release : Fin sp.n → Time → Bool := fun _ _ => true) :
    NodeAsChainShape.Ops sp.n binding.Kind Info Body Out (State sp ro binding) Nat WireVote where
  init k p io := ⟨k, Node.initWith (goldilocksNode sp ro)
    (binding.installVote p (goldilocksNode sp ro).initial),
    0, [], [], false, fun _ => none, [], [], io, [], false⟩
  clock st t := { st with now := t, ticked := false }
  propose := propose
  pollPropose st _ := ({ nodeTick st sign with ticked := true }, none)
  poll st t := poll st t release
  pollBatch st t := pollBatch st t release
  gossip st _ :=
    match st.relayBuf with
    | [] => []
    | cs => [(.data .relay, cs)]
  process := process
  recordOwn := recordOwn
  restore := restore
  out g st := outOf st.node st.now g

variable (sp ro) in
/-- The Goldilocks node as a chain shape over already chosen protocol parameters.
Its grid uses `sp.Δ` directly: only `Setup.params` converts the engine delay to protocol delay. -/
noncomputable def goldilocksShape (binding : VoteBinding := stock) :
    ChainShape sp.pub Out Info :=
  NodeAsChainShape.shape { skeleton sp.pub (binding := binding) with
    grid := ⟨4 * sp.Δ, mul_pos (by decide) sp.toParams.hΔ⟩ }
    (nodeOps sp ro binding) (voteClaim (binding := binding) sp.n) voteBody
    (presented (binding := binding)) (binding.candidateRole sp.n)
    (dependencies sp.n (binding := binding)) (conflicts (binding := binding))
    (isFGAtt (binding := binding))

/-! ## The family -/

/-- The parameters of the Goldilocks node not fixed by the public parameters:
the genesis root, the FG timeout `δ_t`, the lock window `k`, the fast increment `c`, the
optimistic switch, the deep-source depth, and the restart replay order and vote binding at every
parameter set. -/
structure Setup where
  /-- The genesis root. -/
  genesisRoot : Nat
  /-- The FG timeout parameter `δ_t`. -/
  δt : Nat
  /-- The lock window `k ≥ 2`. -/
  k : Nat
  two_le_k : 2 ≤ k
  /-- The fast increment `c ≥ 2` (`ACParams.c`). -/
  c : Nat
  two_le_c : 2 ≤ c
  /-- The restart replay order depends on the validator count and fixed genesis root,
  not on a proposer schedule or timing parameters. -/
  ro : (n : Nat) → AC.ReplayOrderData n genesisRoot (List (FG.Att n))
  /-- Historical vote authentication, permission and threshold denominator. -/
  vote : VoteBinding
  /-- Whether a validator may run `ac_to_fg` and `fg_attest` at a public time.
  By default every public tick may sign. -/
  sign : (pub : Public) → Fin pub.n → Time → Bool := fun _ _ _ => true
  /-- Whether a validator may release its held signed FG attestations at a time.
  By default every time releases, so nothing is ever held. -/
  release : (pub : Public) → Fin pub.n → Time → Bool := fun _ _ _ => true
  /-- Whether the optimistic confirmation runs, one value for the whole protocol.
  By default it runs (the stock node). -/
  optimistic : Bool := true
  /-- The deep-source depth `D` in slots, one value for the whole protocol (`ACParams.deepDepth`).
  By default there are no deep sources (the stock node). -/
  deepDepth : Option Nat := none

/-- The AC parameters use protocol delay `pub.ΔAC` and slots of four protocol delays: L0 delivers
strictly before the bound (`CommLog.PSync`), which is the node's deadline `[τ, max(τ, w) + Δ)`.
The run's proposer selection is independent of these runtime parameters. -/
abbrev Setup.params (S : Setup) (pub : Public) (hn : 1 ≤ pub.n) : ACParams where
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
  committeeSize := S.vote.committeeSize pub
  optimistic := S.optimistic
  deepDepth := S.deepDepth

/-- The shape's state at the public parameters `pub`: a Goldilocks state at every proof that
`pub` has a validator. The dependence on `1 ≤ n` (which `Params` needs) is thus in the state's
*values*, never in the family's types: `(goldilocks S pub).State` is this function type, `.Body`
is `Body`, `.skel.Kind` is `S.vote.Kind`, and a run's state at `hn` is `st hn : State …` without a
cast. Without a validator there are no keys, no duties with an effect and no outputs. -/
def PubState (S : Setup) (pub : Public) : Type :=
  (hn : 1 ≤ pub.n) → State (S.params pub hn) (S.ro _) (binding := S.vote)

/-- The Goldilocks family: `goldilocksShape` at `S.params pub hn` for every `hn`, through
`PubState`; the steps that output something (a proposal, a poll body, the gossip, the
output chains) output it at some proof of `1 ≤ n` and nothing without one. -/
noncomputable def goldilocks (S : Setup) :
    ChainShapeFamily schema Info := fun pub =>
  let binding := S.vote
  NodeAsChainShape.shape (skeleton pub (binding := binding))
    (NodeAsChainShape.familyOps fun hn =>
      nodeOps (S.params pub hn) (S.ro _) binding (S.sign pub) (S.release pub))
    (voteClaim (binding := binding) pub.n) voteBody (presented (binding := binding))
    (binding.candidateRole pub.n) (dependencies pub.n (binding := binding))
    (conflicts (binding := binding)) (isFGAtt (binding := binding))

/-! ## Equations for the Goldilocks wire and state -/

/-- The family uses the Goldilocks duty grid and the setup's voting roles. -/
theorem goldilocks_skel_eq (S : Setup) (pub : Public) :
    (goldilocks S pub).skel = skeleton pub S.vote := by rfl

/-- Run the node proposal when there is a key; otherwise emit no proposal. -/
theorem goldilocks_propose_eq (S : Setup) (pub : Public) (st : PubState S pub) (s : Slot) :
    (goldilocks S pub).propose st s =
      if hn : 1 ≤ pub.n then (fun _ => (propose (st hn) s).1, (propose (st hn) s).2)
      else (st, none) := by rfl

/-- The proposal poll runs the node tick and marks the tick step done, but emits no proposal
directly. -/
theorem goldilocks_pollPropose_eq (S : Setup) (pub : Public) (st : PubState S pub) (t : Time) :
    (goldilocks S pub).pollPropose st t =
      if hn : 1 ≤ pub.n then (fun _ => { nodeTick (st hn) (S.sign pub) with ticked := true }, none)
      else (st, none) := by rfl

/-- The batch poll runs the Goldilocks poll, or emits nothing with no keys. -/
theorem goldilocks_pollBatch_eq (S : Setup) (pub : Public) (st : PubState S pub) (t : Time) :
    (goldilocks S pub).pollBatch st t =
      if hn : 1 ≤ pub.n then
        (fun _ => (pollBatch (st hn) t (S.release pub)).1, (pollBatch (st hn) t (S.release pub)).2)
      else (st, []) := by rfl

/-- Read the node's chain at its current time, or the empty chain with no keys. -/
theorem goldilocks_out_eq (S : Setup) (pub : Public) (st : PubState S pub) (g : Out) :
    (goldilocks S pub).out g st =
      if hn : 1 ≤ pub.n then outOf (st hn).node (st hn).now g else [] := by rfl

/-- Gossip wraps a nonempty relay queue once and otherwise emits nothing. -/
theorem goldilocks_gossip_eq (S : Setup) (pub : Public) (st : PubState S pub) (t : Time) :
    (goldilocks S pub).gossip st t =
      if hn : 1 ≤ pub.n then
        match (st hn).relayBuf with
        | [] => []
        | cs => [(.data .relay, cs)]
      else [] := by
  by_cases hn : 1 ≤ pub.n
  · unfold goldilocks NodeAsChainShape.shape NodeAsChainShape.familyOps
    simp only [dite_eq_left hn]
    unfold nodeOps
    cases h : (st hn).relayBuf <;> simp only [h] <;> rfl
  · unfold goldilocks NodeAsChainShape.shape NodeAsChainShape.familyOps
    simp only [dite_eq_right hn]

/-- Embedding a digest skips the reserved genesis root. -/
theorem taggedRoot_eq (g h : Nat) : taggedRoot g h = (if h < g then h else h + 1) := by rfl

/-- Recover a raw digest by undoing the gap at the genesis root. -/
theorem rawRoot_eq (g r : Nat) : rawRoot g r = (if r < g then r else r - 1) := by rfl

/-- A missing or genesis parent is `.root`; any other parent is a raw digest. -/
theorem parentRef_eq (g : Nat) (r : Option Nat) : parentRef g r = (match r with
  | none => .root
  | some r => if r = g then .root else .digest (rawRoot g r)) := by cases r <;> rfl

/-- Decode a parent reference as genesis or a tagged digest. -/
theorem parentRoot_eq (g : Nat) (p : ParentRef) : parentRoot g p = (match p with
  | .root => some g
  | .digest r => some (taggedRoot g r)) := by cases p <;> rfl

/-- Read the digest paired with the first matching header. -/
theorem rootOf_eq (hs : List (Header Info × Nat)) (h : Header Info) :
    rootOf hs h = (hs.find? fun q => q.1 == h).map (·.2) := by rfl

/-- A block header contains its parent reference, slot, input and encoded payloads. -/
theorem headerOf_eq (B : Blk sp) : headerOf sp B =
    ⟨parentRef sp.genesisRoot B.parent, B.slot, B.input, encodeInfo B.fgPayload B.acPayload⟩ := by
  rfl

/-- Reconstruct a block from its header, digest, signer and decoded payloads. -/
theorem blockOf_eq (d : Nat) (h : Header Info) (k : Fin sp.n) (atts : List (FG.Att sp.n))
    (p : Payload sp.n) : blockOf sp d h k atts p =
    ⟨taggedRoot sp.genesisRoot d, parentRoot sp.genesisRoot h.parent,
      h.pos, k, h.input, atts, p⟩ := by
  rfl

/-- A block object is a proposer-signed header carrying both payloads' objects. -/
theorem blockObj_eq (B : Blk sp) : blockObj sp (binding := binding) B =
    .mk (.signed B.proposer (.proposer B.slot)) (.item (headerOf sp B))
      (payloadObjs (binding := binding) B.fgPayload B.acPayload) := by rfl

open Classical in
/-- Decode a block only if its signature role, carried objects and payload checks agree. -/
theorem decodeBlock_eq (hs : List (Header Info × Nat)) (o : Wire sp.n binding) :
    decodeBlock sp hs o = (match o with
    | .mk (.signed k (.proposer s)) (.item h) cs =>
      match decodeInfo sp.n h.info, rootOf hs h with
      | some (atts, p), some d =>
        let B := blockOf sp d h k atts p
        if h.pos = s ∧ cs = payloadObjs (binding := binding) atts p ∧
            (∀ a ∈ atts, a.WellFormed) ∧ AC.validPayload B then some B else none
      | _, _ => none
    | _ => none) := by
  obtain ⟨a, m, cs⟩ := o
  cases a with
  | none => cases m <;> rfl
  | signed k r =>
    cases r <;> cases m <;> try rfl
    rename_i h
    have hr : NodeAsChainShape.rootOf hs h = rootOf hs h := rfl
    simp only [decodeBlock, NodeAsChainShape.decodeBlock, hr]
    cases decodeInfo sp.n h.info with
    | none => rfl
    | some ap =>
      rcases ap with ⟨atts, p⟩
      cases rootOf hs h with
      | none => rfl
      | some d =>
        have hb : NodeAsChainShape.blockOf (P := sp.toParams) d h k atts p =
            blockOf sp d h k atts p := rfl
        simp only [hb]

/-- Classify a receipt by trying the block, vote and attestation decoders in order. -/
theorem canonEvent_eq (io : VoteAuth sp.n binding) (hs : List (Header Info × Nat))
    (o : Wire sp.n binding) :
    canonEvent sp ro io hs o =
      (match decodeBlock sp hs o, decodeVoteObj sp io o, decodeAttObj sp o with
    | some B, _, _ => some (.block B)
    | none, some v, _ => some (.message v)
    | none, none, some a => some (.attestation a)
    | none, none, none => none) := by
  unfold canonEvent NodeAsChainShape.canonEvent
  have hb : NodeAsChainShape.decodeBlock (wireCodec sp ro binding io).decode
      (wireCodec sp ro binding io).carried
      (goldilocksNode sp ro).validPayload hs o = decodeBlock sp hs o := rfl
  have hv : (wireCodec sp ro binding io).message o = decodeVoteObj sp io o := rfl
  have ha : (wireCodec sp ro binding io).attestation o = decodeAttObj sp o := rfl
  rw [hb, hv, ha]
  cases decodeBlock sp hs o <;> cases decodeVoteObj sp io o <;> cases decodeAttObj sp o <;> rfl

open Classical in
/-- Dispatch a decoded receipt, relaying newly accepted blocks and attestations. -/
theorem processOne_eq (io : VoteAuth sp.n binding) (hs : List (Header Info × Nat))
    (st : State sp ro binding) (o : Wire sp.n binding) :
    processOne io hs st o = (match canonEvent sp ro io hs o with
    | some (.block B) =>
      let r := Node.onBlock st.self st.node st.now B
      relayIf (apply st none r)
        (st.node.fg.blocks B.root ≠ some B ∧ r.1.fg.blocks B.root = some B) o
    | some (.message v) => apply st (some o) (Node.onMessage st.self st.node st.now v)
    | some (.attestation a) => relayIf (apply st none (Node.onAttestation st.node a)) True o
    | _ => st) := by
  unfold processOne NodeAsChainShape.processOne
  have h : NodeAsChainShape.canonEvent (wireCodec sp ro binding io) hs o =
      canonEvent sp ro io hs o := rfl
  rw [h]
  cases canonEvent sp ro io hs o with
  | none => rfl
  | some e => cases e <;> rfl

/-- Refuse block-shaped receipts unless they decode to a timely, FG-accepted block. -/
theorem refuses_iff (io : VoteAuth sp.n binding) (hs : List (Header Info × Nat))
    (st : State sp ro binding) (o : Wire sp.n binding) :
    Refuses io hs st o ↔ BlockShaped o ∧ ∀ B, canonEvent sp ro io hs o = some (.block B) →
      sp.toParams.slotOf st.now < B.slot ∨ st.node.fg.onBlock B = none := by rfl

open Classical in
/-- Visit the receipt first; descend into its carried objects only if it is not refused. -/
theorem visit_eq (io : VoteAuth sp.n binding) (hs : List (Header Info × Nat))
    (st : State sp ro binding)
    (a : Model.Auth sp.n (ShapeRole binding.Kind)) (m : Msg (Header Info) Body)
    (cs : List (Wire sp.n binding)) :
    visit io hs st (.mk a m cs) =
      if Refuses io hs st (.mk a m cs) then ([.mk a m cs], processOne io hs st (.mk a m cs))
      else
        let r := visitList io hs (processOne io hs st (.mk a m cs)) cs
        (.mk a m cs :: r.1, r.2) := by
  rw [visit, NodeAsChainShape.visit]
  rfl

/-- An empty carried list leaves the state unchanged. -/
theorem visitList_nil_eq (io : VoteAuth sp.n binding) (hs : List (Header Info × Nat))
    (st : State sp ro binding) :
    visitList io hs st [] = ([], st) := by rw [visitList, NodeAsChainShape.visitList]

/-- Visit the first carried object before the rest, threading the state and receipt order. -/
theorem visitList_cons_eq (io : VoteAuth sp.n binding) (hs : List (Header Info × Nat))
    (st : State sp ro binding) (o : Wire sp.n binding) (os : List (Wire sp.n binding)) :
    visitList io hs st (o :: os) =
      (let r := visit io hs st o; let r' := visitList io hs r.2 os; (r.1 ++ r'.1, r'.2)) := by
  rw [visitList, NodeAsChainShape.visitList]
  rfl

/-- Delivery records the ordered objects returned by the receipt walk. -/
theorem delivered_eq (io : VoteAuth sp.n binding) (hs : List (Header Info × Nat))
    (st : State sp ro binding) (o : Wire sp.n binding) :
    delivered io hs st o = (visit io hs st o).1 := by rfl

/-- Process the delivered objects in order, starting from the original state. -/
theorem process_eq (st : State sp ro binding) (o : Wire sp.n binding)
    (hs : List (Header Info × Nat)) :
    process st o hs =
      (delivered st.voteIO hs st o).foldl (processOne st.voteIO hs) st := by rfl

/-- On own release, clear the relay queue or insert the block with its released digest. -/
theorem recordOwn_eq (st : State sp ro binding) (o : Wire sp.n binding)
    (hs : List (Header Info × Nat)) :
    recordOwn st o hs = (match o with
    | .mk .none (.data .relay) _ => { st with relayBuf := [] }
    | .mk (.signed k (.proposer _)) (.item h) _ =>
      match decodeInfo sp.n h.info, rootOf hs h with
      | some (atts, p), some d =>
        apply st none (Node.onBlock st.self st.node st.now (blockOf sp d h k atts p))
      | _, _ => st
    | _ => st) := by
  obtain ⟨a, m, cs⟩ := o
  cases a with
  | none => cases m with
    | item => rfl
    | data m => cases m <;> rfl
  | signed k r =>
    cases r <;> cases m <;> try rfl
    rename_i h
    have hr : NodeAsChainShape.rootOf hs h = rootOf hs h := rfl
    simp only [recordOwn, NodeAsChainShape.recordBlock, wireCodec, hr]
    cases decodeInfo sp.n h.info with
    | none => rfl
    | some ap => rcases ap with ⟨a, p⟩; cases rootOf hs h <;> rfl

open Classical in
/-- At a public time, queue AC tick emissions and set the FG duty from the calendar. -/
theorem nodeTick_eq (st : State sp ro binding)
    (sign : Fin sp.n → Time → Bool := fun _ _ => true) : nodeTick st sign =
    if sp.toParams.IsPublic st.now then
      let r := Node.acCall st.self st.node st.now .tick
      { apply st none (r.1, [r.2]) with fgDue := sign st.self st.now }
    else st := by rfl

/-- A proposal updates node state and, if present, encodes the head and payloads. -/
theorem propose_eq (st : State sp ro binding) (s : Slot) : propose st s =
    (let r := Node.acProposal st.node st.now
     let st' := { st with node := r.1 }
     match r.2.2 with
     | none => (st', none)
     | some (d, p) =>
       let atts := r.1.fg.proposalAttestations d.head
       (st', some (parentRef sp.genesisRoot (some d.head.root), encodeInfo atts p,
         payloadObjs atts p))) := by
  unfold propose NodeAsChainShape.propose
  cases h : (Node.acProposal st.node st.now).2.2 with
  | none => simp only [nodeAdapter, h]
  | some dp => rcases dp with ⟨d, p⟩; simp only [nodeAdapter, wireCodec, h]; rfl

/-- Clear the FG duty flag; if AC supplies an attestable source, queue the attestation when the
release schedule allows it at the node's time, processed by the own `on_attestation`, and hold
it otherwise, with only the record changed. -/
theorem fgUpdate_eq (st : State sp ro binding)
    (release : Fin sp.n → Time → Bool := fun _ _ => true) : fgUpdate st release =
    (let r := Node.acToFG st.node st.now
     let st₁ := { st with node := r.1, fgDue := false }
     match r.2.2 with
     | none => st₁
     | some C => match r.1.fg.attest r.1.record st.self C with
       | none => st₁
       | some (a, Λ') =>
         if release st.self st.now then
           { st₁ with
             node := (Node.onAttestation { r.1 with record := Λ' } a).1
             outbox := st₁.outbox ++ [.att (encodeAtt a)] }
         else
           { st₁ with
             node := { r.1 with record := Λ' }
             held := st₁.held ++ [a] }) := by
  unfold fgUpdate NodeAsChainShape.fgUpdate
  cases h : (Node.acToFG st.node st.now).2.2 with
  | none => simp only [nodeAdapter, h]
  | some B =>
    simp only [nodeAdapter, h]
    cases (Node.acToFG st.node st.now).1.fg.attest
      (Node.acToFG st.node st.now).1.record st.self B with
    | none => rfl
    | some ar => rcases ar with ⟨a, r⟩; rfl

/-- With no remaining fuel the parent walk returns no headers. -/
theorem chainTo_zero_eq (blocks : Nat → Option (Blk sp)) (B : Blk sp) :
    chainTo blocks 0 B = [] := by rfl

/-- Walk a non-genesis parent's chain before appending the current header. -/
theorem chainTo_succ_eq (blocks : Nat → Option (Blk sp)) (fuel : Nat) (B : Blk sp) :
    chainTo blocks (fuel + 1) B = (if B.root = sp.genesisRoot then [] else
      (match B.parent.bind blocks with | some Bp => chainTo blocks fuel Bp | none => []) ++
        [headerOf sp B]) := by
  rw [chainTo, NodeAsChainShape.chainTo]
  split_ifs
  · rfl
  · cases B.parent.bind blocks <;> rfl

/-- Restart through the node handler, installing the key and time and clearing the FG duty flag. -/
theorem restore_eq (k : Fin sp.n) (d : State sp ro binding) (t : Time) : restore k d t =
    (let r := Node.restart k d.node t
     { apply { d with self := k, now := t } none r with fgDue := false }) := by rfl

end Consensus.Goldilocks.AsChainShape

end
