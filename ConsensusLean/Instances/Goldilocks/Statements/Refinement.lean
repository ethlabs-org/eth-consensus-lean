module
public import ConsensusLean.Spec.Shape.Run
public import ConsensusLean.Instances.Goldilocks.Refinement.Defs
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Run

@[expose] public section

/-! # Goldilocks milestone Refinement (statements)

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` (goldilocks main
`4ea71d05`), the Refinement row of the module table: **the engine simulates the node (C0.4
kept)** and **G1.5, evidence binding**, over the Goldilocks shape of `Refinement/Defs`
(`family S`) run by the generic engine (`Spec/Model/Run`) and the spec's own run model
(`Spec/Run`, `GoldilocksRun`).

* **Simulation** (`Simulates`, `EngineSimulatesNode`). Every valid engine run (`ExecutionValid`)
  of the family is simulated by a run of the spec's node (the skeleton's proposer selection is
  the setup's schedule, `fixed {proposer s}` at every slot, so a valid run's proposer of a slot
  is the spec node's own `proposer`): a `GoldilocksRun` at the engine's digest (`digestOf`)
  for the honest keys, with a monotone cut map `ι` from engine cuts to node cuts. The node state
  inside the shape's state agrees with the trace at every engine cut; each engine event is one
  group of the node (C0.4 kept: a tick at a public time is the node's tick with the engine's
  input, a delivery is the groups of the canonical objects it carries, a restart is a restart
  group) or no cut (a tick at a non-public time, a dropped object); every labelled node cut
  belongs to an engine event; awake agrees up to the spec's horizon clamp. The engine releases
  what the node sends: an own block at its proposal time, a vote or an attestation at the first
  awake time from its emission (`ReleasedFrom`; a body emitted at a delivery waits for the next
  tick, and a sleep delays it), and an admitted block, vote or attestation in a relay wrapper at
  the next awake time after the admission (`RelayedFrom`).
* **Reads** (`ReadIsOut`): the chain trace reads the shape's outputs of the node state at the
  shape's clock, which is the time of the node's last tick or restart (`lastClock`).
* **`NoColl` transport** (`NoCollTransport`): no observed hash collision and no observed item
  hashing to the genesis root give the spec's `NoColl` over the simulating run.
* **G1.5, evidence binding** (`ConflictsIff`, `EvidenceInView`, `FinalizedAccountable`): the
  instance's `conflicts` holds exactly of two canonical attestation objects whose attestations
  are `slashable` (E1/E2 of fg.tex); every attestation included on an honest finalized read is in
  that reader's view as its canonical object; and two honest finalized reads are compatible or
  at least `2q − n` validators are slashable on the two readers' views together (the run-level
  G1.3 through the simulation; target `finalized_accountable`). `nonFraming` is the generic
  `System.NonFraming` of the compiled family (`sysOf_nonFraming`, Lemmas), nothing to state here.

Not stated: the transport of the engine's network premises (`CommLog.PSync`, `SyncUntil`) to the
spec's `Sync`/`GST` (`Spec/Run/Premises`). The engine's `Delivers` bounds a receipt by
`max(a, g) + Δ` while the spec requires processing strictly before `max(τ, w_y) + Δ'`, and the
spec treats an admission as an instantaneous send while the engine relays at the admitting
node's next awake tick (`RelayedFrom`): the regimes milestone states the transport, once the
spec orb decides the slack. `docs/goldilocks-mapping.md` §"Refinement" maps each statement.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape
open Consensus.Model (pubOf)
open SA (SAParams Vote Payload)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- The honest keys of a run (`H` of the spec's run laws). -/
def honestKeys : Set (Fin (Fintype.card V)) := {k | rho.key k ∈ rho.honest}

/-- The node's digest in a run: `dgOf` of the engine's hash with the setup's genesis root. -/
noncomputable def digestOf :
    Digest (List (FG.Att (Fintype.card V))) (Payload (Fintype.card V)) :=
  dgOf rho.hash S.genesisRoot

/-- The shape's state of node `v` before engine cut `i`, at the parameters of the run. -/
noncomputable def stateAt (v : V) (i : Nat) : State (S.params (pubOf E) hn) (S.ro _) :=
  (rho.stateBefore i v).st.1 hn

/-- The time of the last tick or restart of `v` before engine cut `i` (`0` if none): what the
shape's clock holds there. -/
def lastClock (v : V) : Nat → Time
  | 0 => 0
  | i + 1 =>
    match rho.events[i]? with
    | some (.tick v' t) => if v' = v then t else lastClock v i
    | some (.restart v' t) => if v' = v then t else lastClock v i
    | _ => lastClock v i

/-- The object `o` of node `v`, queued at `τ`, is released at the first time from `τ` on at which
`v` is awake, if there is one within the horizon: a body emitted inside a tick goes out in that
tick, a body emitted at a delivery at the next tick, and a sleep delays the send. -/
def ReleasedFrom (v : V) (o : (Model.protoOf (compiled (family S)) E).Object) (τ : Time) :
    Prop :=
  (∃ t', τ ≤ t' ∧ rho.releases v o t' ∧ ∀ u, τ < u → u < t' → E.awake v u = false) ∨
    ∀ u, τ < u → u ≤ rho.horizon → E.awake v u = false

/-- The object `o` admitted by node `v` at `τ` is relayed, as a carried object of an unsigned
relay wrapper, at the first time after `τ` at which `v` is awake, if there is one within the
horizon. -/
def RelayedFrom (v : V) (o : (Model.protoOf (compiled (family S)) E).Object) (τ : Time) :
    Prop :=
  (∃ t' cs, τ < t' ∧ o ∈ cs ∧ rho.releases v (.mk .none (.data .relay) cs) t' ∧
      ∀ u, τ < u → u < t' → E.awake v u = false) ∨
    ∀ u, τ < u → u ≤ rho.horizon → E.awake v u = false

/-- **The node run `tr` with the cut map `ι` simulates the engine run `rho`** (claims
§"Refinement": "the engine simulates the node (C0.4 kept)"). -/
structure Simulates (tr : GoldilocksTrace (S.params (pubOf E) hn) (S.ro _)) (ι : Nat → Nat) :
    Prop where
  /-- The trace is a run of the Goldilocks protocol at the engine's digest, for the honest keys. -/
  run : GoldilocksRun (digestOf S rho) (honestKeys S rho) tr
  /-- The cut map starts at `0`. -/
  ι_zero : ι 0 = 0
  /-- The cut map is monotone. -/
  ι_mono : Monotone ι
  /-- Every labelled node cut lies in the range of some engine event. -/
  covered : ∀ k, tr.label k ≠ none → ∃ i < rho.events.length, ι i ≤ k ∧ k < ι (i + 1)
  /-- The node state inside the shape's state is the trace's state at the mapped cut. -/
  state : ∀ v ∈ rho.honest, ∀ i ≤ rho.events.length,
    (stateAt S rho hn v i).node = tr.state (rho.ownKey v) (ι i)
  /-- The shape's clock is the time of the node's last tick or restart. -/
  now : ∀ v i, (stateAt S rho hn v i).now = lastClock S rho v i
  /-- An engine tick of an honest node at a public time is the node's tick with the engine's
  input (the encoded mempool), one group. -/
  tick_public : ∀ v ∈ rho.honest, ∀ i t, rho.events[i]? = some (.tick v t) →
    (S.params (pubOf E) hn).toParams.IsPublic t →
      tr.GroupAt (digestOf S rho) (rho.ownKey v) (ι i) t
          (.tick (encodeTxs (Model.mempool rho.inbox v t))) ∧
        ι (i + 1) = ι i + (Node.exec (digestOf S rho) (rho.ownKey v)
          (tr.state (rho.ownKey v) (ι i)) t
          (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2.length
  /-- An engine tick at a non-public time has no cut. -/
  tick_other : ∀ v ∈ rho.honest, ∀ i t, rho.events[i]? = some (.tick v t) →
    ¬ (S.params (pubOf E) hn).toParams.IsPublic t → ι (i + 1) = ι i
  /-- An engine delivery to an honest node is the groups of the canonical objects it delivers,
  in order, with the digests the engine passes. -/
  deliver : ∀ v ∈ rho.honest, ∀ i o t, rho.events[i]? = some (.deliver v o t) →
    DeliverSeq tr (digestOf S rho) (Model.digests rho.hash o) (rho.ownKey v) t
      (delivered (S.params (pubOf E) hn) o) (ι i) (ι (i + 1))
  /-- An engine restart of an honest node is the node's restart group. -/
  restart : ∀ v ∈ rho.honest, ∀ i t, rho.events[i]? = some (.restart v t) →
    tr.GroupAt (digestOf S rho) (rho.ownKey v) (ι i) t .restart ∧
      ι (i + 1) = ι i + (Node.exec (digestOf S rho) (rho.ownKey v)
        (tr.state (rho.ownKey v) (ι i)) t .restart).2.length
  /-- An honest node awake in the trace is awake in the environment, within `[0, horizon]`. -/
  awake_of : ∀ y ∈ honestKeys S rho, ∀ t, tr.awake y t →
    E.awake (rho.key y) t = true ∧ 0 ≤ t ∧ t ≤ rho.horizon
  /-- An honest node awake in the environment at a time from `0` within the trace's horizon is
  awake in the trace (the spec's horizon clamp). -/
  awake_to : ∀ y ∈ honestKeys S rho, ∀ t, E.awake (rho.key y) t = true → 0 ≤ t →
    tr.InHorizon t → tr.awake y t
  /-- The engine releases an honest node's own block, as its canonical object, at the tick that
  proposes it. -/
  block_released : ∀ y ∈ honestKeys S rho, ∀ k B, tr.OwnBlockAt y k B →
    rho.releases (rho.key y) (blockObj (S.params (pubOf E) hn) B) (tr.time k)
  /-- The engine releases an honest node's vote from its emission on. -/
  vote_released : ∀ y ∈ honestKeys S rho, ∀ k m, tr.EmitAt y k m →
    ReleasedFrom S rho (rho.key y) (voteObj m) (tr.time k)
  /-- The engine releases an honest node's attestation from its signing on. -/
  att_released : ∀ y ∈ honestKeys S rho, ∀ k a, tr.SignAt y k a →
    ReleasedFrom S rho (rho.key y) (attObj a) (tr.time k)
  /-- An honest node relays a block it accepts from the wire (a delivery, position `0`). -/
  block_relayed : ∀ y ∈ honestKeys S rho, ∀ k B, tr.AcceptAt y k B → tr.pos k = 0 →
    RelayedFrom S rho (rho.key y) (blockObj (S.params (pubOf E) hn) B) (tr.time k)
  /-- An honest node relays a vote it admits from the wire (an `ac_on_message` call after which
  its pool holds the vote). -/
  vote_relayed : ∀ y ∈ honestKeys S rho, ∀ k m, tr.MsgCallAt y k m →
    m ∈ (tr.post k).ac.pool m.slot → RelayedFrom S rho (rho.key y) (voteObj m) (tr.time k)
  /-- An honest node relays an attestation it receives from the wire (an `fg_on_attestation`
  call at a delivery). -/
  att_relayed : ∀ y ∈ honestKeys S rho, ∀ k a, tr.AttCallAt y k a → tr.pos k = 0 →
    RelayedFrom S rho (rho.key y) (attObj a) (tr.time k)

variable (V) in
/-- **The engine simulates the node.** Every valid engine run of the family in any environment
is simulated by a run of the spec's node. -/
def EngineSimulatesNode : Prop :=
  ∀ (E : Env V) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V),
    rho.ExecutionValid → ∃ tr ι, Simulates S rho hn tr ι

variable (V) in
/-- **Reads are the shape's outputs.** The chain trace of a run reads, at every cut, the output
chains of the node state at the shape's clock. -/
def ReadIsOut : Prop :=
  ∀ (E : Env V) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V),
    ∀ (g : Out) (v : V) (i : Nat),
      (chainTrace rho).read g v i = outOf (stateAt S rho hn v i).node (stateAt S rho hn v i).now g

/-- No observed item hashes to the genesis root (the engine's hash is arbitrary; the genesis root
is a parameter, the digest of no header). -/
def GenesisFresh : Prop := ∀ x, rho.ObservedItem x → rho.hash x ≠ S.genesisRoot

variable (V) in
/-- **`NoColl` transport.** Without an observed hash collision, and with no observed item hashing
to the genesis root, the simulating run satisfies the spec's `NoColl` (`NoCollRun`: on the
blocks that occur in it and genesis). -/
def NoCollTransport : Prop :=
  ∀ (E : Env V) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V) tr ι,
    rho.ExecutionValid → Simulates S rho hn tr ι → ¬ rho.HashCollision → GenesisFresh S rho →
      Compose.NoCollRun (digestOf S rho) tr

/-- **G1.5 (a), `conflicts` is E1/E2.** The instance's slashing rule holds of two objects exactly
when they are the canonical objects of two `slashable` attestations. -/
def ConflictsIff : Prop :=
  ∀ (n : Nat) (o o' : Wire n),
    conflicts o o' = true ↔ ∃ a b : FG.Att n, o = attObj a ∧ o' = attObj b ∧ FG.slashable a b

variable (V) in
/-- **G1.5 (b), evidence in view.** Every attestation included on an honest node's finalized read
at a cut is in that node's view at the cut, as its canonical object (every header of the read is
of a block the node processed, whose object carries its payload's objects). -/
def EvidenceInView : Prop :=
  ∀ (E : Env V) (rho : Model.Run (compiled (family S)) E), rho.ExecutionValid →
    ∀ v ∈ rho.honest, ∀ i ≤ rho.events.length,
      ∀ h ∈ (chainTrace rho).read .finalized v i, ∀ atts (p : Payload (Fintype.card V)),
        decodeInfo (Fintype.card V) h.info = some (atts, p) →
          ∀ a ∈ atts, attObj a ∈ rho.ViewIdx v i

variable (V) in
/-- **G1.5 (c), finalized accountability** (the run-level G1.3; target `finalized_accountable`).
In a valid run without an observed hash collision and with no observed item hashing to the
genesis root, two honest finalized reads are compatible (one a prefix of the other), or at least
`2q − n` validators are slashable on the two readers' views together. -/
def FinalizedAccountable : Prop :=
  ∀ (E : Env V) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V),
    rho.ExecutionValid → ¬ rho.HashCollision → GenesisFresh S rho →
    ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ i ≤ rho.events.length, ∀ j ≤ rho.events.length,
      Consensus.Compatible ((chainTrace rho).read .finalized u i)
          ((chainTrace rho).read .finalized v j) ∨
        2 * (S.params (pubOf E) hn).toParams.q - Fintype.card V ≤
          (convicted rho.Slashable (rho.ViewIdx u i ∪ rho.ViewIdx v j)).card

variable (V) in
/-- The statements of milestone Refinement for the setup `S` at the validators `V`. -/
structure RefinementStatements : Prop where
  engineSimulatesNode : EngineSimulatesNode V S
  readIsOut : ReadIsOut V S
  noCollTransport : NoCollTransport V S
  conflictsIff : ConflictsIff
  evidenceInView : EvidenceInView V S
  finalizedAccountable : FinalizedAccountable V S

end Consensus.Goldilocks.Refinement

end
