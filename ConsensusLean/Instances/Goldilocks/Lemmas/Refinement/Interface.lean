module
public import ConsensusLean.Spec.Shape.Run
public import ConsensusLean.Instances.Goldilocks.Refinement.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.TraceDefs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Common.Params

public section

/-! # Goldilocks Refinement: proof-side simulation interface

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` (goldilocks main
`4ea71d05`), the Refinement row of the module table: **the engine simulates the node (C0.4
kept)** and **G1.5, evidence binding**, over the Goldilocks shape of `Refinement/Defs`
(`family S`) run by the generic engine (`Spec/Model/Run`) and the spec's own run model
(`Spec/Run`, `GoldilocksRun`).

* **Simulation** (`Simulates`, `EngineSimulatesNode`). Every valid engine run (`ExecutionValid`)
  of the family is simulated by a run of the spec's node. The skeleton selects one proposer
  per slot; `runProposer` supplies that run-selected schedule to the node's execution laws,
  independently of its runtime state types: a `GoldilocksRun` at the engine's digest (`digestOf`)
  for the honest keys, with a monotone cut map `ι` from engine cuts to node cuts. The node state
  inside the shape's state agrees with the trace at every engine cut; each engine event is one
  group of the node (C0.4 kept: a tick at a public time is the node's tick with the engine's
  input, a delivery is the groups of the canonical objects it carries, a restart is a restart
  group) or no cut (a tick at a non-public time, a dropped object); every labelled node cut
  belongs to an engine event; awake agrees up to the spec's horizon clamp. The engine releases
  what the node sends: an own block at its proposal time, a vote or an attestation at its
  emission or signing time (`ReleasedFrom`), an accepted block or a received attestation in a
  relay wrapper at the admission time (`RelayedFrom`), and an admitted or own vote in a signed,
  admission-stamped `.voteForward` envelope in that event (`vote_forwarded`). These obligations
  include the horizon and do not depend on a future awake time (consensus-lean#107).
* **Reads** (`ReadIsOut`): the chain trace reads the shape's outputs of the node state at the
  shape's clock, which is the time of the node's last tick or restart (`lastClock`).
* **`NoColl` transport** (`NoCollTransport`): no observed hash collision gives the spec's
  `NoColl` over the canonical engine trace; tagged roots already exclude genesis.
* **G1.5, evidence binding** (`ConflictsIff`, `EvidenceInView`, `FinalizedAccountable`): the
  instance's `conflicts` holds exactly of two canonical attestation objects whose attestations
  are `slashable` (E1/E2 of fg.tex); every attestation included on an honest finalized read is in
  that reader's view as its canonical object; and two honest finalized reads are compatible or
  at least `2q − n` validators are slashable on the two readers' views together (the run-level
  G1.3 through the simulation; target `finalized_accountable`). `nonFraming` is the generic
  `System.NonFraming` of the compiled family (`sysOf_nonFraming`, Lemmas), nothing to state here.

Not stated: the transport of the engine's network premises (`CommLog.PSync`, `SyncUntil`) to the
spec's `Sync`/`GST` (`Spec/Run/Premises`). The engine's `Delivers` holds a receipt by
`max(a, g) + Δ − 1`, strictly before `max(a, g) + Δ`, as the spec requires processing strictly
before `max(τ, w_y) + Δ'` (half-open delivery, 2026-11-04); the engine relays an admission at
the admitting delivery's own time, as the spec's instantaneous send (consensus-lean#107). The
open transport suppliers are in `Lemmas/Refinement/NetworkTransport`; they are not premises of
`AcceptedEndpoint`. `docs/goldilocks-mapping.md` §"Refinement" maps each statement.

Not in `Challenge`: this module is outside the challenge's import closure, the comparator and
`milestone_statements_modules`. Its statements are proved in `Lemmas/Refinement`
(`engineSimulatesNode`, `readIsOut`, `noCollTransport`, `evidenceInView`,
`finalizedAccountable`, …) and used only by those proofs, toward `accepted_endpoint`, and by
tests; the bundle `RefinementStatements` is assembled outside `Solution`
(`refinement_statements`, `Lemmas/Refinement/StatementsBundle`).

These proof-side claims and their characterisers are outside the trusted surface; the
certified endpoint statement remains in `Statements/Refinement/Accepted`. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape
open Consensus.Model (pubOf)
open SA (SAParams Vote Payload)

variable {sp : SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}

/-- The node's cuts for the engine's delivery of the objects `os` to `y` at time `t`, given the
digests `hs`, from cut `j` to cut `j'`: in order, one top-level event (`canonEvent`) per
canonical object, its group at the next cut; nothing for a dropped object, nor for a canonical
object whose handler makes no cut (a future-slot block, which `onBlock` refuses silently). -/
inductive DeliverSeq (proposer : Nat → Fin sp.n) (tr : GoldilocksTrace sp ro)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (y : Fin sp.n) (t : Time) :
    List (Wire sp.n) → Nat → Nat → Prop
  /-- No object, no cut. -/
  | nil (j : Nat) : DeliverSeq proposer tr dg hs y t [] j j
  /-- A canonical object: its event's group starts at `j`, and the rest follow it. -/
  | event {o : Wire sp.n} {os : List (Wire sp.n)} {j j' : Nat}
      (e : Node.Event (goldilocksNode sp ro)) : canonEvent sp ro hs o = some e →
      tr.GroupAt proposer dg y j t e →
      DeliverSeq proposer tr dg hs y t os
        (j + (Node.exec proposer dg y (tr.state y j) t e).2.length) j' →
      DeliverSeq proposer tr dg hs y t (o :: os) j j'
  /-- A dropped object has no cut. -/
  | drop {o : Wire sp.n} {os : List (Wire sp.n)} {j j' : Nat} : canonEvent sp ro hs o = none →
      DeliverSeq proposer tr dg hs y t os j j' →
      DeliverSeq proposer tr dg hs y t (o :: os) j j'
  /-- A canonical object whose handler makes no cut (a future-slot block) is not an event of the
  run (`GroupAt` needs a cut), so it has no cut either. -/
  | noCut {o : Wire sp.n} {os : List (Wire sp.n)} {j j' : Nat}
      (e : Node.Event (goldilocksNode sp ro)) : canonEvent sp ro hs o = some e →
      (Node.exec proposer dg y (tr.state y j) t e).2 = [] →
      DeliverSeq proposer tr dg hs y t os j j' →
      DeliverSeq proposer tr dg hs y t (o :: os) j j'

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- The time of the last tick or restart of `v` before engine cut `i` (`0` if none): what the
shape's clock holds there. -/
def lastClock (v : V) : Nat → Time
  | 0 => 0
  | i + 1 =>
    match rho.events[i]? with
    | some (.tick v' t) => if v' = v then t else lastClock v i
    | some (.restart v' t) => if v' = v then t else lastClock v i
    | _ => lastClock v i

/-- The object `o` of node `v` is released at its emission time `τ`, with no later-tick
or no-future-awake alternative. -/
def ReleasedFrom (v : V) (o : (Model.protoOf (compiled (family S)) E).Object) (τ : Time) :
    Prop :=
  rho.releases v o τ

/-- The object `o` admitted by node `v` at `τ` is relayed, as a carried object of an unsigned
relay wrapper, at that same time `τ`, including an admission at the horizon. -/
def RelayedFrom (v : V) (o : (Model.protoOf (compiled (family S)) E).Object) (τ : Time) :
    Prop :=
  ∃ cs, o ∈ cs ∧ rho.releases v (.mk .none (.data .relay) cs) τ

/-- **The node run `tr` with the cut map `ι` simulates the engine run `rho`** (claims
§"Refinement": "the engine simulates the node (C0.4 kept)"). -/
structure Simulates (tr : GoldilocksTrace (S.params (pubOf E) hn) (S.ro _)) (ι : Nat → Nat) :
    Prop where
  /-- The trace is a run of the Goldilocks protocol at the engine's digest, for the honest keys. -/
  run : GoldilocksRun (runProposer S rho hn) (digestOf S rho) (honestKeys S rho) tr
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
      tr.GroupAt (runProposer S rho hn) (digestOf S rho) (rho.ownKey v) (ι i) t
          (.tick (encodeTxs (Model.mempool rho.inbox v t))) ∧
        ι (i + 1) = ι i + (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
          (tr.state (rho.ownKey v) (ι i)) t
          (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2.length
  /-- An engine tick at a non-public time has no cut. -/
  tick_other : ∀ v ∈ rho.honest, ∀ i t, rho.events[i]? = some (.tick v t) →
    ¬ (S.params (pubOf E) hn).toParams.IsPublic t → ι (i + 1) = ι i
  /-- An engine delivery to an honest node is the groups of the canonical objects it delivers,
  in order, with the digests the engine passes. -/
  deliver : ∀ v ∈ rho.honest, ∀ i o t, rho.events[i]? = some (.deliver v o t) →
    DeliverSeq (runProposer S rho hn) tr (digestOf S rho)
      (Model.digests rho.hash o) (rho.ownKey v) t
      (delivered (S.params (pubOf E) hn) o) (ι i) (ι (i + 1))
  /-- An engine restart of an honest node is the node's restart group. -/
  restart : ∀ v ∈ rho.honest, ∀ i t, rho.events[i]? = some (.restart v t) →
    tr.GroupAt (runProposer S rho hn) (digestOf S rho) (rho.ownKey v) (ι i) t .restart ∧
      ι (i + 1) = ι i + (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
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
  /-- The engine releases an honest node's vote at its emission time. -/
  vote_released : ∀ y ∈ honestKeys S rho, ∀ k m, tr.EmitAt y k m →
    ReleasedFrom S rho (rho.key y) (voteObj m) (tr.time k)
  /-- The engine releases an honest node's attestation at its signing time. -/
  att_released : ∀ y ∈ honestKeys S rho, ∀ k a, tr.SignAt y k a →
    ReleasedFrom S rho (rho.key y) (attObj a) (tr.time k)
  /-- An honest node relays a block it accepts from the wire (a delivery, position `0`). -/
  block_relayed : ∀ y ∈ honestKeys S rho, ∀ k B, tr.AcceptAt y k B → tr.pos k = 0 →
    RelayedFrom S rho (rho.key y) (blockObj (S.params (pubOf E) hn) B) (tr.time k)
  /-- Fresh wire/payload admissions and own emissions publish a signed admission-stamped
  envelope in their actual engine event, including the horizon. Restart replay is not an
  admission. The exact envelope has no earlier engine release. -/
  vote_forwarded : ∀ y ∈ honestKeys S rho, ∀ k (m : Vote (Fintype.card V)),
    (tr.EmitAt y k m ∨
      ((tr.MsgCallAt y k m ∨ ∃ ℓ B, tr.CallAt y k (.ac ℓ) ∧ ℓ.call = .block B ∧
          m ∈ SA.blockVotes B) ∧
        m ∉ (tr.state y k).ac.pool m.slot ∧ m ∈ (tr.post k).ac.pool m.slot)) →
    let envelope : (Model.protoOf (compiled (family S)) E).Object :=
      .mk (.signed y .poll) (.data (.voteForward (tr.time k) (encodeVote m))) [voteObj m]
    ∃ i, ι i ≤ k ∧ k < ι (i + 1) ∧ rho.SendsAt (rho.key y) i (tr.time k) ∧
      envelope ∈ rho.releasesAt i ∧ ∀ j < i, envelope ∉ rho.releasesAt j
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

/-- Every observed item's tagged node root differs from genesis. The raw engine
hash remains arbitrary, including hashes equal to the numeric genesis root. -/
def GenesisFresh : Prop :=
  ∀ x, rho.ObservedItem x → taggedRoot S.genesisRoot (rho.hash x) ≠ S.genesisRoot

variable (V) in
/-- **`NoColl` transport.** Without an observed hash collision, the canonical engine trace
satisfies `NoCollRun` on every occurring block and genesis. Arbitrary simulation witnesses
are not covered: their simulation laws do not identify every occurrence with an engine object.
Tagged roots exclude genesis without an additional premise. -/
def NoCollTransport : Prop :=
  ∀ (E : Env V) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V),
    rho.ExecutionValid → ¬ rho.HashCollision →
      Compose.NoCollRun (digestOf S rho) (simTrace S rho hn)

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
In a valid run without an observed hash collision, two honest finalized reads are
compatible (one a prefix of the other), or at least
`2q − n` validators are slashable on the two readers' views together.

Limitation (a reading of the statement, not a defect of its proof): the evidence is the union of
the two **views** (`ViewIdx u i ∪ ViewIdx v j`), as the generic L0 accountability convicts from
views. CLAIMS G1.5 and G1.3 restrict the slashable pairs to the attestations included on the two
finalized chains. The views contain those attestations (`EvidenceInView`), so this conclusion is
weaker than G1.5's: the slashable pairs may come from viewed attestations on neither chain. A
chain-restricted statement would be a separate proposal. -/
def FinalizedAccountable : Prop :=
  ∀ (E : Env V) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V),
    rho.ExecutionValid → ¬ rho.HashCollision →
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

/-- The initial shape clock. -/
theorem lastClock_zero (v : V) : lastClock S rho v 0 = 0 := by rfl

/-- Only a tick or restart of this node changes its clock. -/
theorem lastClock_succ (v : V) (i : Nat) : lastClock S rho v (i + 1) =
    match rho.events[i]? with
    | some (.tick v' t) => if v' = v then t else lastClock S rho v i
    | some (.restart v' t) => if v' = v then t else lastClock S rho v i
    | _ => lastClock S rho v i := by rfl

/-- Release means an engine release at the stated time. -/
theorem releasedFrom_iff (v : V) (o : (Model.protoOf (compiled (family S)) E).Object)
    (τ : Time) : ReleasedFrom S rho v o τ ↔ rho.releases v o τ := by rfl

/-- Relay means carrying the object in an unsigned relay released at the stated time. -/
theorem relayedFrom_iff (v : V) (o : (Model.protoOf (compiled (family S)) E).Object)
    (τ : Time) : RelayedFrom S rho v o τ ↔
      ∃ cs, o ∈ cs ∧ rho.releases v (.mk .none (.data .relay) cs) τ := by rfl

variable (V) in
/-- Every valid engine run has a simulating node run. -/
theorem engineSimulatesNode_iff : EngineSimulatesNode V S ↔
    ∀ (E : Env V) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V),
      rho.ExecutionValid → ∃ tr ι, Simulates S rho hn tr ι := by rfl

variable (V) in
/-- Engine reads are exactly the embedded node's outputs. -/
theorem readIsOut_iff : ReadIsOut V S ↔
    ∀ (E : Env V) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V),
      ∀ (g : Out) (v : V) (i : Nat),
        (chainTrace rho).read g v i =
          outOf (stateAt S rho hn v i).node (stateAt S rho hn v i).now g := by rfl

/-- Observed tagged roots differ from genesis. -/
theorem genesisFresh_iff : GenesisFresh S rho ↔
    ∀ x, rho.ObservedItem x → taggedRoot S.genesisRoot (rho.hash x) ≠ S.genesisRoot := by rfl

variable (V) in
/-- Collision transport targets the canonical trace, not an arbitrary simulation. -/
theorem noCollTransport_iff : NoCollTransport V S ↔
    ∀ (E : Env V) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V),
      rho.ExecutionValid → ¬ rho.HashCollision →
        Compose.NoCollRun (digestOf S rho) (simTrace S rho hn) := by rfl

/-- Conflicts are exactly canonical slashable attestation pairs. -/
theorem conflictsIff_iff : ConflictsIff ↔
    ∀ (n : Nat) (o o' : Wire n),
      conflicts o o' = true ↔
        ∃ a b : FG.Att n, o = attObj a ∧ o' = attObj b ∧ FG.slashable a b := by
  rfl

variable (V) in
/-- Finalized attestations are in the reader's engine view. -/
theorem evidenceInView_iff : EvidenceInView V S ↔
    ∀ (E : Env V) (rho : Model.Run (compiled (family S)) E), rho.ExecutionValid →
      ∀ v ∈ rho.honest, ∀ i ≤ rho.events.length,
        ∀ h ∈ (chainTrace rho).read .finalized v i, ∀ atts (p : Payload (Fintype.card V)),
          decodeInfo (Fintype.card V) h.info = some (atts, p) →
            ∀ a ∈ atts, attObj a ∈ rho.ViewIdx v i := by rfl

variable (V) in
/-- Incompatible finalized reads convict the threshold from the union of the views. -/
theorem finalizedAccountable_iff : FinalizedAccountable V S ↔
    ∀ (E : Env V) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V),
      rho.ExecutionValid → ¬ rho.HashCollision →
      ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ i ≤ rho.events.length, ∀ j ≤ rho.events.length,
        Consensus.Compatible ((chainTrace rho).read .finalized u i)
            ((chainTrace rho).read .finalized v j) ∨
          2 * (S.params (pubOf E) hn).toParams.q - Fintype.card V ≤
            (convicted rho.Slashable (rho.ViewIdx u i ∪ rho.ViewIdx v j)).card := by rfl

end Consensus.Goldilocks.Refinement

end
