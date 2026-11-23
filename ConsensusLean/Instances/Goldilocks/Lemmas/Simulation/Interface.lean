module
public import ConsensusLean.Spec.Shape.Run
public import ConsensusLean.Instances.Goldilocks.AsChainShape
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.TraceDefs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Common.Params

public section

/-! # Goldilocks Simulation: proof-side simulation interface

Transcribed from `specs/goldilocks/tex/goldilocks-claims.tex`,
the Refinement row of the module table: **the engine simulates the node (C0.4
kept)** and **G1.5, evidence binding**, over the Goldilocks shape of `AsChainShape`
(`goldilocks S`) run by the generic engine (`Spec/Model/Run`) and the spec's own run model
(`Spec/Run`, `GoldilocksRun`).

* **Simulation** (`SimulatesAt`, `Growing/Simulation/Interface`). A run of the spec's node simulates
  an engine run of the family. The skeleton selects one proposer per slot; `runProposer` supplies
  that run-selected schedule to the node's execution laws, independently of its runtime state types:
  a `GoldilocksRun` at the engine's digest (`digestOf`) for the honest keys, with a monotone cut map
  `ι` from engine cuts to node cuts. The node state inside the shape's state agrees with the trace
  at every engine cut; each engine event is one group of the node (C0.4 kept: a tick at a public
  time is the node's tick with the engine's input, a delivery is the groups of the canonical objects
  it carries, a restart is a restart group) or no cut (a tick at a non-public time, a dropped
  object); every labelled node cut belongs to an engine event; awake agrees up to the spec's horizon
  clamp. The engine releases what the node sends: an own block at its proposal time, a vote or an
  attestation at its emission or signing time (`ReleasedFrom`), an accepted block or a received
  attestation in a relay wrapper at the admission time (`RelayedFrom`), and an admitted or own vote
  in a signed, admission-stamped `.voteForward` envelope in that event (`vote_forwarded`). These
  obligations include the horizon and do not depend on a future awake time.
* **Reads** (`ReadIsOut`): the chain trace reads the shape's outputs of the node state at the
  shape's clock, which is the time of the node's last tick or restart (`lastClock`).
* **Genesis freshness** (`GenesisFresh`): tagged roots exclude genesis from every observed item,
  so `NoColl` over the canonical engine trace needs no genesis premise.
* **G1.5 (a), `conflicts` is E1/E2** (`ConflictsIff`): the instance's `conflicts` holds exactly
  of two canonical attestation objects whose attestations are `slashable` (E1/E2 of fg.tex).
  `nonFraming` is the generic `System.NonFraming` of the compiled family (`sysOf_nonFraming`,
  Lemmas), nothing to state here.

Not stated: the transport of the engine's network premises (`CommLog.PSync`, `SyncUntil`) to the
spec's `Sync`/`GST` (`Spec/Run/Premises`). The engine's `Delivers` holds a receipt by
`max(a, g) + Δ − 1`, strictly before `max(a, g) + Δ`, as the spec requires processing strictly
before `max(τ, w_y) + Δ'` (half-open delivery); the engine relays an admission at
the admitting delivery's own time, as the spec's instantaneous send. The obligations proof does
not need the whole-run transport: the per-service suppliers of `Lemmas/Growing/Obligations/Network`
give it directly, at every vote binding. `docs/goldilocks-mapping.md` §"AsChainShape, Simulation
and Obligations" maps each statement.

Not in `Challenge`: this module is outside the challenge's import closure, the comparator and
`milestone_statements_modules`. Its statements are proved in `Lemmas/Simulation` (`readIsOut`,
`conflicts_iff`) and used by the proofs toward `meets_obligations`; the growing-fault forms of the
simulation, the `NoColl` transport and G1.5 (b) and (c) are proved in `Lemmas/Growing/Simulation`
(`simTraceAt_simulates`, `noCollRun_simTraceAt`, `held_att_in_view_at`, `final_accountable_at`).

These proof-side claims and their characterisers are outside the trusted surface; the
certified endpoint statement remains in `Statements/Obligations`. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape
open Consensus.Model (pubOf)
open AC (ACParams Vote Payload)

variable {binding : VoteBinding}

variable {sp : ACParams} {ro : AC.ReplayOrder sp (List (FG.Att sp.n))}

/-- The node's cuts for the engine's delivery of the objects `os` to `y` at time `t`, given the
digests `hs`, from cut `j` to cut `j'`: in order, one top-level event (`canonEvent`) per
canonical object, its group at the next cut; nothing for a dropped object, nor for a canonical
object whose handler makes no cut (a future-slot block, which `onBlock` refuses silently). -/
inductive DeliverSeq (proposer : Nat → Fin sp.n) (tr : GoldilocksTrace sp ro)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (io : VoteAuth sp.n binding) (hs : List (Header Info × Nat)) (y : Fin sp.n) (t : Time) :
    List (Wire sp.n binding) → Nat → Nat → Prop
  /-- No object, no cut. -/
  | nil (j : Nat) : DeliverSeq proposer tr dg io hs y t [] j j
  /-- A canonical object: its event's group starts at `j`, and the rest follow it. -/
  | event {o : Wire sp.n binding} {os : List (Wire sp.n binding)} {j j' : Nat}
      (e : Node.Event (goldilocksNode sp ro)) : canonEvent sp ro io hs o = some e →
      tr.GroupAt proposer dg y j t e →
      DeliverSeq proposer tr dg io hs y t os
        (j + (Node.exec proposer dg y (tr.state y j) t e).2.length) j' →
      DeliverSeq proposer tr dg io hs y t (o :: os) j j'
  /-- A dropped object has no cut. -/
  | drop {o : Wire sp.n binding} {os : List (Wire sp.n binding)}
      {j j' : Nat} : canonEvent sp ro io hs o = none →
      DeliverSeq proposer tr dg io hs y t os j j' →
      DeliverSeq proposer tr dg io hs y t (o :: os) j j'
  /-- A canonical object whose handler makes no cut (a future-slot block) is not an event of the
  run (`GroupAt` needs a cut), so it has no cut either. -/
  | noCut {o : Wire sp.n binding} {os : List (Wire sp.n binding)} {j j' : Nat}
      (e : Node.Event (goldilocksNode sp ro)) : canonEvent sp ro io hs o = some e →
      (Node.exec proposer dg y (tr.state y j) t e).2 = [] →
      DeliverSeq proposer tr dg io hs y t os j j' →
      DeliverSeq proposer tr dg io hs y t (o :: os) j j'

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

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
def ReleasedFrom (v : V) (o : (Model.protoOf (compiled (goldilocks S)) E).Object) (τ : Time) :
    Prop :=
  rho.releases v o τ

/-- The object `o` admitted by node `v` at `τ` is relayed, as a carried object of an unsigned
relay wrapper, at that same time `τ`, including an admission at the horizon. -/
def RelayedFrom (v : V) (o : (Model.protoOf (compiled (goldilocks S)) E).Object) (τ : Time) :
    Prop :=
  ∃ cs, o ∈ cs ∧ rho.releases v (.mk .none (.data .relay) cs) τ

variable (V) in
/-- **Reads are the shape's outputs.** The chain trace of a run reads, at every cut, the output
chains of the node state at the shape's clock. -/
def ReadIsOut : Prop :=
  ∀ (E : Env V) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V),
    ∀ (g : Out) (v : V) (i : Nat),
      (chainTrace rho).read g v i = outOf (stateAt S rho hn v i).node (stateAt S rho hn v i).now g

/-- Every observed item's tagged node root differs from genesis. The raw engine
hash remains arbitrary, including hashes equal to the numeric genesis root. -/
def GenesisFresh : Prop :=
  ∀ x, rho.ObservedItem x → taggedRoot S.genesisRoot (rho.hash x) ≠ S.genesisRoot

/-- **G1.5 (a), `conflicts` is E1/E2.** The instance's slashing rule holds of two objects exactly
when they are the canonical objects of two `slashable` attestations, at every vote binding. -/
def ConflictsIff : Prop :=
  ∀ (B : VoteBinding) (n : Nat) (o o' : Wire n B),
    conflicts o o' = true ↔ ∃ a b : FG.Att n, o = attObj a ∧ o' = attObj b ∧ FG.slashable a b

/-- The initial shape clock. -/
theorem lastClock_zero (v : V) : lastClock S rho v 0 = 0 := by rfl

/-- Only a tick or restart of this node changes its clock. -/
theorem lastClock_succ (v : V) (i : Nat) : lastClock S rho v (i + 1) =
    match rho.events[i]? with
    | some (.tick v' t) => if v' = v then t else lastClock S rho v i
    | some (.restart v' t) => if v' = v then t else lastClock S rho v i
    | _ => lastClock S rho v i := by rfl

/-- Release means an engine release at the stated time. -/
theorem releasedFrom_iff (v : V) (o : (Model.protoOf (compiled (goldilocks S)) E).Object)
    (τ : Time) : ReleasedFrom S rho v o τ ↔ rho.releases v o τ := by rfl

/-- Relay means carrying the object in an unsigned relay released at the stated time. -/
theorem relayedFrom_iff (v : V) (o : (Model.protoOf (compiled (goldilocks S)) E).Object)
    (τ : Time) : RelayedFrom S rho v o τ ↔
      ∃ cs, o ∈ cs ∧ rho.releases v (.mk .none (.data .relay) cs) τ := by rfl

variable (V) in
/-- Engine reads are exactly the embedded node's outputs. -/
theorem readIsOut_iff : ReadIsOut V S ↔
    ∀ (E : Env V) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V),
      ∀ (g : Out) (v : V) (i : Nat),
        (chainTrace rho).read g v i =
          outOf (stateAt S rho hn v i).node (stateAt S rho hn v i).now g := by rfl

/-- Conflicts are exactly canonical slashable attestation pairs. -/
theorem conflictsIff_iff : ConflictsIff ↔
    ∀ (B : VoteBinding) (n : Nat) (o o' : Wire n B),
      conflicts o o' = true ↔
        ∃ a b : FG.Att n, o = attObj a ∧ o' = attObj b ∧ FG.slashable a b := by
  rfl

end Consensus.Goldilocks.Simulation

end
