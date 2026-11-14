module
public import ConsensusLean.Spec.Shape.Run
public import ConsensusLean.Instances.Goldilocks.AsChainShape
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Goldilocks

public section

/-! # Canonical engine-to-node trace construction

Collision transport refers to this trace, not an arbitrary trace satisfying simulation laws.
The construction is proof-side vocabulary, outside the trusted surface and `Challenge`;
its non-exposed bodies are described by characterising lemmas. Further proofs are in
`Lemmas/Simulation/Trace`.

The trace is **built from the engine run**, not chosen: every engine event of an honest node is
replayed through the node's handler (`Node.exec`) on the node state the engine holds before the
event, and the handler's cuts, with their post-states (`cutPost`, the unique successor of the cut
law), become the trace's cuts. The cut map `ι` (`cutMap`) counts the cuts of the events before an
engine cut.

* A tick at a public time is the node's tick with the engine's input (the encoded mempool), a
  tick at a non-public time contributes no cut (`eventCuts`).
* A delivery is one group per canonical object it carries (`deliverRecs`), with the node state
  threaded through the handlers; a dropped object, or a canonical object whose handler makes no
  cut, contributes nothing. The sub-event index gives each group its own event id (`Nat.pair`).
* A restart is the restart group.
* After the last engine cut the trace stutters: unlabelled cuts at `horizon + 1`, each under its
  own event id (`cutTime`, `simTrace`).
* The trace's awake function is the environment's, clamped to `[0, ∞)` and to the trace's horizon
  (`awakeAt`). -/

namespace Consensus.Goldilocks

open Blocks

namespace Node

variable {P : Params} {A : NodeAC P}

/-- The post-state of a cut: the unique successor of the cut law (`Node.CutStep`). -/
noncomputable def cutPost (self : Fin P.n) (t : Time) (st : NodeState A) : Cut A → NodeState A
  | .ac ℓ => { st with ac := (A.step self st.ac ℓ.frame t ℓ.call).1 }
  | .fg (.block B true) => { st with fg := (st.fg.onBlock B).getD st.fg }
  | .fg (.block _ false) => st
  | .fg (.attestation a) => { st with fg := st.fg.onAttestation a }
  | .fg (.attest _ none) => st
  | .fg (.attest C (some _)) =>
      { st with record := ((st.fg.attest st.record self C).map Prod.snd).getD st.record }

/-- The post-states of a list of cuts, each from the previous one's post-state. -/
noncomputable def cutPosts (self : Fin P.n) (t : Time) :
    List (Cut A) → NodeState A → List (NodeState A)
  | [], _ => []
  | c :: cs, st => cutPost self t st c :: cutPosts self t cs (cutPost self t st c)

/-- The cut successor, by the kind of handler cut. -/
theorem cutPost_eq (self : Fin P.n) (t : Time) (st : NodeState A) (c : Cut A) :
    cutPost self t st c = match c with
      | .ac ℓ => { st with ac := (A.step self st.ac ℓ.frame t ℓ.call).1 }
      | .fg (.block B true) => { st with fg := (st.fg.onBlock B).getD st.fg }
      | .fg (.block _ false) => st
      | .fg (.attestation a) => { st with fg := st.fg.onAttestation a }
      | .fg (.attest _ none) => st
      | .fg (.attest C (some _)) =>
          { st with record := ((st.fg.attest st.record self C).map Prod.snd).getD st.record } := by
  rfl

/-- `cutPosts` of no cut. -/
theorem cutPosts_nil (self : Fin P.n) (t : Time) (st : NodeState A) :
    cutPosts self t [] st = [] := by rfl

/-- `cutPosts` of a cut and more: its post-state, then the rest from there. -/
theorem cutPosts_cons (self : Fin P.n) (t : Time) (c : Cut A) (cs : List (Cut A))
    (st : NodeState A) :
    cutPosts self t (c :: cs) st =
      cutPost self t st c :: cutPosts self t cs (cutPost self t st c) := by rfl

end Node

namespace Simulation
open AsChainShape

open Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload)

/-- The SA parameters of a bound setup at `pub`: the setup's parameters at its own vote binding
(the parameters of `goldilocksWith S`). -/
abbrev _root_.Consensus.Goldilocks.AsChainShape.BoundSetup.params (S : BoundSetup)
    (pub : Model.Public) (hn : 1 ≤ pub.n) : SAParams :=
  S.toSetup.params pub hn (binding := S.vote)

/-- A bound setup's committee is nonempty at every population with a validator: the population
binding's committee is the population, a committee binding's by `VoteBinding.committeeSize_pos`. -/
theorem _root_.Consensus.Goldilocks.AsChainShape.BoundSetup.committeeSize_pos (S : BoundSetup)
    (pub : Model.Public) (hn : 1 ≤ pub.n) : 0 < (S.params pub hn).committeeSize := by
  change 0 < S.vote.committeeSize pub
  unfold VoteBinding.committeeSize
  split
  · exact hn
  · rename_i k _
    have h := S.vote.committeeSize_pos pub k hn
    split
    · rename_i m hm
      rw [hm] at h
      exact lt_min h hn
    · rename_i keys hk
      rw [hk] at h
      exact Finset.card_pos.mpr h

/-- The node's digest from the engine's hash with genesis root `g`: genesis (no parent) has
root `g`; any other block's root is the tagged hash of its header (`parentRef` for the parent). -/
def dgOf {n : Nat} (hash : Header Info → Nat) (g : Nat) : Digest (List (FG.Att n)) (Payload n) :=
  fun par slot x atts p =>
    match par with
    | none => g
    | some r => taggedRoot g (hash ⟨parentRef g (some r), slot, x, encodeInfo atts p⟩)

/-- The node digest is genesis, or the tagged hash of its encoded header. -/
theorem dgOf_eq {n : Nat} (hash : Header Info → Nat) (g : Nat) (par : Option Nat)
    (slot x : Nat) (atts : List (FG.Att n)) (p : Payload n) :
    dgOf hash g par slot x atts p =
      match par with
      | none => g
      | some r => taggedRoot g (hash ⟨parentRef g (some r), slot, x, encodeInfo atts p⟩) := by
  rfl

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- The honest keys of the engine run. -/
def honestKeys : Set (Fin (Fintype.card V)) := {k | rho.key k ∉ rho.faultyAt 0}

/-- The tagged node digest induced by the engine hash. -/
noncomputable def digestOf :
    Digest (List (FG.Att (Fintype.card V))) (Payload (Fintype.card V)) :=
  dgOf rho.hash S.genesisRoot

/-- The selected proposer, totalized for invalid selections. -/
noncomputable def runProposer (s : Nat) : Fin (Fintype.card V) :=
  if h : (rho.sel (.proposer s)).Nonempty then (rho.sel (.proposer s)).min' h
  else ⟨0, hn⟩

/-- The node state held by the shape before an engine cut. -/
noncomputable def stateAt (v : V) (i : Nat) :
    State (S.params (pubOf E) hn) (S.ro _) S.vote :=
  (rho.stateBefore i v).st.1 hn

omit [DecidableEq V] in
/-- Honest trace keys are exactly the keys of honest engine nodes. -/
theorem mem_honestKeys_iff (y : Fin (Fintype.card V)) :
    y ∈ honestKeys S rho ↔ rho.key y ∉ rho.faultyAt 0 := by rfl

omit [DecidableEq V] in
/-- The trace uses the shape's tagged digest. -/
theorem digestOf_eq : digestOf S rho = dgOf rho.hash S.genesisRoot := by rfl

omit [DecidableEq V] in
/-- The trace uses the least selected proposer, defaulting to key zero. -/
theorem runProposer_eq (s : Nat) : runProposer S rho hn s =
    if h : (rho.sel (.proposer s)).Nonempty then (rho.sel (.proposer s)).min' h
    else ⟨0, hn⟩ := by rfl

/-- The state embedded by the engine before a cut. -/
theorem stateAt_eq (v : V) (i : Nat) :
    stateAt S rho hn v i = (rho.stateBefore i v).st.1 hn := by rfl

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {binding : VoteBinding}

/-- A trace cut: its node, time, event id, position in the event, label and post-state. -/
structure CutRec (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n))) where
  node : Fin sp.n
  time : Time
  event : Nat
  pos : Nat
  label : Cut (goldilocksNode sp ro)
  post : NodeState (goldilocksNode sp ro)

/-- The cuts of one handler group: the cuts of `Node.exec` at `(st, t, e)` with their
post-states, under event id `id`. -/
noncomputable def groupRecs (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp ro)) (t : Time) (id : Nat)
    (e : Event (goldilocksNode sp ro)) : List (CutRec sp ro) :=
  let cs := (exec proposer dg self st t e).2
  (cs.zip (cutPosts self t cs st)).mapIdx fun k cp => ⟨self, t, id, k, cp.1, cp.2⟩

/-- The handler's cuts zipped with their post-states, indexed by position. -/
theorem groupRecs_eq (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp ro)) (t : Time) (id : Nat)
    (e : Event (goldilocksNode sp ro)) :
    groupRecs proposer dg self st t id e =
      ((exec proposer dg self st t e).2.zip
        (cutPosts self t (exec proposer dg self st t e).2 st)).mapIdx
        fun k cp => ⟨self, t, id, k, cp.1, cp.2⟩ := by rfl

/-- The groups of a delivery: one group per canonical object it carries, the node state threaded
through the handlers, each under its own event id `Nat.pair i sub`; a dropped object contributes
nothing. -/
noncomputable def deliverRecs (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat) :
    List (Wire sp.n binding) → NodeState (goldilocksNode sp ro) →
      Nat → List (CutRec sp ro)
  | [], _, _ => []
  | o :: os, st, sub =>
      match canonEvent sp ro (binding := binding) hs o with
      | some e =>
          groupRecs proposer dg self st t (Nat.pair i sub) e ++
            deliverRecs proposer dg hs self t i os (exec proposer dg self st t e).1 (sub + 1)
      | none => deliverRecs proposer dg hs self t i os st (sub + 1)

/-- `deliverRecs` of no object. -/
theorem deliverRecs_nil (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat)
    (st : NodeState (goldilocksNode sp ro)) (sub : Nat) :
    deliverRecs (binding := binding) proposer dg hs self t i [] st sub = [] := by rfl

/-- Receipt of an object, followed by the rest of the delivery. -/
theorem deliverRecs_cons (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat) (o : Wire sp.n binding)
    (os : List (Wire sp.n binding)) (st : NodeState (goldilocksNode sp ro)) (sub : Nat) :
    deliverRecs proposer dg hs self t i (o :: os) st sub =
      match canonEvent sp ro hs o with
      | some e => groupRecs proposer dg self st t (Nat.pair i sub) e ++
          deliverRecs proposer dg hs self t i os (exec proposer dg self st t e).1 (sub + 1)
      | none => deliverRecs proposer dg hs self t i os st (sub + 1) := by rfl

/-- A canonical object contributes its group, then the rest from the handler's state. -/
theorem deliverRecs_cons_some (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat) (o : Wire sp.n binding)
    (os : List (Wire sp.n binding)) (st : NodeState (goldilocksNode sp ro)) (sub : Nat)
    (e : Event (goldilocksNode sp ro)) (he : canonEvent sp ro hs o = some e) :
    deliverRecs proposer dg hs self t i (o :: os) st sub =
      groupRecs proposer dg self st t (Nat.pair i sub) e ++
        deliverRecs proposer dg hs self t i os (exec proposer dg self st t e).1 (sub + 1) := by
  rw [deliverRecs_cons, he]

/-- A dropped object contributes no group. -/
theorem deliverRecs_cons_none (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat) (o : Wire sp.n binding)
    (os : List (Wire sp.n binding)) (st : NodeState (goldilocksNode sp ro)) (sub : Nat)
    (he : canonEvent sp ro hs o = none) :
    deliverRecs proposer dg hs self t i (o :: os) st sub =
      deliverRecs proposer dg hs self t i os st (sub + 1) := by
  rw [deliverRecs_cons, he]

open Classical in
/-- The trace cuts of engine event `i`: the node's group for a tick at a public time (none at a
non-public time), the groups of a delivery's canonical objects (`deliverRecs`), the restart group
for a restart. -/
noncomputable def eventCuts (i : Nat) : List (CutRec (S.params (pubOf E) hn) (S.ro _)) :=
  match rho.events[i]? with
  | some (.tick v t) =>
      if (S.params (pubOf E) hn).toParams.IsPublic t then
        groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
          (stateAt S rho hn v i).node t (Nat.pair i 0)
          (.tick (encodeTxs (Model.mempool rho.inbox v t)))
      else []
  | some (.deliver v o t) =>
      deliverRecs (runProposer S rho hn) (digestOf S rho)
        (Model.digests rho.hash o) (rho.ownKey v) t i
        (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn v i).node 0
  | some (.restart v t) =>
      groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0)
        .restart
  | none => []

open Classical in
/-- Each engine event contributes exactly its handler groups. -/
theorem eventCuts_eq (i : Nat) : eventCuts S rho hn i =
    match rho.events[i]? with
    | some (.tick v t) =>
        if (S.params (pubOf E) hn).toParams.IsPublic t then
          groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
            (stateAt S rho hn v i).node t (Nat.pair i 0)
            (.tick (encodeTxs (Model.mempool rho.inbox v t)))
        else []
    | some (.deliver v o t) =>
        deliverRecs (runProposer S rho hn) (digestOf S rho)
          (Model.digests rho.hash o) (rho.ownKey v) t i
          (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn v i).node 0
    | some (.restart v t) =>
        groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
          (stateAt S rho hn v i).node t (Nat.pair i 0) .restart
    | none => [] := by rfl

/-- The cut map `ι`: the number of trace cuts of the engine events before engine cut `i`. -/
noncomputable def cutMap : Nat → Nat
  | 0 => 0
  | i + 1 => cutMap i + (eventCuts S rho hn i).length

/-- The cut map starts at zero. -/
theorem cutMap_zero : cutMap S rho hn 0 = 0 := by rfl

/-- The cut map steps by the number of cuts of the event. -/
theorem cutMap_succ (i : Nat) :
    cutMap S rho hn (i + 1) = cutMap S rho hn i + (eventCuts S rho hn i).length := by rfl

/-- Every trace cut, in engine event order. -/
noncomputable def allCuts : List (CutRec (S.params (pubOf E) hn) (S.ro _)) :=
  (List.range rho.events.length).flatMap (eventCuts S rho hn)

/-- The time of trace cut `k`; after the last cut, `horizon + 1` (the stutter). -/
noncomputable def cutTime (k : Nat) : Time :=
  ((allCuts S rho hn)[k]?).elim (rho.horizon + 1) CutRec.time

/-- The label of trace cut `k`; after the last cut, none. -/
noncomputable def cutLabel (k : Nat) :
    Option (Cut (goldilocksNode (S.params (pubOf E) hn) (S.ro _))) :=
  ((allCuts S rho hn)[k]?).map CutRec.label

/-- The trace's awake function: the environment's, clamped to `[0, horizon]`. -/
def awakeAt (_hn : 1 ≤ Fintype.card V) (y : Fin (Fintype.card V)) (t : Time) : Prop :=
  E.awake (rho.key y) t = true ∧ 0 ≤ t ∧ t ≤ rho.horizon

/-- The canonical trace of the engine run: its cuts are `allCuts`; after the last one it stutters
with unlabelled cuts at `horizon + 1`, each under its own event id (recorded post-state: the
initial node state). Each node starts from the initial node state with its own-role vote
permission installed by the binding (`goldilocksShape.init`). -/
noncomputable def simTrace : GoldilocksTrace (S.params (pubOf E) hn) (S.ro _) where
  init y := Node.initWith _ (S.vote.installVote (fun r => decide (y ∈ rho.sel r))
    (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).initial)
  node k := ((allCuts S rho hn)[k]?).elim ⟨0, hn⟩ CutRec.node
  time := cutTime S rho hn
  event k := ((allCuts S rho hn)[k]?).elim (Nat.pair rho.events.length k) CutRec.event
  pos k := ((allCuts S rho hn)[k]?).elim 0 CutRec.pos
  label := cutLabel S rho hn
  post k := ((allCuts S rho hn)[k]?).elim (Node.init _) CutRec.post
  awake := awakeAt S rho hn
  observationHorizon := some rho.horizon

/-- The cuts of an engine tick at a public time: the node's tick group. -/
theorem eventCuts_tick_public (i : Nat) (v : V) (t : Time)
    (he : rho.events[i]? = some (.tick v t)) (hp : (S.params (pubOf E) hn).toParams.IsPublic t) :
    eventCuts S rho hn i =
      groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t))) := by
  simp only [eventCuts_eq, he, hp, ↓reduceIte]

/-- An engine tick at a non-public time has no cut. -/
theorem eventCuts_tick_other (i : Nat) (v : V) (t : Time)
    (he : rho.events[i]? = some (.tick v t))
    (hp : ¬ (S.params (pubOf E) hn).toParams.IsPublic t) : eventCuts S rho hn i = [] := by
  simp only [eventCuts_eq, he, hp, ↓reduceIte]

/-- The cuts of an engine delivery. -/
theorem eventCuts_deliver (i : Nat) (v : V)
    (o : (Model.protoOf (compiled (goldilocksWith S)) E).Object)
    (t : Time) (he : rho.events[i]? = some (.deliver v o t)) :
    eventCuts S rho hn i =
      deliverRecs (runProposer S rho hn) (digestOf S rho)
        (Model.digests rho.hash o) (rho.ownKey v) t i
        (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn v i).node 0 := by
  simp only [eventCuts_eq, he]

/-- The cuts of an engine restart. -/
theorem eventCuts_restart (i : Nat) (v : V) (t : Time)
    (he : rho.events[i]? = some (.restart v t)) :
    eventCuts S rho hn i =
      groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0) .restart := by
  simp only [eventCuts_eq, he]

/-- The cuts of the events in order. -/
theorem allCuts_eq :
    allCuts S rho hn = (List.range rho.events.length).flatMap (eventCuts S rho hn) := by rfl

/-- The recorded time, or a stutter beyond the horizon. -/
theorem cutTime_eq (k : Nat) :
    cutTime S rho hn k = ((allCuts S rho hn)[k]?).elim (rho.horizon + 1) CutRec.time := by rfl

/-- The recorded label, or an unlabelled stutter. -/
theorem cutLabel_eq (k : Nat) :
    cutLabel S rho hn k = ((allCuts S rho hn)[k]?).map CutRec.label := by rfl

omit [DecidableEq V] in
/-- The environment's awake predicate clamped to the horizon. -/
theorem awakeAt_iff (y : Fin (Fintype.card V)) (t : Time) :
    awakeAt S rho hn y t ↔ E.awake (rho.key y) t = true ∧ 0 ≤ t ∧ t ≤ rho.horizon := by rfl

/-- Every trace node starts in the initial state with its own-role vote permission installed. -/
theorem simTrace_init_eq (y : Fin (Fintype.card V)) :
    (simTrace S rho hn).init y = Node.initWith (goldilocksNode (S.params (pubOf E) hn) (S.ro _))
      (S.vote.installVote (fun r => decide (y ∈ rho.sel r))
        (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).initial) := by
  rfl

/-- The node of a trace cut. -/
theorem simTrace_node (k : Nat) :
    (simTrace S rho hn).node k = ((allCuts S rho hn)[k]?).elim ⟨0, hn⟩ CutRec.node := by rfl

/-- The time of a trace cut. -/
theorem simTrace_time (k : Nat) :
    (simTrace S rho hn).time k =
      ((allCuts S rho hn)[k]?).elim (rho.horizon + 1) CutRec.time := by rfl

/-- The event id of a trace cut. -/
theorem simTrace_event (k : Nat) :
    (simTrace S rho hn).event k =
      ((allCuts S rho hn)[k]?).elim (Nat.pair rho.events.length k) CutRec.event := by rfl

/-- The position of a trace cut. -/
theorem simTrace_pos (k : Nat) :
    (simTrace S rho hn).pos k = ((allCuts S rho hn)[k]?).elim 0 CutRec.pos := by rfl

/-- The label of a trace cut. -/
theorem simTrace_label (k : Nat) :
    (simTrace S rho hn).label k = ((allCuts S rho hn)[k]?).map CutRec.label := by rfl

/-- The post-state of a trace cut. -/
theorem simTrace_post (k : Nat) :
    (simTrace S rho hn).post k = ((allCuts S rho hn)[k]?).elim (Node.init _) CutRec.post := by rfl

/-- Awake agrees with the clamped environment predicate. -/
theorem simTrace_awake_iff (y : Fin (Fintype.card V)) (t : Time) :
    (simTrace S rho hn).awake y t ↔ awakeAt S rho hn y t := by rfl

/-- The canonical trace records the engine's observation horizon. -/
theorem simTrace_observationHorizon :
    (simTrace S rho hn).observationHorizon = some rho.horizon := by rfl

end Simulation

end Consensus.Goldilocks
