module
public import ConsensusLean.Spec.Shape.Run
public import ConsensusLean.Instances.Goldilocks.AsChainShape
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Results.Spec.NodeCanonicalTrace

public section

/-! # Canonical engine-to-node trace construction

The definitions of the canonical trace of an engine run, with the lemmas that characterise their
bodies: the vocabulary in which results over the engine are stated
(`Results/Statements/SleepyGrowth`). The trace is `simTrace`, with its growing-fault reading
`simTraceAt`; the honest keys are `honestKeys` and `honestKeysAt`; the node digest is `digestOf`;
the run's proposer is `runProposer`. This module is untrusted statement vocabulary of the results
home, outside the trusted surface and `Challenge`. Its bodies are not exposed: each is described by
its characterising lemma here (`*_eq`, `*_iff`, `*_nil`, `*_cons`, `simTrace_*`). Derived facts are
in `Lemmas/Simulation/TraceDefs` and `Lemmas/Growing/Simulation/Defs`, which re-export this module,
and further proofs in `Lemmas/Simulation/Trace`. Collision transport refers to this trace, not an
arbitrary trace satisfying simulation laws.

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
  (`awakeAt`).
* Under growing faults the honest keys are read at the observation time, clamped to the horizon
  (`honestKeysAt`), on the same trace (`simTraceAt`). -/

namespace Consensus.Goldilocks

open Blocks

namespace Simulation
open AsChainShape

open Shape Node
open Consensus.Goldilocks.NodeAsChainShape hiding parentRef taggedRoot
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload)

section
variable {V : Type} [Fintype V] {E : Env V}

/-- The concrete publication envelope and codec used by the compiled Goldilocks family. -/
noncomputable def traceEncoding (S : Setup) (hn : 1 ≤ Fintype.card V) :
    NodeAsChainShape.CanonicalTrace.Encoding (goldilocks S) E (S.params (pubOf E) hn).toParams
      rfl hn (goldilocksNode (S.params (pubOf E) hn) (S.ro _)) where
  skel := skeleton (pubOf E) S.vote
  Body := Body
  decBody := inferInstance
  State h := State (S.params (pubOf E) h) (S.ro _) S.vote
  codec := wireCodec _ _ S.vote
  adapter := nodeAdapter _ _ S.vote
  ops h := nodeOps (S.params (pubOf E) h) (S.ro _) S.vote
  role := S.vote.candidateRole _
  dep := dependencies _ (binding := S.vote)
  conflict := conflicts (binding := S.vote)
  isFGAtt := isFGAtt (binding := S.vote)
  shape_eq := rfl

/-- The proof-side observer reads the Goldilocks envelope's FG-due flag, not a replay input. -/
noncomputable def traceDue (S : Setup) (hn : 1 ≤ Fintype.card V) :
    (traceEncoding (E := E) S hn).State hn → Bool := by
  unfold traceEncoding
  exact State.fgDue

end

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

/-- Prove a property of the encoding and its dependent observer at their concrete assembly.
The digest equation identifies the generic digest with Goldilocks' own digest. -/
theorem traceEncoding_induction {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (hn : 1 ≤ Fintype.card V)
    (P : (e : CanonicalTrace.Encoding (goldilocks S) E (S.params (pubOf E) hn).toParams
      rfl hn (goldilocksNode (S.params (pubOf E) hn) (S.ro _))) → (e.State hn → Bool) → Prop)
    (h : let e : CanonicalTrace.Encoding (goldilocks S) E (S.params (pubOf E) hn).toParams
            rfl hn (goldilocksNode (S.params (pubOf E) hn) (S.ro _)) :=
           { skel := skeleton (pubOf E) S.vote
             Body := Body
             decBody := inferInstance
             State h := State (S.params (pubOf E) h) (S.ro _) S.vote
             codec := wireCodec _ _ S.vote
             adapter := nodeAdapter _ _ S.vote
             ops h := nodeOps (S.params (pubOf E) h) (S.ro _) S.vote
             role := S.vote.candidateRole _
             dep := dependencies _ (binding := S.vote)
             conflict := conflicts (binding := S.vote)
             isFGAtt := isFGAtt (binding := S.vote)
             shape_eq := rfl }
         (∀ rho : Model.Run (compiled (goldilocks S)) E,
           CanonicalTrace.digestOf e rho = dgOf rho.hash S.genesisRoot) →
         P e State.fgDue) : P (traceEncoding S hn) (traceDue S hn) := by
  apply h
  intro rho
  funext par s x atts pl
  exact (CanonicalTrace.digestOf_eq (traceEncoding S hn) rho par s x atts pl).trans
    (dgOf_eq _ _ _ _ _ _ _).symm

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- The honest keys of the engine run. -/
def honestKeys : Set (Fin (Fintype.card V)) := CanonicalTrace.honestKeys rho

/-- The tagged node digest induced by the engine hash. -/
noncomputable def digestOf :
    Digest (List (FG.Att (Fintype.card V))) (Payload (Fintype.card V)) :=
  dgOf rho.hash S.genesisRoot

/-- The selected proposer, totalized for invalid selections. -/
noncomputable def runProposer (s : Nat) : Fin (Fintype.card V) :=
  CanonicalTrace.runProposer rho hn s

/-- The node state held by the shape before an engine cut. -/
noncomputable def stateAt (v : V) (i : Nat) :
    State (S.params (pubOf E) hn) (S.ro _) S.vote :=
  CanonicalTrace.stateAt (traceEncoding S hn) rho v i

omit [DecidableEq V] in
/-- Honest trace keys are exactly the keys of honest engine nodes. -/
theorem mem_honestKeys_iff (y : Fin (Fintype.card V)) :
    y ∈ honestKeys S rho ↔ rho.key y ∉ rho.faultyAt 0 :=
  CanonicalTrace.mem_honestKeys_iff rho y

omit [DecidableEq V] in
/-- The trace uses the shape's tagged digest. -/
theorem digestOf_eq : digestOf S rho = dgOf rho.hash S.genesisRoot := by rfl

omit [DecidableEq V] in
/-- The trace uses the least selected proposer, defaulting to key zero. -/
theorem runProposer_eq (s : Nat) : runProposer S rho hn s =
    if h : (rho.sel (.proposer s)).Nonempty then (rho.sel (.proposer s)).min' h
    else ⟨0, hn⟩ := CanonicalTrace.runProposer_eq rho s

/-- The state embedded by the engine before a cut. -/
theorem stateAt_eq (v : V) (i : Nat) :
    stateAt S rho hn v i = (rho.stateBefore i v).st.1 hn :=
  CanonicalTrace.stateAt_eq (traceEncoding S hn) rho v i

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {binding : VoteBinding}

/-- A trace cut: its node, time, event id, position in the event, label and post-state. -/
structure CutRec (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n))) where
  node : Fin sp.n
  time : Time
  event : Nat
  pos : Nat
  label : Cut (goldilocksNode sp ro)
  post : NodeState (goldilocksNode sp ro)

private def goldilocksCut (r : NodeAsChainShape.CanonicalTrace.CutRec (goldilocksNode sp ro)) :
    CutRec sp ro :=
  ⟨r.node, r.time, r.event, r.pos, r.label, r.post⟩

/-- The cuts of one handler group: the cuts of `Node.exec` at `(st, t, e)` with their
post-states, under event id `id`. -/
noncomputable def groupRecs (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp ro)) (t : Time) (id : Nat)
    (e : Event (goldilocksNode sp ro)) : List (CutRec sp ro) :=
  (NodeAsChainShape.CanonicalTrace.groupRecs proposer dg self st t id e).map goldilocksCut

/-- The handler's cuts zipped with their post-states, indexed by position. -/
theorem groupRecs_eq (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp ro)) (t : Time) (id : Nat)
    (e : Event (goldilocksNode sp ro)) :
    groupRecs proposer dg self st t id e =
      ((exec proposer dg self st t e).2.zip
        (cutPosts self t (exec proposer dg self st t e).2 st)).mapIdx
        fun k cp => ⟨self, t, id, k, cp.1, cp.2⟩ := by
  unfold groupRecs
  rw [NodeAsChainShape.CanonicalTrace.groupRecs_eq]
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_map, List.getElem?_mapIdx, Option.map_map]
  rfl

/-- The groups of a delivery: one group per canonical object it carries, the node state threaded
through the handlers, each under its own event id `Nat.pair i sub`; a dropped object contributes
nothing. -/
noncomputable def deliverRecs (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat) :
    List (Wire sp.n binding) → NodeState (goldilocksNode sp ro) →
      Nat → List (CutRec sp ro) := fun os st sub =>
  (NodeAsChainShape.CanonicalTrace.deliverRecs (wireCodec sp ro binding) proposer dg hs self t i
    os st sub).map goldilocksCut

/-- `deliverRecs` of no object. -/
theorem deliverRecs_nil (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat)
    (st : NodeState (goldilocksNode sp ro)) (sub : Nat) :
    deliverRecs (binding := binding) proposer dg hs self t i [] st sub = [] := by
  unfold deliverRecs
  rw [NodeAsChainShape.CanonicalTrace.deliverRecs_nil, List.map_nil]

/-- Receipt of an object, followed by the rest of the delivery. -/
theorem deliverRecs_cons (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat) (o : Wire sp.n binding)
    (os : List (Wire sp.n binding)) (st : NodeState (goldilocksNode sp ro)) (sub : Nat) :
    deliverRecs proposer dg hs self t i (o :: os) st sub =
      match canonEvent sp ro hs o with
      | some e => groupRecs proposer dg self st t (Nat.pair i sub) e ++
          deliverRecs proposer dg hs self t i os (exec proposer dg self st t e).1 (sub + 1)
      | none => deliverRecs proposer dg hs self t i os st (sub + 1) := by
  unfold deliverRecs
  rw [NodeAsChainShape.CanonicalTrace.deliverRecs_cons]
  have h : NodeAsChainShape.canonEvent (wireCodec sp ro binding) hs o = canonEvent sp ro hs o :=
    rfl
  rw [h]
  cases canonEvent sp ro hs o with
  | none => rfl
  | some e => rw [List.map_append]; rfl

open Classical in
/-- The trace cuts of engine event `i`: the node's group for a tick at a public time (none at a
non-public time), the groups of a delivery's canonical objects (`deliverRecs`), the restart group
for a restart. -/
noncomputable def eventCuts (i : Nat) : List (CutRec (S.params (pubOf E) hn) (S.ro _)) :=
  (CanonicalTrace.eventCuts (traceEncoding S hn) rho i).map goldilocksCut

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
          (delivered (Model.digests rho.hash o) (stateAt S rho hn v i) o)
            (stateAt S rho hn v i).node 0
    | some (.restart v t) =>
        groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
          (stateAt S rho hn v i).node t (Nat.pair i 0) .restart
    | none => [] := by
  unfold eventCuts
  cases he : rho.events[i]? with
  | none => rw [CanonicalTrace.eventCuts_none _ _ _ he]; rfl
  | some ev =>
    have hd : CanonicalTrace.digestOf (traceEncoding S hn) rho = digestOf S rho := by
      funext par slot x atts p
      rw [CanonicalTrace.digestOf_eq]
      rfl
    cases ev with
    | tick v t =>
      rw [CanonicalTrace.eventCuts_tick _ _ _ _ _ he]
      dsimp only
      by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
      · simp only [ite_eq_left hp, hd]; rfl
      · simp only [ite_eq_right hp, List.map_nil]
    | restart v t => rw [CanonicalTrace.eventCuts_restart _ _ _ _ _ he, hd]; rfl
    | deliver v o t =>
      rw [CanonicalTrace.eventCuts_deliver _ _ _ _ _ _ he]
      simp only [hd, CanonicalTrace.wireOf_eq]
      rfl

/-- The cut map `ι`: the number of trace cuts of the engine events before engine cut `i`. -/
noncomputable def cutMap : Nat → Nat := CanonicalTrace.cutMap (traceEncoding S hn) rho

/-- The cut map starts at zero. -/
theorem cutMap_zero : cutMap S rho hn 0 = 0 := CanonicalTrace.cutMap_zero _ _

/-- The cut map steps by the number of cuts of the event. -/
theorem cutMap_succ (i : Nat) :
    cutMap S rho hn (i + 1) = cutMap S rho hn i + (eventCuts S rho hn i).length := by
  unfold cutMap eventCuts
  rw [CanonicalTrace.cutMap_succ, List.length_map]

/-- Every trace cut, in engine event order. -/
noncomputable def allCuts : List (CutRec (S.params (pubOf E) hn) (S.ro _)) :=
  (CanonicalTrace.allCuts (traceEncoding S hn) rho).map goldilocksCut

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
noncomputable def simTrace : GoldilocksTrace (S.params (pubOf E) hn) (S.ro _) :=
  CanonicalTrace.simTrace (traceEncoding S hn) rho

/-- Goldilocks replay specializes the canonical encoded-node trace and its cut map. -/
theorem simTrace_encoding :
    simTrace S rho hn = CanonicalTrace.simTrace (traceEncoding S hn) rho ∧
    cutMap S rho hn = CanonicalTrace.cutMap (traceEncoding S hn) rho := ⟨by rfl, by rfl⟩

/-- The cuts of the events in order. -/
theorem allCuts_eq :
    allCuts S rho hn = (List.range rho.events.length).flatMap (eventCuts S rho hn) := by
  unfold allCuts eventCuts
  rw [CanonicalTrace.allCuts_eq, List.map_flatMap]

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
  unfold simTrace
  simp only [CanonicalTrace.simTrace_init_eq, CanonicalTrace.engineRole_eq]
  rfl

/-- The node of a trace cut. -/
theorem simTrace_node (k : Nat) :
    (simTrace S rho hn).node k = ((allCuts S rho hn)[k]?).elim ⟨0, hn⟩ CutRec.node := by
  rw [simTrace, CanonicalTrace.simTrace_node, allCuts, List.getElem?_map]
  cases (CanonicalTrace.allCuts (traceEncoding S hn) rho)[k]? <;> rfl

/-- The time of a trace cut. -/
theorem simTrace_time (k : Nat) :
    (simTrace S rho hn).time k =
      ((allCuts S rho hn)[k]?).elim (rho.horizon + 1) CutRec.time := by
  rw [simTrace, CanonicalTrace.simTrace_time, allCuts, List.getElem?_map]
  cases (CanonicalTrace.allCuts (traceEncoding S hn) rho)[k]? <;> rfl

/-- The event id of a trace cut. -/
theorem simTrace_event (k : Nat) :
    (simTrace S rho hn).event k =
      ((allCuts S rho hn)[k]?).elim (Nat.pair rho.events.length k) CutRec.event := by
  rw [simTrace, CanonicalTrace.simTrace_event, allCuts, List.getElem?_map]
  cases (CanonicalTrace.allCuts (traceEncoding S hn) rho)[k]? <;> rfl

/-- The position of a trace cut. -/
theorem simTrace_pos (k : Nat) :
    (simTrace S rho hn).pos k = ((allCuts S rho hn)[k]?).elim 0 CutRec.pos := by
  rw [simTrace, CanonicalTrace.simTrace_pos, allCuts, List.getElem?_map]
  cases (CanonicalTrace.allCuts (traceEncoding S hn) rho)[k]? <;> rfl

/-- The label of a trace cut. -/
theorem simTrace_label (k : Nat) :
    (simTrace S rho hn).label k = ((allCuts S rho hn)[k]?).map CutRec.label := by
  rw [simTrace, CanonicalTrace.simTrace_label, allCuts, List.getElem?_map]
  cases (CanonicalTrace.allCuts (traceEncoding S hn) rho)[k]? <;> rfl

/-- The post-state of a trace cut. -/
theorem simTrace_post (k : Nat) :
    (simTrace S rho hn).post k = ((allCuts S rho hn)[k]?).elim (Node.init _) CutRec.post := by
  rw [simTrace, CanonicalTrace.simTrace_post, allCuts, List.getElem?_map]
  cases (CanonicalTrace.allCuts (traceEncoding S hn) rho)[k]? <;> rfl

/-- Awake agrees with the clamped environment predicate. -/
theorem simTrace_awake_iff (y : Fin (Fintype.card V)) (t : Time) :
    (simTrace S rho hn).awake y t ↔ awakeAt S rho hn y t :=
  CanonicalTrace.simTrace_awake_iff _ _ _ _

/-- The canonical trace records the engine's observation horizon. -/
theorem simTrace_observationHorizon :
    (simTrace S rho hn).observationHorizon = some rho.horizon :=
  CanonicalTrace.simTrace_observationHorizon _ _

end Simulation

namespace Simulation
open AsChainShape

open Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E)

/-- Keys uncompromised at `t`, with observations beyond the horizon clamped to it. -/
def honestKeysAt (t : Time) : Set (Fin (Fintype.card V)) :=
  NodeAsChainShape.CanonicalTrace.honestKeysAt rho t

omit [DecidableEq V] in
/-- Membership reads the engine's faulty set at the clamped observation time. -/
theorem mem_honestKeysAt_iff (t : Time) (y : Fin (Fintype.card V)) :
    y ∈ honestKeysAt S rho t ↔ rho.key y ∉ rho.faultyAt (min t rho.horizon) := by
  exact NodeAsChainShape.CanonicalTrace.mem_honestKeysAt_iff rho t y

/-- Growing simulation uses the same event expansion as static simulation. -/
noncomputable def simTraceAt (hn : 1 ≤ Fintype.card V) :
    GoldilocksTrace (S.params (pubOf E) hn) (S.ro _) := simTrace S rho hn

/-- The growing trace is the canonical engine trace, not a choice of simulation witness. -/
theorem simTraceAt_eq (hn : 1 ≤ Fintype.card V) :
    simTraceAt S rho hn = simTrace S rho hn := by rfl

end Simulation

end Consensus.Goldilocks
