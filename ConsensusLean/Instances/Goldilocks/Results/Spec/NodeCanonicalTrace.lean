module
public import ConsensusLean.Spec.Shape.Run
public import ConsensusLean.Instances.Goldilocks.NodeAsChainShape
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Model
public import Mathlib.Data.Finset.Max

public section

/-! # Canonical trace of an encoded node

Replay the events of the actual compiled run. The encoding identifies its local shape;
it does not assert agreement between the shape operations and the replayed node steps. -/

namespace Consensus.Goldilocks.Node

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

end Consensus.Goldilocks.Node

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Blocks Shape Node
open Model (pubOf)

/-- Index the node parameters by the engine's validator count. -/
abbrev paramsAtCount (p : Params) (n : Nat) (_hN : p.n = n) (hn : 1 ≤ n) : Params :=
  { p with n := n, hn := hn }

variable {V : Type} [Fintype V] {E : Env V}
variable {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
variable {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
variable {hn : 1 ≤ Fintype.card V}

/-- The codec, adapter and assembly for the family's actual shape at this environment. -/
structure Encoding (F : ChainShapeFamily O I) (E : Env V)
    (p : Params) (hN : p.n = Fintype.card V) (hn : 1 ≤ Fintype.card V)
    (A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)) where
  skel : Skeleton (pubOf E).n
  Body : Type
  decBody : DecidableEq Body
  Tok : Type
  [decTok : DecidableEq Tok]
  [infTok : Infinite Tok]
  Data : Type
  [countData : Countable Data]
  State : (1 ≤ (pubOf E).n) → Type
  codec : WireCodec A skel.Kind I Body
  decodeMessage : Model.VoteIO Tok (ShapeRole skel.Kind) Data (pubOf E).n →
    ShapeObj (pubOf E).n skel.Kind I Body → Option A.Msg
  adapter : Adapter A skel.Kind I Body (State hn)
  ops : (h : 1 ≤ (pubOf E).n) → Ops (pubOf E).n skel.Kind I Body O.Id (State h) Tok Data
  claim : Data → Option (Fin (pubOf E).n × ShapeRole skel.Kind)
  voteBody : Body → Bool
  presented : ShapeObj (pubOf E).n skel.Kind I Body →
    Option ((Fin (pubOf E).n × ShapeRole skel.Kind × Data) × Tok)
  role : ShapeDuty skel.Kind → Model.Msg (Header I) Body → Option (ShapeRole skel.Kind)
  dep : Model.DependencyPolicy (ShapeObj (pubOf E).n skel.Kind I Body)
  conflict : ShapeObj (pubOf E).n skel.Kind I Body → ShapeObj (pubOf E).n skel.Kind I Body → Bool
  isFGAtt : ShapeObj (pubOf E).n skel.Kind I Body → Prop
  shape_eq : F (pubOf E) =
    (letI : DecidableEq Body := decBody
     shape skel (familyOps ops) claim voteBody presented role dep conflict isFGAtt)

variable {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)}
variable (e : Encoding F E p hN hn A)
variable (rho : Model.Run (compiled F) E)

/-- Cast an engine object to the encoder's local wire type. -/
def wireOf (o : (Model.protoOf (compiled F) E).Object) :
    ShapeObj (paramsAtCount p (Fintype.card V) hN hn).n e.skel.Kind I e.Body :=
  cast (congrArg (fun s : ChainShape (pubOf E) O.Id I => (compile s).Object) e.shape_eq) o

/-- The wire cast is induced by the equality of the two assembled shapes. -/
theorem wireOf_eq (o : (Model.protoOf (compiled F) E).Object) : wireOf e o =
    cast (congrArg (fun s : ChainShape (pubOf E) O.Id I => (compile s).Object) e.shape_eq) o := by
  rfl

/-- Regard a local wire object as an object of the actual engine. -/
def engineObj (o : ShapeObj (paramsAtCount p (Fintype.card V) hN hn).n e.skel.Kind I e.Body) :
    (Model.protoOf (compiled F) E).Object :=
  cast (congrArg (fun s : ChainShape (pubOf E) O.Id I => (compile s).Object) e.shape_eq.symm) o

/-- The cast back to an engine object inverts the equality of assembled shapes. -/
theorem engineObj_eq
    (o : ShapeObj (paramsAtCount p (Fintype.card V) hN hn).n e.skel.Kind I e.Body) :
    engineObj e o =
      cast (congrArg (fun s : ChainShape (pubOf E) O.Id I => (compile s).Object)
        e.shape_eq.symm) o := by rfl

private theorem transportObj_symm {s s' : ChainShape (pubOf E) O.Id I} (h : s = s')
    (o : (compile s).Object) :
    cast (congrArg (fun q => (compile q).Object) h.symm)
      (cast (congrArg (fun q => (compile q).Object) h) o) = o := by
  cases h
  rfl

/-- The wire view represents the very same engine object. -/
theorem engineObj_wireOf (o : (Model.protoOf (compiled F) E).Object) :
    engineObj e (wireOf e o) = o := transportObj_symm e.shape_eq o

/-- Casting into the engine and back leaves a wire object unchanged. -/
theorem wireOf_engineObj
    (o : ShapeObj (paramsAtCount p (Fintype.card V) hN hn).n e.skel.Kind I e.Body) :
    wireOf e (engineObj e o) = o := transportObj_symm e.shape_eq.symm o

private theorem transportObj_item {s s' : ChainShape (pubOf E) O.Id I} (h : s = s')
    (o : (compile s).Object) :
    (cast (congrArg (fun q => (compile q).Object) h) o : (compile s').Object).item? = o.item? := by
  cases h
  rfl

/-- Casting an object does not change the header read by the engine. -/
theorem engineObj_item
    (o : ShapeObj (paramsAtCount p (Fintype.card V) hN hn).n e.skel.Kind I e.Body) :
    (engineObj e o).item? = o.item? := transportObj_item e.shape_eq.symm o

private theorem transportObj_parts {s s' : ChainShape (pubOf E) O.Id I} (h : s = s')
    (o : (compile s).Object) :
    (cast (congrArg (fun q => (compile q).Object) h) o : (compile s').Object).parts =
      o.parts.map (cast (congrArg (fun q => (compile q).Object) h)) := by
  cases h
  exact (List.map_id _).symm

/-- Casting preserves the ordered traversal of carried objects. -/
theorem engineObj_parts
    (o : ShapeObj (paramsAtCount p (Fintype.card V) hN hn).n e.skel.Kind I e.Body) :
    (engineObj e o).parts = o.parts.map (engineObj e) := transportObj_parts e.shape_eq.symm o

/-- Transport a role to the engine's selection type. -/
def engineRole (r : ShapeRole e.skel.Kind) : (Model.protoOf (compiled F) E).Role :=
  cast (congrArg (fun s : ChainShape (pubOf E) O.Id I => (compile s).Role) e.shape_eq.symm) r

/-- The role cast is induced by the equality of the two assembled shapes. -/
theorem engineRole_eq (r : ShapeRole e.skel.Kind) : engineRole e r =
    cast (congrArg (fun s : ChainShape (pubOf E) O.Id I => (compile s).Role) e.shape_eq.symm) r :=
  by rfl

/-- Transport the receiver's authentication operations across the equality of shapes. -/
def voteIOAt (v : V) : Model.VoteIO e.Tok (ShapeRole e.skel.Kind) e.Data (pubOf E).n :=
  cast (congrArg (fun s : ChainShape (pubOf E) O.Id I =>
    Model.VoteIO s.Token (ShapeRole s.skel.Kind) s.VoteData (pubOf E).n) e.shape_eq) (rho.voteIO v)

/-- The authentication transport is induced by the equality of the two assembled shapes. -/
theorem voteIOAt_eq (v : V) : voteIOAt e rho v =
  cast (congrArg (fun s : ChainShape (pubOf E) O.Id I =>
    Model.VoteIO s.Token (ShapeRole s.skel.Kind) s.VoteData (pubOf E).n) e.shape_eq)
    (rho.voteIO v) := by rfl

/-- Only message decoding depends on the recipient; block framing and hashing do not. -/
def receiverCodec (v : V) : WireCodec A e.skel.Kind I e.Body :=
  { e.codec with message := e.decodeMessage (voteIOAt e rho v) }

/-- Replay uses the receiver's authentication operations to decode messages. -/
theorem receiverCodec_eq (v : V) : receiverCodec e rho v =
    { e.codec with message := e.decodeMessage (voteIOAt e rho v) } := by rfl

variable [DecidableEq V]

/-- The envelope held by the engine just before the indicated cut. -/
noncomputable def stateAt (v : V) (i : Nat) : e.State hn :=
  (cast (congrArg (fun s : ChainShape (pubOf E) O.Id I => s.State) e.shape_eq)
    (rho.stateBefore i v).st.1 : ∀ h, e.State h) hn

/-- The own-role initialization of the compiled shape, projected into the node. -/
noncomputable def initial (y : Fin (Fintype.card V)) : NodeState A :=
  e.adapter.node ((e.ops hn).init y (fun r => decide (y ∈ rho.sel (engineRole e r)))
    (voteIOAt e rho (rho.key y)))

omit [DecidableEq V] in
/-- The projected trace initialization reads the actual compiled role selections. -/
theorem initial_eq (y : Fin (Fintype.card V)) : initial e rho y =
    e.adapter.node ((e.ops hn).init y (fun r => decide (y ∈ rho.sel (engineRole e r)))
      (voteIOAt e rho (rho.key y))) := by rfl

/-- The keys of validators honest at time zero. -/
def honestKeys : Set (Fin (Fintype.card V)) := {y | rho.key y ∉ rho.faultyAt 0}

/-- The keys still honest at the observation time, clamped to the horizon. -/
def honestKeysAt (t : Time) : Set (Fin (Fintype.card V)) :=
  {y | rho.key y ∉ rho.faultyAt (min t rho.horizon)}

/-- The least selected proposer, totalized for empty selections. -/
noncomputable def runProposer (hn : 1 ≤ Fintype.card V) (s : Nat) : Fin (Fintype.card V) :=
  if h : (rho.sel (.proposer s)).Nonempty then (rho.sel (.proposer s)).min' h else ⟨0, hn⟩

/-- The engine's hash, with the genesis root reserved. -/
noncomputable def digestOf :
    Digest (List (FG.Att (paramsAtCount p (Fintype.card V) hN hn).n)) A.Payload :=
  fun par s x atts payload =>
    match par with
    | none => (paramsAtCount p (Fintype.card V) hN hn).genesisRoot
    | some r => taggedRoot (paramsAtCount p (Fintype.card V) hN hn).genesisRoot
        (rho.hash ⟨parentRef (paramsAtCount p (Fintype.card V) hN hn).genesisRoot (some r),
          s, x, e.codec.encode atts payload⟩)

section Replay

variable {Q : Params} {N : NodeAC Q} {K B : Type}

/-- A cut, indexed by its position within its handler group. -/
structure CutRec (N : NodeAC Q) where
  node : Fin Q.n
  time : Time
  event : Nat
  pos : Nat
  label : Cut N
  post : NodeState N

/-- The cuts and successive post-states of one invocation of the node handler. -/
noncomputable def groupRecs (proposer : Nat → Fin Q.n)
    (dg : Digest (List (FG.Att Q.n)) N.Payload) (self : Fin Q.n)
    (st : NodeState N) (t : Time) (id : Nat) (ev : Node.Event N) : List (CutRec N) :=
  let cs := (exec proposer dg self st t ev).2
  (cs.zip (cutPosts self t cs st)).mapIdx fun k cp => ⟨self, t, id, k, cp.1, cp.2⟩

/-- Each handler cut is paired with its successor and position in the group. -/
theorem groupRecs_eq (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (self : Fin Q.n) (st : NodeState N) (t : Time) (id : Nat) (ev : Node.Event N) :
    groupRecs pr dg self st t id ev =
      let cs := (exec pr dg self st t ev).2
      (cs.zip (cutPosts self t cs st)).mapIdx fun k cp => ⟨self, t, id, k, cp.1, cp.2⟩ := by
  rfl

/-- Replay delivered objects in order, advancing the group index even for a dropped object. -/
noncomputable def deliverRecs (C : WireCodec N K I B) (proposer : Nat → Fin Q.n)
    (dg : Digest (List (FG.Att Q.n)) N.Payload) (hs : List (Header I × Nat))
    (self : Fin Q.n) (t : Time) (i : Nat) :
    List (ShapeObj Q.n K I B) → NodeState N → Nat → List (CutRec N)
  | [], _, _ => []
  | o :: os, st, sub =>
    match canonEvent C hs o with
    | some ev => groupRecs proposer dg self st t (Nat.pair i sub) ev ++
        deliverRecs C proposer dg hs self t i os (exec proposer dg self st t ev).1 (sub + 1)
    | none => deliverRecs C proposer dg hs self t i os st (sub + 1)

omit [Countable I] in
/-- No delivered objects produce no replay cuts. -/
theorem deliverRecs_nil (C : WireCodec N K I B) (pr : Nat → Fin Q.n)
    (dg : Digest (List (FG.Att Q.n)) N.Payload) (hs : List (Header I × Nat))
    (self : Fin Q.n) (t : Time) (i : Nat) (st : NodeState N) (sub : Nat) :
    deliverRecs C pr dg hs self t i [] st sub = [] := by rfl

omit [Countable I] in
/-- A delivery contributes the first object's handler group, if any, then the rest. -/
theorem deliverRecs_cons (C : WireCodec N K I B) (pr : Nat → Fin Q.n)
    (dg : Digest (List (FG.Att Q.n)) N.Payload) (hs : List (Header I × Nat))
    (self : Fin Q.n) (t : Time) (i : Nat) (o : ShapeObj Q.n K I B)
    (os : List (ShapeObj Q.n K I B)) (st : NodeState N) (sub : Nat) :
    deliverRecs C pr dg hs self t i (o :: os) st sub =
      match canonEvent C hs o with
      | some ev => groupRecs pr dg self st t (Nat.pair i sub) ev ++
          deliverRecs C pr dg hs self t i os (exec pr dg self st t ev).1 (sub + 1)
      | none => deliverRecs C pr dg hs self t i os st (sub + 1) := by rfl

end Replay

/-- The own attestations the engine admits to the node's pool during engine event `i` of `v`:
the pool after the event beyond the pool before it (the pool only grows, by appending). For a
tick these are the attestation the tick signs, when the release schedule allows its release at
once, and the held attestations a poll of the tick flushes; the replay processes each as its own
`.attestation` group after the tick's group (`eventCutsWith`). -/
noncomputable def admitsAt (v : V) (i : Nat) :
    List (FG.Att (paramsAtCount p (Fintype.card V) hN hn).n) :=
  (e.adapter.node (stateAt e rho v (i + 1))).fg.atts.drop
    (e.adapter.node (stateAt e rho v i)).fg.atts.length

/-- The own admissions of an event are the pool's growth across it. -/
theorem admitsAt_eq (v : V) (i : Nat) : admitsAt e rho v i =
    (e.adapter.node (stateAt e rho v (i + 1))).fg.atts.drop
      (e.adapter.node (stateAt e rho v i)).fg.atts.length := by rfl

section Admits

variable {Q : Params} {N : NodeAC Q}

/-- The replay of own admissions: one `.attestation` group per admitted attestation, in order,
with the group indices `Nat.pair i sub`, `Nat.pair i (sub + 1)`, …. -/
noncomputable def admitRecs (proposer : Nat → Fin Q.n)
    (dg : Digest (List (FG.Att Q.n)) N.Payload) (self : Fin Q.n) (t : Time) (i : Nat) :
    List (FG.Att Q.n) → NodeState N → Nat → List (CutRec N)
  | [], _, _ => []
  | a :: as, st, sub => groupRecs proposer dg self st t (Nat.pair i sub) (.attestation a) ++
      admitRecs proposer dg self t i as (exec proposer dg self st t (.attestation a)).1 (sub + 1)

/-- No admissions replay no cuts. -/
theorem admitRecs_nil (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (self : Fin Q.n) (t : Time) (i : Nat) (st : NodeState N) (sub : Nat) :
    admitRecs pr dg self t i [] st sub = [] := by rfl

/-- An admission replays its `.attestation` group, then the rest. -/
theorem admitRecs_cons (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (self : Fin Q.n) (t : Time) (i : Nat) (a : FG.Att Q.n) (as : List (FG.Att Q.n))
    (st : NodeState N) (sub : Nat) :
    admitRecs pr dg self t i (a :: as) st sub =
      groupRecs pr dg self st t (Nat.pair i sub) (.attestation a) ++
        admitRecs pr dg self t i as (exec pr dg self st t (.attestation a)).1 (sub + 1) := by rfl

omit [Countable I] in
/-- A cut of the admission replay is a cut of the `.attestation` group of one of the admitted
attestations, under an event id `Nat.pair i s` with `sub ≤ s`. -/
theorem mem_admitRecs (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (self : Fin Q.n) (t : Time) (i : Nat) :
    ∀ (as : List (FG.Att Q.n)) (st : NodeState N) (sub : Nat) (r : CutRec N),
      r ∈ admitRecs pr dg self t i as st sub →
      ∃ a ∈ as, ∃ (st' : NodeState N) (s : Nat), sub ≤ s ∧
        r ∈ groupRecs pr dg self st' t (Nat.pair i s) (.attestation a)
  | [], _, _, _, h => absurd h List.not_mem_nil
  | a :: as, st, sub, r, h => by
    rw [admitRecs_cons] at h
    rcases List.mem_append.mp h with h | h
    · exact ⟨a, List.mem_cons_self, st, sub, le_rfl, h⟩
    · obtain ⟨b, hb, st', s, hs, hr⟩ := mem_admitRecs pr dg self t i as _ (sub + 1) r h
      exact ⟨b, List.mem_cons_of_mem _ hb, st', s, by omega, hr⟩

end Admits

open Classical in
/-- The node of `v` after its tick at `t` (engine event `j`): the node's tick at a public time, with
the FG update exactly when `due` allows it, from the engine's node before the event; the engine's
node before the event at a time that is not public. -/
noncomputable def postTick (due : Fin (Fintype.card V) → Time → Bool) (v : V) (j : Nat)
    (t : Time) : NodeState A :=
  if (paramsAtCount p (Fintype.card V) hN hn).IsPublic t then
    (exec (runProposer rho hn) (digestOf e rho) (rho.ownKey v) (e.adapter.node (stateAt e rho v j))
      t (.tick (encodeTxs (Model.mempool rho.inbox v t)) (due (rho.ownKey v) t))).1
  else e.adapter.node (stateAt e rho v j)

open Classical in
/-- `postTick` unfolded. -/
theorem postTick_eq (due : Fin (Fintype.card V) → Time → Bool) (v : V) (j : Nat) (t : Time) :
    postTick e rho due v j t =
      if (paramsAtCount p (Fintype.card V) hN hn).IsPublic t then
        (exec (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
          (e.adapter.node (stateAt e rho v j)) t
          (.tick (encodeTxs (Model.mempool rho.inbox v t)) (due (rho.ownKey v) t))).1
      else e.adapter.node (stateAt e rho v j) := by rfl

open Classical in
/-- Replay one engine event on the node state held by the engine before the event; a tick of
`y` at `t` runs the node's tick at public times, with the FG update exactly when `due y t` (the
signing calendar). The own attestations the engine admits to the node's pool during the tick
(`admitsAt`) follow the tick group directly, each as its own `.attestation` group from the node
after its tick (`postTick`), under the event ids `Nat.pair i 1`, `Nat.pair i 2`, …: the node's
own publications, which the run's phase order allows before another node's tick at that time. -/
noncomputable def eventCutsWith (due : Fin (Fintype.card V) → Time → Bool) (i : Nat) :
    List (CutRec A) :=
  match rho.events[i]? with
  | some (.tick v t) =>
    (if (paramsAtCount p (Fintype.card V) hN hn).IsPublic t then
      groupRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
        (e.adapter.node (stateAt e rho v i)) t (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t)) (due (rho.ownKey v) t))
    else []) ++
    admitRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v) t i (admitsAt e rho v i)
      (postTick e rho due v i t) 1
  | some (.deliver v o t) =>
    let hs := Model.digests rho.hash o
    let st := stateAt e rho v i
    let C := receiverCodec e rho v
    deliverRecs C (runProposer rho hn) (digestOf e rho) hs (rho.ownKey v) t i
      (delivered C e.adapter hs st (wireOf e o)) (e.adapter.node st) 0
  | some (.restart v t) =>
    groupRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
      (e.adapter.node (stateAt e rho v i)) t (Nat.pair i 0) .restart
  | none => []

/-- Replay one engine event; a tick runs the FG update on the adapter's signing calendar. -/
noncomputable def eventCuts (i : Nat) : List (CutRec A) := eventCutsWith e rho e.adapter.sign i

/-- An absent engine event contributes no replay cuts. -/
theorem eventCuts_none (i : Nat) (he : rho.events[i]? = none) : eventCuts e rho i = [] := by
  unfold eventCuts eventCutsWith
  rw [he]

open Classical in
/-- A tick replays the node handler exactly at public times, then the node's own admissions. -/
theorem eventCuts_tick (i : Nat) (v : V) (t : Time)
    (he : rho.events[i]? = some (.tick v t)) :
    eventCuts e rho i =
      (if (paramsAtCount p (Fintype.card V) hN hn).IsPublic t then
        groupRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
          (e.adapter.node (stateAt e rho v i)) t (Nat.pair i 0)
          (.tick (encodeTxs (Model.mempool rho.inbox v t)) (e.adapter.sign (rho.ownKey v) t))
      else []) ++
      admitRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v) t i (admitsAt e rho v i)
        (postTick e rho e.adapter.sign v i t) 1 := by
  unfold eventCuts eventCutsWith
  rw [he]

/-- A restart replays the restart handler on the engine's current node state. -/
theorem eventCuts_restart (i : Nat) (v : V) (t : Time)
    (he : rho.events[i]? = some (.restart v t)) :
    eventCuts e rho i = groupRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
      (e.adapter.node (stateAt e rho v i)) t (Nat.pair i 0) .restart := by
  unfold eventCuts eventCutsWith
  rw [he]

open Classical in
/-- A delivery replays exactly the objects the encoder visits, starting at the pre-event state. -/
theorem eventCuts_deliver (i : Nat) (v : V) (o : (Model.protoOf (compiled F) E).Object)
    (t : Time) (he : rho.events[i]? = some (.deliver v o t)) :
    eventCuts e rho i =
      let hs := Model.digests rho.hash o
      let st := stateAt e rho v i
      let C := receiverCodec e rho v
      deliverRecs C (runProposer rho hn) (digestOf e rho) hs (rho.ownKey v) t i
        (delivered C e.adapter hs st (wireOf e o)) (e.adapter.node st) 0 := by
  unfold eventCuts eventCutsWith
  rw [he]

/-- Number of replay cuts strictly before an engine cut, under the signing calendar `due`. -/
noncomputable def cutMapWith (due : Fin (Fintype.card V) → Time → Bool) : Nat → Nat
  | 0 => 0
  | i + 1 => cutMapWith due i + (eventCutsWith e rho due i).length

/-- All replay cuts in engine event order, under the signing calendar `due`. -/
noncomputable def allCutsWith (due : Fin (Fintype.card V) → Time → Bool) : List (CutRec A) :=
  (List.range rho.events.length).flatMap (eventCutsWith e rho due)

/-- The replay trace under the signing calendar `due`; it stutters beyond its final labelled
cut. -/
noncomputable def simTraceWith (due : Fin (Fintype.card V) → Time → Bool) : RunTrace A where
  init := initial e rho
  node k := ((allCutsWith e rho due)[k]?).elim ⟨0, hn⟩ CutRec.node
  time k := ((allCutsWith e rho due)[k]?).elim (rho.horizon + 1) CutRec.time
  event k := ((allCutsWith e rho due)[k]?).elim (Nat.pair rho.events.length k) CutRec.event
  pos k := ((allCutsWith e rho due)[k]?).elim 0 CutRec.pos
  label k := ((allCutsWith e rho due)[k]?).map CutRec.label
  post k := ((allCutsWith e rho due)[k]?).elim (Node.init A) CutRec.post
  awake y t := E.awake (rho.key y) t = true ∧ 0 ≤ t ∧ t ≤ rho.horizon
  observationHorizon := some rho.horizon

/-- Number of replay cuts strictly before an engine cut. -/
noncomputable def cutMap : Nat → Nat := cutMapWith e rho e.adapter.sign

/-- All replay cuts in engine event order. -/
noncomputable def allCuts : List (CutRec A) := allCutsWith e rho e.adapter.sign

/-- The replay trace on the adapter's signing calendar; it stutters beyond its final labelled
cut. -/
noncomputable def simTrace : RunTrace A := simTraceWith e rho e.adapter.sign

/-- The replay is the calendar replay at the adapter's signing calendar. -/
theorem simTrace_eq_with : simTrace e rho = simTraceWith e rho e.adapter.sign := by rfl

/-- The event cuts are the calendar event cuts at the adapter's signing calendar. -/
theorem eventCuts_eq_with (i : Nat) : eventCuts e rho i = eventCutsWith e rho e.adapter.sign i :=
  by rfl

open Classical in
/-- Under a calendar, a tick replays the node handler at public times with the calendar's flag,
then the node's own admissions. -/
theorem eventCutsWith_tick (due : Fin (Fintype.card V) → Time → Bool) (i : Nat) (v : V)
    (t : Time) (he : rho.events[i]? = some (.tick v t)) :
    eventCutsWith e rho due i =
      (if (paramsAtCount p (Fintype.card V) hN hn).IsPublic t then
        groupRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
          (e.adapter.node (stateAt e rho v i)) t (Nat.pair i 0)
          (.tick (encodeTxs (Model.mempool rho.inbox v t)) (due (rho.ownKey v) t))
      else []) ++
      admitRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v) t i (admitsAt e rho v i)
        (postTick e rho due v i t) 1 := by
  unfold eventCutsWith
  rw [he]

/-- Under a calendar, a restart replays the restart handler. -/
theorem eventCutsWith_restart (due : Fin (Fintype.card V) → Time → Bool) (i : Nat) (v : V)
    (t : Time) (he : rho.events[i]? = some (.restart v t)) :
    eventCutsWith e rho due i = groupRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
      (e.adapter.node (stateAt e rho v i)) t (Nat.pair i 0) .restart := by
  unfold eventCutsWith
  rw [he]

open Classical in
/-- Under a calendar, a delivery replays the objects the encoder visits. -/
theorem eventCutsWith_deliver (due : Fin (Fintype.card V) → Time → Bool) (i : Nat) (v : V)
    (o : (Model.protoOf (compiled F) E).Object) (t : Time)
    (he : rho.events[i]? = some (.deliver v o t)) :
    eventCutsWith e rho due i =
      deliverRecs (receiverCodec e rho v) (runProposer rho hn) (digestOf e rho)
        (Model.digests rho.hash o) (rho.ownKey v) t i
        (delivered (receiverCodec e rho v) e.adapter (Model.digests rho.hash o) (stateAt e rho v i)
          (wireOf e o)) (e.adapter.node (stateAt e rho v i)) 0 := by
  unfold eventCutsWith
  rw [he]

/-- Under a calendar, an absent engine event contributes no replay cuts. -/
theorem eventCutsWith_none (due : Fin (Fintype.card V) → Time → Bool) (i : Nat)
    (he : rho.events[i]? = none) : eventCutsWith e rho due i = [] := by
  unfold eventCutsWith
  rw [he]

/-- The calendar prefix map advances by the length of the next event's replay. -/
theorem cutMapWith_succ (due : Fin (Fintype.card V) → Time → Bool) (i : Nat) :
    cutMapWith e rho due (i + 1) = cutMapWith e rho due i + (eventCutsWith e rho due i).length :=
  by rfl

/-- The calendar prefix map starts at zero. -/
theorem cutMapWith_zero (due : Fin (Fintype.card V) → Time → Bool) : cutMapWith e rho due 0 = 0 :=
  by rfl

/-- The calendar replay's cuts, in engine event order. -/
theorem allCutsWith_eq (due : Fin (Fintype.card V) → Time → Bool) : allCutsWith e rho due =
    (List.range rho.events.length).flatMap (eventCutsWith e rho due) := by rfl

/-- The calendar trace's node, time, event id and label at a cut are its record's. -/
theorem simTraceWith_fields (due : Fin (Fintype.card V) → Time → Bool) (k : Nat) :
    (simTraceWith e rho due).node k = ((allCutsWith e rho due)[k]?).elim ⟨0, hn⟩ CutRec.node ∧
    (simTraceWith e rho due).time k =
      ((allCutsWith e rho due)[k]?).elim (rho.horizon + 1) CutRec.time ∧
    (simTraceWith e rho due).event k =
      ((allCutsWith e rho due)[k]?).elim (Nat.pair rho.events.length k) CutRec.event ∧
    (simTraceWith e rho due).label k = ((allCutsWith e rho due)[k]?).map CutRec.label :=
  ⟨by rfl, by rfl, by rfl, by rfl⟩

/-- Growing faults change the honest keys at observation time, not the replay trace. -/
noncomputable def simTraceAt : RunTrace A := simTrace e rho

/-- The prefix map starts at zero. -/
theorem cutMap_zero : cutMap e rho 0 = 0 := by rfl

/-- The prefix map advances by the length of the next event's replay. -/
theorem cutMap_succ (i : Nat) : cutMap e rho (i + 1) =
    cutMap e rho i + (eventCuts e rho i).length := by rfl

/-- The initial trace state is the node projection of own-role initialization. -/
theorem simTrace_init_eq (y : Fin (Fintype.card V)) :
    (simTrace e rho).init y =
      e.adapter.node ((e.ops hn).init y (fun r => decide (y ∈ rho.sel (engineRole e r)))
        (voteIOAt e rho (rho.key y))) := by rfl

/-- Growing replay has the same cuts as ordinary replay. -/
theorem simTraceAt_eq : simTraceAt e rho = simTrace e rho := by rfl

omit [DecidableEq V] in
/-- Membership is determined by the run's initial faulty set. -/
theorem mem_honestKeys_iff (y : Fin (Fintype.card V)) :
    y ∈ honestKeys rho ↔ rho.key y ∉ rho.faultyAt 0 := by rfl

omit [DecidableEq V] in
/-- Membership is determined by the run's faulty set at the clamped time. -/
theorem mem_honestKeysAt_iff (t : Time) (y : Fin (Fintype.card V)) :
    y ∈ honestKeysAt rho t ↔ rho.key y ∉ rho.faultyAt (min t rho.horizon) := by rfl

omit [DecidableEq V] in
/-- The run-derived proposal key, with key zero as the empty-selection default. -/
theorem runProposer_eq (s : Nat) : runProposer rho hn s =
    if h : (rho.sel (.proposer s)).Nonempty then (rho.sel (.proposer s)).min' h
    else ⟨0, hn⟩ := by rfl

/-- The envelope at a cut is the corresponding component of the actual engine state. -/
theorem stateAt_eq (v : V) (i : Nat) : stateAt e rho v i =
    (cast (congrArg (fun s : ChainShape (pubOf E) O.Id I => s.State) e.shape_eq)
      (rho.stateBefore i v).st.1 : ∀ h, e.State h) hn := by rfl

omit [DecidableEq V] in
/-- Non-genesis blocks use their tagged engine header hash. -/
theorem digestOf_eq (par : Option Nat) (s x : Nat)
    (atts : List (FG.Att (paramsAtCount p (Fintype.card V) hN hn).n))
    (payload : A.Payload) : digestOf e rho par s x atts payload =
    match par with
    | none => (paramsAtCount p (Fintype.card V) hN hn).genesisRoot
    | some r => taggedRoot (paramsAtCount p (Fintype.card V) hN hn).genesisRoot
        (rho.hash ⟨parentRef (paramsAtCount p (Fintype.card V) hN hn).genesisRoot (some r),
          s, x, e.codec.encode atts payload⟩) := by rfl

/-- The cuts of every engine event, in order. -/
theorem allCuts_eq : allCuts e rho =
    (List.range rho.events.length).flatMap (eventCuts e rho) := by rfl

/-- The recorded node, or key zero during stuttering. -/
theorem simTrace_node (k : Nat) :
    (simTrace e rho).node k = ((allCuts e rho)[k]?).elim ⟨0, hn⟩ CutRec.node := by rfl

/-- The recorded time, or one past the horizon during stuttering. -/
theorem simTrace_time (k : Nat) :
    (simTrace e rho).time k = ((allCuts e rho)[k]?).elim (rho.horizon + 1) CutRec.time := by rfl

/-- Recorded and stutter groups have disjoint event identifiers. -/
theorem simTrace_event (k : Nat) : (simTrace e rho).event k =
    ((allCuts e rho)[k]?).elim (Nat.pair rho.events.length k) CutRec.event := by rfl

/-- The position within a replayed group, or zero during stuttering. -/
theorem simTrace_pos (k : Nat) :
    (simTrace e rho).pos k = ((allCuts e rho)[k]?).elim 0 CutRec.pos := by rfl

/-- After the replay there are no more labelled cuts. -/
theorem simTrace_label (k : Nat) :
    (simTrace e rho).label k = ((allCuts e rho)[k]?).map CutRec.label := by rfl

/-- The recorded post-state, or the bare initial state during stuttering. -/
theorem simTrace_post (k : Nat) :
    (simTrace e rho).post k = ((allCuts e rho)[k]?).elim (Node.init A) CutRec.post := by rfl

/-- Awake is read from the environment within the trace horizon. -/
theorem simTrace_awake_iff (y : Fin (Fintype.card V)) (t : Time) :
    (simTrace e rho).awake y t ↔ E.awake (rho.key y) t = true ∧ 0 ≤ t ∧ t ≤ rho.horizon := by rfl

/-- The observation horizon is the engine horizon. -/
theorem simTrace_observationHorizon : (simTrace e rho).observationHorizon = some rho.horizon :=
  by rfl

/-- A one-run state correspondence target for an instance's compiled execution.
The implementation must establish this from that run's validity. -/
def StateAgreement : Prop :=
  ∀ (v : V) (i : Nat), i ≤ rho.events.length →
    rho.point.HonestAt v (rho.cutTime i) →
    e.adapter.node (stateAt e rho v i) = (simTrace e rho).state (rho.ownKey v) (cutMap e rho i)

/-- State agreement is equality at the same bounded engine and replay prefix. -/
theorem stateAgreement_iff : StateAgreement e rho ↔
    ∀ (v : V) (i : Nat), i ≤ rho.events.length →
      rho.point.HonestAt v (rho.cutTime i) →
      e.adapter.node (stateAt e rho v i) = (simTrace e rho).state (rho.ownKey v) (cutMap e rho i) :=
  by rfl

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace
