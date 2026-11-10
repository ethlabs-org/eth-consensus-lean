module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.NodeEngine.Stages
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model
public import Mathlib.Data.Finset.Max

@[expose] public section
namespace Consensus.Goldilocks.NodeEngine
open Blocks Shape Node
open Consensus.Model (pubOf)

/-- Root encoding is data; injectivity and genesis separation are separate obligations. -/
structure TraceData where
  tag : Nat → Nat → Nat

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  {I B : Type} {O : OutputSchema} [DecidableEq I] [Countable I]
  (A : Family I B) (fin : O.Id → Bool)
  (rho : Model.Run (compiled (shapeFamily A fin)) E) (hn : 1 ≤ Fintype.card V)

abbrev nodeAC := (A.runtime (pubOf E) hn).operations.toAC
abbrev runWire := A.wire (pubOf E) hn

noncomputable def digest (D : TraceData) :
    Digest (List (FG.Att (Fintype.card V))) (A.Payload (Fintype.card V)) :=
  fun par s x atts p => match par with
  | none => (A.runtime (pubOf E) hn).genesisRoot
  | some r => D.tag (A.runtime (pubOf E) hn).genesisRoot
      (rho.hash ⟨(runWire (E := E) A hn).parentRef (some r), s, x,
        (runWire (E := E) A hn).encodeInfo atts p⟩)

noncomputable def proposer (s : Nat) : Fin (Fintype.card V) :=
  if h : (rho.sel (.proposer s)).Nonempty then (rho.sel (.proposer s)).min' h else ⟨0, hn⟩

def honestAt (t : Time) : Set (Fin (Fintype.card V)) :=
  {y | rho.key y ∉ rho.faultyAt (min t rho.horizon)}

noncomputable def engineState (v : V) (i : Nat) := (rho.stateBefore i v).st.1 hn

/-- Generic cut successor, including the record written by an attestation signing. -/
noncomputable def postCut {P : Params} {N : NodeAC P}
    (self : Fin P.n) (t : Time) (st : NodeState N) : Cut N → NodeState N
  | .ac ℓ => { st with ac := (N.step self st.ac ℓ.frame t ℓ.call).1 }
  | .fg (.block C true) => { st with fg := (st.fg.onBlock C).getD st.fg }
  | .fg (.block _ false) => st
  | .fg (.attestation a) => { st with fg := st.fg.onAttestation a }
  | .fg (.attest _ none) => st
  | .fg (.attest C (some _)) =>
    { st with record := ((st.fg.attest st.record self C).map Prod.snd).getD st.record }

noncomputable def posts {P : Params} {N : NodeAC P} (self : Fin P.n) (t : Time) :
    List (Cut N) → NodeState N → List (NodeState N)
  | [], _ => []
  | c :: cs, st => postCut self t st c :: posts self t cs (postCut self t st c)

structure Record {P : Params} (N : NodeAC P) where
  node : Fin P.n
  time : Time
  event : Nat
  pos : Nat
  label : Cut N
  post : NodeState N

variable (D : TraceData)

noncomputable def group (self : Fin (Fintype.card V)) (st : NodeState (nodeAC (E := E) A hn))
    (t : Time) (id : Nat) (e : Node.Event (nodeAC (E := E) A hn)) :
    List (Record (nodeAC (E := E) A hn)) :=
  let cs := (Node.exec (proposer A fin rho hn) (digest A fin rho hn D) self st t e).2
  (cs.zip (posts self t cs st)).mapIdx fun k cp => ⟨self, t, id, k, cp.1, cp.2⟩

noncomputable def delivery (hs : List (Header I × Nat))
    (self : Fin (Fintype.card V)) (t : Time) (i : Nat) :
    List (ShapeObj (Fintype.card V) Empty I B) → NodeState (nodeAC (E := E) A hn) → Nat →
      List (Record (nodeAC (E := E) A hn))
  | [], _, _ => []
  | o :: os, st, sub => match (runWire (E := E) A hn).canonEvent hs o with
    | some e => group A fin rho hn D self st t (Nat.pair i sub) e ++
        delivery hs self t i os
          (Node.exec (proposer A fin rho hn) (digest A fin rho hn D) self st t e).1 (sub + 1)
    | none => delivery hs self t i os st (sub + 1)

open Classical in
noncomputable def eventRecords (i : Nat) : List (Record (nodeAC (E := E) A hn)) :=
  match rho.events[i]? with
  | some (.tick v t) => if (params (pubOf E) hn
      (A.runtime (pubOf E) hn).genesisRoot (A.runtime (pubOf E) hn).δt).IsPublic t then
      group A fin rho hn D (rho.ownKey v) (engineState A fin rho hn v i).node t
        (Nat.pair i 0) (.tick (encodeTxs (Model.mempool rho.inbox v t))) else []
  | some (.deliver v o t) => delivery A fin rho hn D (Model.digests rho.hash o)
      (rho.ownKey v) t i o.parts (engineState A fin rho hn v i).node 0
  | some (.restart v t) => group A fin rho hn D (rho.ownKey v)
      (engineState A fin rho hn v i).node t (Nat.pair i 0) .restart
  | none => []

noncomputable def cutMapNode : Nat → Nat
  | 0 => 0
  | i + 1 => cutMapNode i + (eventRecords A fin rho hn D i).length

noncomputable def records := (List.range rho.events.length).flatMap (eventRecords A fin rho hn D)

/-- The canonical growing trace is computed, never chosen from a simulation witness. -/
noncomputable def simTraceNodeAt : RunTrace (nodeAC (E := E) A hn) where
  init _ := Node.init _
  node k := ((records A fin rho hn D)[k]?).elim ⟨0, hn⟩ Record.node
  time k := ((records A fin rho hn D)[k]?).elim (rho.horizon + 1) Record.time
  event k := ((records A fin rho hn D)[k]?).elim (Nat.pair rho.events.length k) Record.event
  pos k := ((records A fin rho hn D)[k]?).elim 0 Record.pos
  label k := ((records A fin rho hn D)[k]?).map Record.label
  post k := ((records A fin rho hn D)[k]?).elim (Node.init _) Record.post
  awake y t := E.awake (rho.key y) t = true ∧ 0 ≤ t ∧ t ≤ rho.horizon
  observationHorizon := some rho.horizon

def lastClockNode (v : V) : Nat → Time
  | 0 => 0
  | i + 1 => match rho.events[i]? with
    | some (.tick w t) | some (.restart w t) => if w = v then t else lastClockNode v i
    | _ => lastClockNode v i

end Consensus.Goldilocks.NodeEngine
