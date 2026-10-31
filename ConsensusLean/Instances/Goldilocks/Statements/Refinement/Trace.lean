module
public import ConsensusLean.Spec.Shape.Run
public import ConsensusLean.Instances.Goldilocks.Refinement.Defs

@[expose] public section

/-! Canonical engine-to-node trace construction. These definitions are protected because
collision transport refers to this trace, not an arbitrary trace satisfying simulation laws.
The construction is unchanged from Lemmas/Refinement/Trace; its proofs remain there. -/

namespace Consensus.Goldilocks

open Blocks

namespace Node

variable {P : Params} {A : NodeAC P}

noncomputable def cutPost (self : Fin P.n) (t : Time) (st : NodeState A) : Cut A → NodeState A
  | .ac ℓ => { st with ac := (A.step self st.ac ℓ.frame t ℓ.call).1 }
  | .fg (.block B true) => { st with fg := (st.fg.onBlock B).getD st.fg }
  | .fg (.block _ false) => st
  | .fg (.attestation a) => { st with fg := st.fg.onAttestation a }
  | .fg (.attest _ none) => st
  | .fg (.attest C (some _)) =>
      { st with record := ((st.fg.attest st.record self C).map Prod.snd).getD st.record }

noncomputable def cutPosts (self : Fin P.n) (t : Time) :
    List (Cut A) → NodeState A → List (NodeState A)
  | [], _ => []
  | c :: cs, st => cutPost self t st c :: cutPosts self t cs (cutPost self t st c)

end Node

namespace Refinement

open Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- The honest keys of the engine run. -/
def honestKeys : Set (Fin (Fintype.card V)) := {k | rho.key k ∈ rho.honest}

/-- The tagged node digest induced by the engine hash. -/
noncomputable def digestOf :
    Digest (List (FG.Att (Fintype.card V))) (Payload (Fintype.card V)) :=
  dgOf rho.hash S.genesisRoot

/-- The selected proposer, totalized for invalid selections. -/
noncomputable def runProposer (s : Nat) : Fin (Fintype.card V) :=
  if h : (rho.sel (.proposer s)).Nonempty then (rho.sel (.proposer s)).min' h
  else ⟨0, hn⟩

/-- The node state held by the shape before an engine cut. -/
noncomputable def stateAt (v : V) (i : Nat) : State (S.params (pubOf E) hn) (S.ro _) :=
  (rho.stateBefore i v).st.1 hn

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

structure CutRec (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n))) where
  node : Fin sp.n
  time : Time
  event : Nat
  pos : Nat
  label : Cut (goldilocksNode sp ro)
  post : NodeState (goldilocksNode sp ro)

noncomputable def groupRecs (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp ro)) (t : Time) (id : Nat)
    (e : Event (goldilocksNode sp ro)) : List (CutRec sp ro) :=
  let cs := (exec proposer dg self st t e).2
  (cs.zip (cutPosts self t cs st)).mapIdx fun k cp => ⟨self, t, id, k, cp.1, cp.2⟩

noncomputable def deliverRecs (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat) :
    List (Wire sp.n) → NodeState (goldilocksNode sp ro) → Nat → List (CutRec sp ro)
  | [], _, _ => []
  | o :: os, st, sub =>
      match canonEvent sp ro hs o with
      | some e =>
          groupRecs proposer dg self st t (Nat.pair i sub) e ++
            deliverRecs proposer dg hs self t i os (exec proposer dg self st t e).1 (sub + 1)
      | none => deliverRecs proposer dg hs self t i os st (sub + 1)

open Classical in
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

noncomputable def cutMap : Nat → Nat
  | 0 => 0
  | i + 1 => cutMap i + (eventCuts S rho hn i).length

noncomputable def allCuts : List (CutRec (S.params (pubOf E) hn) (S.ro _)) :=
  (List.range rho.events.length).flatMap (eventCuts S rho hn)

noncomputable def cutTime (k : Nat) : Time :=
  ((allCuts S rho hn)[k]?).elim (rho.horizon + 1) CutRec.time

noncomputable def cutLabel (k : Nat) :
    Option (Cut (goldilocksNode (S.params (pubOf E) hn) (S.ro _))) :=
  ((allCuts S rho hn)[k]?).map CutRec.label

def awakeAt (_hn : 1 ≤ Fintype.card V) (y : Fin (Fintype.card V)) (t : Time) : Prop :=
  E.awake (rho.key y) t = true ∧ 0 ≤ t ∧ t ≤ rho.horizon

noncomputable def simTrace : GoldilocksTrace (S.params (pubOf E) hn) (S.ro _) where
  init _ := Node.init _
  node k := ((allCuts S rho hn)[k]?).elim ⟨0, hn⟩ CutRec.node
  time := cutTime S rho hn
  event k := ((allCuts S rho hn)[k]?).elim (Nat.pair rho.events.length k) CutRec.event
  pos k := ((allCuts S rho hn)[k]?).elim 0 CutRec.pos
  label := cutLabel S rho hn
  post k := ((allCuts S rho hn)[k]?).elim (Node.init _) CutRec.post
  awake := awakeAt S rho hn
  observationHorizon := some rho.horizon

end Refinement
end Consensus.Goldilocks
