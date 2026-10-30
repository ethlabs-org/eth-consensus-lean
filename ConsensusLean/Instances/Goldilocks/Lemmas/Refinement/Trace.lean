module
public import ConsensusLean.Instances.Goldilocks.Statements.Refinement
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts

public section

/-! # Goldilocks Refinement: the simulating trace

The run of the spec's node that simulates a valid engine run (`EngineSimulatesNode`,
`Statements/Refinement`) is **built from the engine run**, not chosen: every engine event of an
honest node is replayed through the node's handler (`Node.exec`) on the node state the engine holds
before the event, and the handler's cuts, with their post-states (`cutPost`, the unique successor
of the cut law), become the trace's cuts. The cut map `ι` (`cutMap`) counts the cuts of the events
before an engine cut.

* A tick at a public time is the node's tick with the engine's input (the encoded mempool), a
  tick at a non-public time contributes no cut (`eventCuts`).
* A delivery is one group per canonical object it carries (`deliverRecs`), with the node state
  threaded through the handlers; a dropped object, or a canonical object whose handler makes no
  cut, contributes nothing. The sub-event index gives each group its own event id (`Nat.pair`).
* A restart is the restart group.
* After the last engine cut the trace stutters: unlabelled cuts at the horizon, each under its own
  event id.
* The trace's awake function is the environment's, clamped to `[0, ∞)` and to the trace's horizon
  (`awakeAt`), so that `awake_in_horizon` holds by construction and `Simulates.awake_to` is the
  clamp itself.

The proof that this trace is a `GoldilocksRun` and that the engine agrees with it at every cut is
split into named steps (`Shape`, `Steps`, `Run`), assembled in `Simulation`. This file has no
`sorry`. -/

namespace Consensus.Goldilocks

open Blocks

/-! ## The post-state of a cut -/

namespace Node

variable {P : Params} {A : NodeAC P}

/-- The node state after cut `c` of validator `self` at time `t` from `st`: the successor the cut
law `CutStep` determines (an AC cut writes the AC's step, an accepted block the store's `onBlock`,
an attestation the store's `onAttestation`, a signing attest the new record; a refused block and
a silent attest change nothing). -/
noncomputable def cutPost (self : Fin P.n) (t : Time) (st : NodeState A) : Cut A → NodeState A
  | .ac ℓ => { st with ac := (A.step self st.ac ℓ.frame t ℓ.call).1 }
  | .fg (.block B true) => { st with fg := (st.fg.onBlock B).getD st.fg }
  | .fg (.block _ false) => st
  | .fg (.attestation a) => { st with fg := st.fg.onAttestation a }
  | .fg (.attest _ none) => st
  | .fg (.attest C (some _)) =>
      { st with record := ((st.fg.attest st.record self C).map Prod.snd).getD st.record }

/-- The post-states of the cuts `cs` in order from `st`, one per cut. -/
noncomputable def cutPosts (self : Fin P.n) (t : Time) :
    List (Cut A) → NodeState A → List (NodeState A)
  | [], _ => []
  | c :: cs, st => cutPost self t st c :: cutPosts self t cs (cutPost self t st c)

/-- The cut law's successor is `cutPost`. -/
theorem cutPost_of_cutStep {self : Fin P.n} {t : Time} {st st' : NodeState A} {c : Cut A}
    (h : CutStep self t st c st') : cutPost self t st c = st' := by
  obtain ⟨fg', ac', r'⟩ := st'
  cases c with
  | ac ℓ =>
    obtain ⟨-, e, hfg, hr⟩ := h
    simp only at hfg hr
    subst hfg hr
    simp only [cutPost, e]
  | fg ℓ =>
    rcases ℓ with ⟨B, acc⟩ | a | ⟨C, signed⟩
    · cases acc with
      | true =>
        obtain ⟨-, e, hac, hr⟩ := h
        simp only at hac hr
        subst hac hr
        simp only [cutPost, e, Option.getD_some]
      | false =>
        obtain ⟨-, e⟩ := h
        simp only [cutPost, e]
    · obtain ⟨hfg, hac, hr⟩ := h
      simp only at hfg hac hr
      subst hfg hac hr
      rfl
    · cases signed with
      | none =>
        obtain ⟨-, e⟩ := h
        simp only [cutPost, e]
      | some a =>
        obtain ⟨e, hfg, hac⟩ := h
        simp only at hfg hac
        subst hfg hac
        simp only [cutPost, e, Option.map_some, Option.getD_some]

/-- A cut chain ends at the fold of `cutPost` over its cuts. -/
theorem foldl_cutPost_of_cutChain {self : Fin P.n} {t : Time} {st st' : NodeState A}
    {cs : List (Cut A)} (h : CutChain self t st cs st') : cs.foldl (cutPost self t) st = st' := by
  induction h with
  | nil => rfl
  | cons hc _ ih => simp only [List.foldl_cons, cutPost_of_cutStep hc, ih]

/-- The handler's result state is the fold of `cutPost` over its cuts (C0.5). -/
theorem foldl_cutPost_exec (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) (e : Event A) :
    (exec dg self st t e).2.foldl (cutPost self t) st = (exec dg self st t e).1 :=
  foldl_cutPost_of_cutChain (Compose.exec_is_cut_chain dg self st t e)

end Node

/-! ## The cuts of an engine event -/

namespace Refinement

open Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- One cut of the simulating trace: its node, time, event id, position, label and post-state. -/
structure CutRec (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n))) where
  /-- The node of the cut. -/
  node : Fin sp.n
  /-- The time of the cut. -/
  time : Time
  /-- The event id of the cut's group. -/
  event : Nat
  /-- The position inside the group. -/
  pos : Nat
  /-- The label. -/
  label : Cut (goldilocksNode sp ro)
  /-- The node state after the cut. -/
  post : NodeState (goldilocksNode sp ro)

/-- The cuts of the top-level event `e` of `self` at time `t` on `st`, under the event id `id`:
the handler's cuts at positions `0, 1, …` with their post-states. -/
noncomputable def groupRecs (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp ro)) (t : Time) (id : Nat)
    (e : Event (goldilocksNode sp ro)) : List (CutRec sp ro) :=
  let cs := (exec dg self st t e).2
  (cs.zip (cutPosts self t cs st)).mapIdx fun k cp => ⟨self, t, id, k, cp.1, cp.2⟩

/-- The cuts of a delivery of the objects `os` to `self` at time `t`, from the node state `st`,
the sub-event index `sub` on: the group of each canonical object (`canonEvent`) under the event
id `Nat.pair i sub` of the engine event `i`, the state threaded through the handlers; nothing for
a dropped object. -/
noncomputable def deliverRecs (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat) :
    List (Wire sp.n) → NodeState (goldilocksNode sp ro) → Nat → List (CutRec sp ro)
  | [], _, _ => []
  | o :: os, st, sub =>
      match canonEvent sp ro hs o with
      | some e =>
          groupRecs dg self st t (Nat.pair i sub) e ++
            deliverRecs dg hs self t i os (exec dg self st t e).1 (sub + 1)
      | none => deliverRecs dg hs self t i os st (sub + 1)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

open Classical in
/-- The node cuts of engine event `i`: a tick at a public time is the node's tick with the
engine's input (the encoded mempool) on the node state the engine holds before the event, a tick
at a non-public time has none; a delivery is `deliverRecs` of its `delivered` objects with the
digests the engine passes; a restart is the restart group. Nothing past the last event. -/
noncomputable def eventCuts (i : Nat) : List (CutRec (S.params (pubOf E) hn) (S.ro _)) :=
  match rho.events[i]? with
  | some (.tick v t) =>
      if (S.params (pubOf E) hn).toParams.IsPublic t then
        groupRecs (digestOf S rho) (rho.ownKey v) (stateAt S rho hn v i).node t (Nat.pair i 0)
          (.tick (encodeTxs (Model.mempool rho.inbox v t)))
      else []
  | some (.deliver v o t) =>
      deliverRecs (digestOf S rho) (Model.digests rho.hash o) (rho.ownKey v) t i
        (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn v i).node 0
  | some (.restart v t) =>
      groupRecs (digestOf S rho) (rho.ownKey v) (stateAt S rho hn v i).node t (Nat.pair i 0)
        .restart
  | none => []

/-- The cut map `ι`: the number of node cuts of the engine events before engine cut `i`. -/
noncomputable def cutMap : Nat → Nat
  | 0 => 0
  | i + 1 => cutMap i + (eventCuts S rho hn i).length

/-- All node cuts of the run, in order. -/
noncomputable def allCuts : List (CutRec (S.params (pubOf E) hn) (S.ro _)) :=
  (List.range rho.events.length).flatMap (eventCuts S rho hn)

/-- The time of node cut `k`: the time of its engine event; the horizon past the last cut. -/
noncomputable def cutTime (k : Nat) : Time :=
  ((allCuts S rho hn)[k]?).elim rho.horizon CutRec.time

/-- The label of node cut `k`: its cut; none past the last cut. -/
noncomputable def cutLabel (k : Nat) :
    Option (Cut (goldilocksNode (S.params (pubOf E) hn) (S.ro _))) :=
  ((allCuts S rho hn)[k]?).map CutRec.label

/-- The trace's awake function: the environment's, from time `0` on and within the trace's
horizon (some labelled cut at or after the time). -/
def awakeAt (y : Fin (Fintype.card V)) (t : Time) : Prop :=
  E.awake (rho.key y) t = true ∧ 0 ≤ t ∧ ∃ k, cutLabel S rho hn k ≠ none ∧ t ≤ cutTime S rho hn k

/-- **The simulating trace** of the engine run `rho`: the node cuts of its events in order
(`allCuts`), then unlabelled cuts at the horizon under fresh event ids. -/
noncomputable def simTrace : GoldilocksTrace (S.params (pubOf E) hn) (S.ro _) where
  init _ := Node.init _
  node k := ((allCuts S rho hn)[k]?).elim ⟨0, hn⟩ CutRec.node
  time := cutTime S rho hn
  event k := ((allCuts S rho hn)[k]?).elim (Nat.pair rho.events.length k) CutRec.event
  pos k := ((allCuts S rho hn)[k]?).elim 0 CutRec.pos
  label := cutLabel S rho hn
  post k := ((allCuts S rho hn)[k]?).elim (Node.init _) CutRec.post
  awake := awakeAt S rho hn

/-- Every node of the trace starts from the initial node state. -/
theorem simTrace_init_eq (y : Fin (Fintype.card V)) :
    (simTrace S rho hn).init y = Node.init (goldilocksNode (S.params (pubOf E) hn) (S.ro _)) := by
  rfl

/-- The trace's horizon is `awakeAt`'s clamp. -/
theorem simTrace_inHorizon_iff (t : Time) :
    (simTrace S rho hn).InHorizon t ↔ ∃ k, cutLabel S rho hn k ≠ none ∧ t ≤ cutTime S rho hn k :=
  Iff.rfl

/-- The trace's awake function is `awakeAt`. -/
theorem simTrace_awake_iff (y : Fin (Fintype.card V)) (t : Time) :
    (simTrace S rho hn).awake y t ↔ awakeAt S rho hn y t :=
  Iff.rfl

/-- An honest node is awake only within the run's horizon: `awakeAt`'s clamp
(`LocalRun.awake_in_horizon`). -/
theorem simTrace_awake_in_horizon :
    ∀ y ∈ honestKeys S rho, ∀ t, (simTrace S rho hn).awake y t →
      (simTrace S rho hn).InHorizon t :=
  fun _ _ _ h => h.2.2

/-- An honest node awake in the environment at a time from `0` within the trace's horizon is
awake in the trace: `awakeAt` is that clamp (`Simulates.awake_to`). -/
theorem simTrace_awake_to :
    ∀ y ∈ honestKeys S rho, ∀ t, E.awake (rho.key y) t = true → 0 ≤ t →
      (simTrace S rho hn).InHorizon t → (simTrace S rho hn).awake y t :=
  fun _ _ _ hw h0 hh => ⟨hw, h0, hh⟩

/-- The trace's cut map starts at `0`. -/
theorem cutMap_zero : cutMap S rho hn 0 = 0 := by rfl

/-- The cut map is monotone. -/
theorem cutMap_mono : Monotone (cutMap S rho hn) :=
  monotone_nat_of_le_succ fun i => by
    change cutMap S rho hn i ≤ cutMap S rho hn (i + 1)
    simp only [cutMap]
    exact Nat.le_add_right _ _

end Refinement

end Consensus.Goldilocks

end
