module
public import ConsensusLean.Instances.Goldilocks.Statements.Refinement.Interface
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts

public section

/-! # Goldilocks Refinement: the simulating trace

The facts about the trace that simulates a valid engine run (`EngineSimulatesNode`,
`Statements/Refinement`). The construction itself, its definitions and their docstrings are in
the protected module `Statements/Refinement/Trace` (`cutPost`, `eventCuts`, `cutMap`,
`simTrace`, …), which states how each engine event becomes the trace's cuts; this module proves
the characterising lemmas of those definitions.

The proof that this trace is a `GoldilocksRun` and that the engine agrees with it at every cut is
split into named steps (`Shape`, `Steps`, `Run`), assembled in `Simulation`. This file has no
`sorry`. -/

namespace Consensus.Goldilocks

open Blocks

/-! ## The post-state of a cut -/

namespace Node

variable {P : Params} {A : NodeAC P}

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
theorem foldl_cutPost_exec (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) (e : Event A) :
    (exec proposer dg self st t e).2.foldl (cutPost self t) st = (exec proposer dg self st t e).1 :=
  foldl_cutPost_of_cutChain (Compose.exec_is_cut_chain proposer dg self st t e)

end Node

/-! ## The cuts of an engine event -/

namespace Refinement

open Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- Every node of the trace starts from the initial node state. -/
theorem simTrace_init_eq (y : Fin (Fintype.card V)) :
    (simTrace S rho hn).init y = Node.init (goldilocksNode (S.params (pubOf E) hn) (S.ro _)) := by
  rfl

/-- The trace's horizon is `awakeAt`'s clamp. -/
theorem simTrace_inHorizon_iff (t : Time) :
    (simTrace S rho hn).InHorizon t ↔
      ∃ k, (cutLabel S rho hn k ≠ none ∨ t ≤ rho.horizon) ∧ t ≤ cutTime S rho hn k := by
  simp [RunTrace.InHorizon, simTrace]

/-- The trace's awake function is `awakeAt`. -/
theorem simTrace_awake_iff (y : Fin (Fintype.card V)) (t : Time) :
    (simTrace S rho hn).awake y t ↔ awakeAt S rho hn y t :=
  Iff.rfl

/-- An honest node is awake only within the run's horizon: `awakeAt`'s clamp
(`LocalRun.awake_in_horizon`). -/
theorem simTrace_awake_in_horizon :
    ∀ y ∈ honestKeys S rho, ∀ t, (simTrace S rho hn).awake y t →
      (simTrace S rho hn).InHorizon t := by
  intro y _ t h
  refine (simTrace_inHorizon_iff S rho hn t).mpr
    ⟨(allCuts S rho hn).length, Or.inr h.2.2, ?_⟩
  simp only [cutTime, List.getElem?_length, Option.elim_none]
  linarith [h.2.2]

/-- An honest node awake in the environment at a time from `0` within the trace's horizon is
awake in the trace: `awakeAt` is that clamp (`Simulates.awake_to`). -/
theorem simTrace_awake_before_horizon :
    ∀ y ∈ honestKeys S rho, ∀ t, E.awake (rho.key y) t = true → 0 ≤ t →
      t ≤ rho.horizon → (simTrace S rho hn).awake y t :=
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

/-! ## Characterising lemmas

The definitions above export no bodies (plan §3): other modules reason through these equations. -/

namespace Node

variable {P : Params} {A : NodeAC P}

/-- `cutPosts` of no cut. -/
theorem cutPosts_nil (self : Fin P.n) (t : Time) (st : NodeState A) :
    cutPosts self t [] st = [] := by rfl

/-- `cutPosts` of a cut and more: its post-state, then the rest from there. -/
theorem cutPosts_cons (self : Fin P.n) (t : Time) (c : Cut A) (cs : List (Cut A))
    (st : NodeState A) :
    cutPosts self t (c :: cs) st =
      cutPost self t st c :: cutPosts self t cs (cutPost self t st c) := by rfl

end Node

namespace Refinement

open Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload)

section

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- `groupRecs` unfolded: the handler's cuts zipped with their post-states, indexed by
position. -/
theorem groupRecs_eq (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp ro)) (t : Time) (id : Nat)
    (e : Event (goldilocksNode sp ro)) :
    groupRecs proposer dg self st t id e =
      ((exec proposer dg self st t e).2.zip
        (cutPosts self t (exec proposer dg self st t e).2 st)).mapIdx
        fun k cp => ⟨self, t, id, k, cp.1, cp.2⟩ := by rfl

/-- `deliverRecs` of no object. -/
theorem deliverRecs_nil (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat)
    (st : NodeState (goldilocksNode sp ro)) (sub : Nat) :
    deliverRecs proposer dg hs self t i [] st sub = [] := by rfl

/-- `deliverRecs` of a canonical object and more: its group, then the rest from the handler's
state. -/
theorem deliverRecs_cons_some (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat) (o : Wire sp.n)
    (os : List (Wire sp.n)) (st : NodeState (goldilocksNode sp ro)) (sub : Nat)
    (e : Event (goldilocksNode sp ro)) (he : canonEvent sp ro hs o = some e) :
    deliverRecs proposer dg hs self t i (o :: os) st sub =
      groupRecs proposer dg self st t (Nat.pair i sub) e ++
        deliverRecs proposer dg hs self t i os (exec proposer dg self st t e).1 (sub + 1) := by
  simp only [deliverRecs, he]

/-- `deliverRecs` of a dropped object and more: the rest, at the next sub-event index. -/
theorem deliverRecs_cons_none (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat) (o : Wire sp.n)
    (os : List (Wire sp.n)) (st : NodeState (goldilocksNode sp ro)) (sub : Nat)
    (he : canonEvent sp ro hs o = none) :
    deliverRecs proposer dg hs self t i (o :: os) st sub =
      deliverRecs proposer dg hs self t i os st (sub + 1) := by
  simp only [deliverRecs, he]

/-- A canonical message in a recursive receipt has an actual AC message cut,
even when its vote is already present or rejected by the pool cap. -/
theorem deliverRecs_message_call (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat)
    (m : Vote sp.n) :
    ∀ (os : List (Wire sp.n)) (st : NodeState (goldilocksNode sp ro)) (sub : Nat),
    (∃ o ∈ os, canonEvent sp ro hs o = some (.message m)) →
    ∃ r ∈ deliverRecs proposer dg hs self t i os st sub,
      ∃ ℓ, r.label = .ac ℓ ∧ ℓ.call = .message m := by
  intro os
  induction os with
  | nil => intro st sub h; simp at h
  | cons o os ih =>
    intro st sub ⟨x, hx, he⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _ he]
      simp only [groupRecs, exec, onMessage, acCall, cutPosts]
      simp
    · cases ho : canonEvent sp ro hs o with
      | none =>
        rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ ho]
        exact ih st (sub + 1) ⟨x, hx, he⟩
      | some e =>
        rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _ ho]
        obtain ⟨r, hr, ℓ, hl, hm⟩ := ih (exec proposer dg self st t e).1
          (sub + 1) ⟨x, hx, he⟩
        exact ⟨r, List.mem_append_right _ hr, ℓ, hl, hm⟩

end

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- The cuts of an engine tick at a public time: the node's tick group. -/
theorem eventCuts_tick_public (i : Nat) (v : V) (t : Time)
    (he : rho.events[i]? = some (.tick v t)) (hp : (S.params (pubOf E) hn).toParams.IsPublic t) :
    eventCuts S rho hn i =
      groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t))) := by
  simp only [eventCuts, he, hp, ↓reduceIte]

/-- An engine tick at a non-public time has no cut. -/
theorem eventCuts_tick_other (i : Nat) (v : V) (t : Time)
    (he : rho.events[i]? = some (.tick v t))
    (hp : ¬ (S.params (pubOf E) hn).toParams.IsPublic t) : eventCuts S rho hn i = [] := by
  simp only [eventCuts, he, hp, ↓reduceIte]

/-- The cuts of an engine delivery: `deliverRecs` of its delivered objects. -/
theorem eventCuts_deliver (i : Nat) (v : V) (o : (Model.protoOf (compiled (family S)) E).Object)
    (t : Time) (he : rho.events[i]? = some (.deliver v o t)) :
    eventCuts S rho hn i =
      deliverRecs (runProposer S rho hn) (digestOf S rho)
        (Model.digests rho.hash o) (rho.ownKey v) t i
        (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn v i).node 0 := by
  simp only [eventCuts, he]

/-- The cuts of an engine restart: the node's restart group. -/
theorem eventCuts_restart (i : Nat) (v : V) (t : Time)
    (he : rho.events[i]? = some (.restart v t)) :
    eventCuts S rho hn i =
      groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0)
        .restart := by
  simp only [eventCuts, he]

/-- The cut map steps by the number of cuts of the event. -/
theorem cutMap_succ (i : Nat) :
    cutMap S rho hn (i + 1) = cutMap S rho hn i + (eventCuts S rho hn i).length := by rfl

/-- `allCuts` unfolded: the cuts of the events in order. -/
theorem allCuts_eq :
    allCuts S rho hn = (List.range rho.events.length).flatMap (eventCuts S rho hn) := by rfl

/-- `cutTime` unfolded. -/
theorem cutTime_eq (k : Nat) :
    cutTime S rho hn k = ((allCuts S rho hn)[k]?).elim (rho.horizon + 1) CutRec.time := by rfl

/-- `cutLabel` unfolded. -/
theorem cutLabel_eq (k : Nat) :
    cutLabel S rho hn k = ((allCuts S rho hn)[k]?).map CutRec.label := by rfl

omit [DecidableEq V] in
/-- `awakeAt` unfolded. -/
theorem awakeAt_iff (y : Fin (Fintype.card V)) (t : Time) :
    awakeAt S rho hn y t ↔
      E.awake (rho.key y) t = true ∧ 0 ≤ t ∧
        t ≤ rho.horizon := Iff.rfl

/-- The node of a cut of the trace. -/
theorem simTrace_node (k : Nat) :
    (simTrace S rho hn).node k = ((allCuts S rho hn)[k]?).elim ⟨0, hn⟩ CutRec.node := by rfl

/-- The time of a cut of the trace. -/
theorem simTrace_time (k : Nat) :
    (simTrace S rho hn).time k =
      ((allCuts S rho hn)[k]?).elim (rho.horizon + 1) CutRec.time := by rfl

/-- The event id of a cut of the trace. -/
theorem simTrace_event (k : Nat) :
    (simTrace S rho hn).event k =
      ((allCuts S rho hn)[k]?).elim (Nat.pair rho.events.length k) CutRec.event := by rfl

/-- The position of a cut of the trace. -/
theorem simTrace_pos (k : Nat) :
    (simTrace S rho hn).pos k = ((allCuts S rho hn)[k]?).elim 0 CutRec.pos := by rfl

/-- The label of a cut of the trace. -/
theorem simTrace_label (k : Nat) :
    (simTrace S rho hn).label k = ((allCuts S rho hn)[k]?).map CutRec.label := by rfl

/-- The post-state of a cut of the trace. -/
theorem simTrace_post (k : Nat) :
    (simTrace S rho hn).post k = ((allCuts S rho hn)[k]?).elim (Node.init _) CutRec.post := by rfl

end Refinement

end Consensus.Goldilocks

end
