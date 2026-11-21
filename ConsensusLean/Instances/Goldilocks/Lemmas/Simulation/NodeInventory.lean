module
public import ConsensusLean.Instances.Goldilocks.NodeAsChainShape
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Entries
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeOpLaws
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeInventorySchedule
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Lemmas.Model.Candidates

public section

namespace Consensus.Goldilocks.NodeAsChainShape

open Blocks Shape

variable {P : Params} {A : NodeAC P} {K I B : Type}
variable (C : WireCodec A K I B) (attObj : FG.Att P.n → ShapeObj P.n K I B)
variable {Avail : ShapeObj P.n K I B → Prop} {st : Store P A.Payload}

/-- The FG store and the material of its tree and attestation pool. -/
structure FGInventory (genesis : A.Payload) (Avail : ShapeObj P.n K I B → Prop)
    (st : Store P A.Payload) : Prop where
  reachable : st.Reachable genesis
  blocks : ∀ b ∈ st.tree, ∀ o ∈ C.carried b.fgPayload b.acPayload, Avail o
  atts : ∀ a ∈ st.atts, Avail (attObj a)

/-- Processing an available attestation does not introduce any unavailable material. -/
theorem inventory_att {genesis : A.Payload} (h : FGInventory C attObj genesis Avail st)
    (a : FG.Att P.n) (ha : Avail (attObj a)) :
    FGInventory C attObj genesis Avail (st.onAttestation a) := by
  obtain ⟨hb, _, hats⟩ := Store.onAttestation_fields st a
  refine ⟨h.reachable.tail (Or.inr ⟨a, rfl⟩), ?_, ?_⟩
  · intro b hb'
    exact h.blocks b (by
      change (st.onAttestation a).blocks b.root = some b at hb'
      rwa [hb] at hb')
  · intro b hb'
    rcases hats b hb' with hb' | rfl
    · exact h.atts b hb'
    · exact ha

/-- Accepting a block adds only material carried by that block. -/
theorem inventory_accept {genesis : A.Payload} (h : FGInventory C attObj genesis Avail st)
    {b : A.Blk} {st' : Store P A.Payload} (hacc : st.onBlock b = some st')
    (hb : ∀ o ∈ C.carried b.fgPayload b.acPayload, Avail o)
    (hatt : ∀ a ∈ b.fgPayload, attObj a ∈ C.carried b.fgPayload b.acPayload) :
    FGInventory C attObj genesis Avail st' := by
  obtain ⟨_, _, _, _, _, _, _, _, hatts⟩ := Store.onBlock_fields hacc
  refine ⟨h.reachable.tail (Or.inl ⟨b, hacc⟩), ?_, ?_⟩
  · intro c hc
    rw [(Store.tree_grows P A.Payload genesis st h.reachable).1 b st' hacc] at hc
    rcases hc with rfl | hc
    · exact hb
    · exact h.blocks c hc
  · intro a ha
    rcases hatts a ha with ha | ha
    · exact h.atts a ha
    · exact hb _ (hatt a ha)

end Consensus.Goldilocks.NodeAsChainShape

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Shape Model

variable {V : Type} [Fintype V] {E : Env V}
variable {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
variable {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
variable {hn : 1 ≤ Fintype.card V}
variable {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)}
variable (e : Encoding F E p hN hn A) (rho : Model.Run (compiled F) E)

/-- The engine protocol obtained by compiling a shape family for an environment. -/
abbrev Engine (F : ChainShapeFamily O I) (E : Env V) := Model.protoOf (compiled F) E

/-- A rejected release keeps the current state; an accepted release records and appends it. -/
theorem release_envelope_cons (k : Fin (Fintype.card V)) (nd : Model.Node (Engine F E))
    (o : (Engine F E).Object) (os : List (Engine F E).Object) :
    let r := Model.releaseAll (Engine F E) rho.hash k nd (o :: os)
    (envelope e r.1, r.1.seen, r.2) =
      if Model.releasable nd.seen o &&
          (Engine F E).dependencies.ready (Model.closure nd.seen) o then
        let next : Model.Node (Engine F E) :=
          ⟨(Engine F E).recordOwn nd.st o (Model.digests rho.hash o), nd.seen ++ [o]⟩
        let tail := Model.releaseAll (Engine F E) rho.hash k next os
        (envelope e tail.1, tail.1.seen, o :: tail.2)
      else
        let tail := Model.releaseAll (Engine F E) rho.hash k nd os
        (envelope e tail.1, tail.1.seen, tail.2) := by
  dsimp only
  by_cases h : (Model.releasable nd.seen o &&
      (Engine F E).dependencies.ready (Model.closure nd.seen) o) = true
  · simp only [Model.releaseAll, h, ite_true]
  · simp only [Model.releaseAll, h, Bool.false_eq_true, ite_false]

/-- A raw tick always clocks, including when asleep; an awake tick runs duties and gossip. -/
theorem tick_envelope (nd : Model.Node (Engine F E)) (v : V) (t : Time) :
    let r := rho.tick nd v t
    (envelope e r.1, r.2) =
      if E.awake v t then
        let ds := rho.runDuties v (afterClock rho nd v t) ((Engine F E).duties t)
        let gs := Model.releaseAll (Engine F E) rho.hash (rho.ownKey v) ds.1
          (Model.gossipCandidates (Engine F E) ds.1.st t)
        (envelope e gs.1, ds.2 ++ gs.2)
      else (envelope e (afterClock rho nd v t), []) := by
  dsimp only
  rw [afterClock_eq, Model.Run.tick]
  split <;> rfl

/-- A raw delivery starts its duty fold from the post-process state, then gossips. -/
theorem deliver_envelope (nd : Model.Node (Engine F E)) (v : V)
    (o : (Engine F E).Object) (t : Time) :
    let post : Model.Node (Engine F E) :=
      ⟨(Engine F E).process nd.st o (Model.digests rho.hash o), nd.seen ++ [o]⟩
    let ds := rho.runDuties v post ((Engine F E).deliverDuties t)
    let gs := Model.releaseAll (Engine F E) rho.hash (rho.ownKey v) ds.1
      (Model.gossipCandidates (Engine F E) ds.1.st t)
    (envelope e (rho.deliver nd v o t).1, (rho.deliver nd v o t).2) =
      (envelope e gs.1, ds.2 ++ gs.2) := by
  rfl

/-- An unselected duty does nothing; a selected duty releases from the post-act state. -/
theorem duty_envelope (v : V) (nd : Model.Node (Engine F E)) (d : (Engine F E).Duty) :
    (envelope e (rho.dutyStep v nd d).1, (rho.dutyStep v nd d).2) =
      if rho.ownKey v ∈ rho.sel ((Engine F E).role d) then
        let act := (Engine F E).act nd.st d
        let out := Model.releaseAll (Engine F E) rho.hash (rho.ownKey v) ⟨act.1, nd.seen⟩
          (rho.signedCandidate v d act.2)
        (envelope e out.1, out.2)
      else (envelope e nd, []) := by
  rw [rho.dutyStep_eq]
  split <;> rfl

/-- The duty fold exposes its first step and does not reorder what was released. -/
theorem duties_envelope_cons (v : V) (nd : Model.Node (Engine F E))
    (d : (Engine F E).Duty) (ds : List (Engine F E).Duty) :
    let start := rho.dutyStep v nd d
    let tail := rho.runDuties v start.1 ds
    (envelope e (rho.runDuties v nd (d :: ds)).1, (rho.runDuties v nd (d :: ds)).2) =
      (envelope e tail.1, start.2 ++ tail.2) := by
  dsimp only
  rw [rho.runDuties_cons]

variable [DecidableEq V]

/-- Read the next cut at its own event, or keep the envelope at an unrelated or absent event. -/
theorem stateAt_succ_envelope (v : V) (i : Nat) :
    stateAt e rho v (i + 1) =
      match rho.events[i]? with
      | none => stateAt e rho v i
      | some ev => envelope e (rho.step (rho.stateBefore i) ev v) := by
  cases he : rho.events[i]? with
  | none =>
    rw [Encoding.OpLaws.cut_envelope, Encoding.OpLaws.cut_envelope]
    simp only [Model.Run.stateBefore, List.take_add_one, he, Option.toList_none, List.append_nil]
  | some ev => rw [Encoding.OpLaws.cut_envelope, rho.stateBefore_succ he]

omit [DecidableEq V] in
/-- A pending carried object may still be queued if it is already in the sender's closure. -/
theorem releasable_of_carried_available (nd : Model.Node (Engine F E)) (o : (Engine F E).Object)
    (Pending : e.State hn → (Engine F E).Object → Prop)
    (available : ∀ x ∈ o.carried, x ∈ Model.closure nd.seen ∨ Pending (envelope e nd) x)
    (drained : ∀ x ∈ o.carried, Pending (envelope e nd) x → x ∈ Model.closure nd.seen) :
    Model.releasable nd.seen o = true :=
  List.all_eq_true.mpr fun x hx => decide_eq_true ((available x hx).elim id (drained x hx))

/-- A local invariant carried by the immediately preceding duty prefix of an actual event. -/
inductive DutyPrefix (v : V) (i j : Nat) :
    Model.Node (Engine F E) → List (Engine F E).Duty → Prop where
  | tick {t} (he : rho.events[i]? = some (.tick v t)) (hw : E.awake v t = true) :
      DutyPrefix v i j (rho.runDuties v (afterClock rho (rho.stateBefore i v) v t)
        (((Engine F E).duties t).take j)).1 ((Engine F E).duties t)
  | deliver {t o} (he : rho.events[i]? = some (.deliver v o t)) :
      DutyPrefix v i j (rho.runDuties v
        ⟨(Engine F E).process (rho.stateBefore i v).st o (Model.digests rho.hash o),
          (rho.stateBefore i v).seen ++ [o]⟩ (((Engine F E).deliverDuties t).take j)).1
        ((Engine F E).deliverDuties t)

omit [DecidableEq V] in
/-- Prove preservation over the release fold; the local law is needed only on success. -/
theorem release_inventory {Inv : Model.Node (Engine F E) → Prop}
    {Admissible : (Engine F E).Object → Prop}
    (k : Fin (Fintype.card V)) (nd : Model.Node (Engine F E)) (cs : List (Engine F E).Object)
    (record : ∀ nd c, Inv nd → Admissible c →
      Inv ⟨(Engine F E).recordOwn nd.st c (Model.digests rho.hash c), nd.seen ++ [c]⟩)
    (h : Inv nd) (hc : ∀ o ∈ cs, Admissible o) :
    Inv (Model.releaseAll (Engine F E) rho.hash k nd cs).1 := by
  induction cs generalizing nd with
  | nil => exact h
  | cons c cs ih =>
    rw [Model.releaseAll]
    split
    · exact ih _ (record nd c h (hc c List.mem_cons_self))
        (fun o ho => hc o (List.mem_cons_of_mem _ ho))
    · exact ih nd h (fun o ho => hc o (List.mem_cons_of_mem _ ho))

omit [DecidableEq V] in
/-- Extend an inventory through the actual duty prefixes of a tick or delivery. -/
theorem prefix_inventory {Inv : Model.Node (Engine F E) → Prop} {v : V}
    (nd : Model.Node (Engine F E)) (ds : List (Engine F E).Duty)
    (AtPrefix : Nat → Model.Node (Engine F E) → Prop)
    (hprefix : ∀ j, j ≤ ds.length → AtPrefix j (rho.runDuties v nd (ds.take j)).1)
    (duty : ∀ j n d, AtPrefix j n → ds[j]? = some d →
      Inv n → Inv (rho.dutyStep v n d).1)
    (h : Inv nd) (j : Nat) (hj : j ≤ ds.length) :
    Inv (rho.runDuties v nd (ds.take j)).1 := by
  induction j with
  | zero => exact h
  | succ j ih =>
    have hlt : j < ds.length := hj
    have hd := List.getElem?_eq_getElem hlt
    rw [List.take_add_one, hd, Option.toList_some, Encoding.OpLaws.runDuties_append,
      rho.runDuties_cons, rho.runDuties_nil]
    exact duty j _ _ (hprefix j hlt.le) hd (ih hlt.le)

/-- The event induction uses local laws at the actual operation, not an invariant at every cut. -/
theorem event_inventory {Inv : Model.Node (Engine F E) → Prop}
    {Admissible : (Engine F E).Object → Prop}
    (v : V) (hv : rho.ExecutionValid) (init : Inv (rho.initWorld v))
    (clock : ∀ nd t, 0 ≤ t → Inv nd → Inv (afterClock rho nd v t))
    (process : ∀ nd o, Inv nd → Inv
      ⟨(Engine F E).process nd.st o (Model.digests rho.hash o), nd.seen ++ [o]⟩)
    (restore : ∀ nd t, 0 ≤ t → Inv nd → Inv
      ⟨(Engine F E).restore (rho.ownKey v) ((Engine F E).durable nd.st) t, nd.seen⟩)
    (record : ∀ nd c, Inv nd → Admissible c →
      Inv ⟨(Engine F E).recordOwn nd.st c (Model.digests rho.hash c), nd.seen ++ [c]⟩)
    (gossip : ∀ (nd : Model.Node (Engine F E)) t o,
      o ∈ Model.gossipCandidates (Engine F E) nd.st t → Admissible o)
    (duty : ∀ i j n ds d, DutyPrefix rho v i j n ds → ds[j]? = some d →
      Inv n → Inv (rho.dutyStep v n d).1) :
    ∀ i, Inv (rho.stateBefore i v) := by
  have hg : ∀ nd t, Inv nd → Inv (Model.releaseAll (Engine F E) rho.hash (rho.ownKey v) nd
      (Model.gossipCandidates (Engine F E) nd.st t)).1 := fun nd t h =>
    release_inventory rho _ nd _ record h (gossip nd t)
  intro i
  induction i with
  | zero => exact init
  | succ i ih =>
    cases he : rho.events[i]? with
    | none =>
      simpa only [Model.Run.stateBefore, List.take_add_one, he, Option.toList_none,
        List.append_nil] using ih
    | some ev =>
      have ht := (hv.in_horizon ev (List.mem_of_getElem? he)).1
      rw [rho.stateBefore_succ he]
      cases ev with
      | tick u t =>
        by_cases hu : v = u
        · subst u
          have hc := clock _ t ht ih
          simp only [Model.Run.step, Function.update_self, Model.Run.tick]
          rw [← afterClock_eq]
          split
          · rename_i hw
            apply hg
            simpa only [List.take_length] using prefix_inventory rho
              (afterClock rho (rho.stateBefore i v) v t) ((Engine F E).duties t)
              (fun j n => DutyPrefix rho v i j n ((Engine F E).duties t))
              (fun j _ => .tick he hw) (fun j n d => duty i j n _ d) hc _ (Nat.le_refl _)
          · exact hc
        · simpa only [Model.Run.step, Function.update_of_ne hu] using ih
      | deliver u o t =>
        by_cases hu : v = u
        · subst u
          simp only [Model.Run.step, Function.update_self, Model.Run.deliver]
          apply hg
          simpa only [List.take_length] using prefix_inventory rho _ ((Engine F E).deliverDuties t)
            (fun j n => DutyPrefix rho v i j n ((Engine F E).deliverDuties t))
            (fun j _ => .deliver he) (fun j n d => duty i j n _ d)
            (process _ o ih) _ (Nat.le_refl _)
        · simpa only [Model.Run.step, Function.update_of_ne hu] using ih
      | restart u t =>
        by_cases hu : v = u
        · subst u
          simp only [Model.Run.step, Function.update_self]
          exact restore _ t ht ih
        · simpa only [Model.Run.step, Function.update_of_ne hu] using ih

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace
