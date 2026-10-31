module
public import ConsensusLean.Instances.Goldilocks.Statements.Refinement.Interface
public import ConsensusLean.Lemmas.Model.Candidates
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.EngineSteps

public section

/-! # Publication contracts for the revised publisher

OPEN implementation arguments, not paper proofs. The paper's forwarding rule motivates these
interfaces but does not prove engine candidate ordering or signed-object provenance. In
particular installing the signed publisher does not prove these contracts. The Accepted
assembly must construct an implementation and discharge every field, never assume this bundle
as an additional regime premise. Parameters remain explicit until run-selected simulation lands.
-/

namespace Consensus.Goldilocks.Refinement

open Shape Blocks
open Consensus.Model

/-- Abstract publisher state, separate from the installed runtime state. The map
survives restarts; pending wrappers are drained in acceptance order before the event ends.
OPEN implementation: connecting this state to `State`, actual duties and own proposals. -/
structure ForwardingState (n : Nat) where
  wrappers : Nat → Option (Wire n)
  pending : List (Wire n)

/-- Revised publication transition: remember the exact wrapper and append it to the same-event
drain. Resolve the parent from the durable map, never from a raw parent object. A missing
non-genesis parent fails explicitly; proving this cannot occur on actual acceptance is OPEN.
Callers must establish canonical acceptance first. This is not an installed engine handler. -/
def ForwardingState.enqueue {sp : SA.SAParams} (st : ForwardingState sp.n)
    (origin : Fin sp.n) (t : Time) (B : Blk sp) :
    Option (ForwardingState sp.n) := do
  let root ← B.parent
  let parent ← if root = sp.genesisRoot then some none
    else (st.wrappers root).map some
  let o := forwardObj sp origin t parent B
  return ⟨Function.update st.wrappers B.root (some o), st.pending ++ [o]⟩

/-- Drain the entire event queue in one ordered engine release batch, retaining the durable
map and clearing only the queue. Parent wrappers queued earlier become available to later
guards through `releaseAll`'s seen update. Integration as an executed signed batch is OPEN. -/
noncomputable def ForwardingState.drain {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E)
    (st : ForwardingState (Fintype.card V)) (origin : Fin (Fintype.card V))
    (nd : Model.Node (protoOf (compiled (family S)) E)) :
    ForwardingState (Fintype.card V) ×
      (Model.Node (protoOf (compiled (family S)) E) × List (Wire (Fintype.card V))) :=
  (⟨st.wrappers, []⟩,
    Model.releaseAll (protoOf (compiled (family S)) E) rho.hash origin nd st.pending)

/-- A drain clears pending traffic but keeps the canonical wrapper map. This is a local
producer-state fact, not a release guarantee or a theorem about engine restarts. -/
theorem ForwardingState.drain_persistent {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E)
    (st : ForwardingState (Fintype.card V)) (origin : Fin (Fintype.card V))
    (nd : Model.Node (protoOf (compiled (family S)) E)) :
    (st.drain S rho origin nd).1.wrappers = st.wrappers ∧
      (st.drain S rho origin nd).1.pending = [] := by
  exact ⟨rfl, rfl⟩

/-- A newly queued candidate comes from this acceptance, at the current clock, using
either genesis or the exact parent wrapper already in the durable map. Missing parents
do not manufacture candidates. This local fact does not assume the parent exists. -/
theorem queueAccepted_forward_origin {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (B : Blk sp)
    (q : Time × List (Wire sp.n)) (hq : q ∈ (queueAccepted st B).forwards) :
    q ∈ st.forwards ∨ ∃ root p, B.parent = some root ∧
      (if root = sp.genesisRoot then some none else (st.wrappers root).map some) = some p ∧
      q = (st.now, p.toList ++ [blockObj sp B]) := by
  unfold queueAccepted at hq
  split at hq
  · exact Or.inl hq
  · rename_i root hroot
    cases hp : (if root = sp.genesisRoot then some none else
        (st.wrappers root).map some) with
    | none => simp only [hp] at hq; exact Or.inl hq
    | some p =>
      simp only [hp] at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact Or.inl hq
      · exact Or.inr ⟨root, p, hroot, hp, List.mem_singleton.mp hq⟩

/-- The publisher clock is unchanged while constructing a wrapper. -/
theorem queueAccepted_now {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (B : Blk sp) :
    (queueAccepted st B).now = st.now := by
  unfold queueAccepted
  split
  · rfl
  · dsimp only
    split <;> rfl

/-- A parent available in the durable map is used exactly, and the fresh wrapper is
remembered before subsequent acceptance cuts are processed. This is the local
parent-first step, not the reachable-state theorem ensuring the parent is available. -/
theorem queueAccepted_of_parent {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (B : Blk sp)
    (root : Nat) (p : Option (Wire sp.n)) (hr : B.parent = some root)
    (hp : (if root = sp.genesisRoot then some none else
      (st.wrappers root).map some) = some p) :
    (queueAccepted st B).wrappers =
      Function.update st.wrappers B.root (some (forwardObj sp st.self st.now p B)) ∧
    (queueAccepted st B).forwards = st.forwards ++ [(st.now, p.toList ++ [blockObj sp B])] := by
  simp [queueAccepted, hr, hp]

/-- Every fresh pending wrapper in a handler result has a successful block-acceptance cut
in that very result, with the handler's clock. Fold induction preserves the original
clock and retains list membership, including multiple accepts within one event. -/
theorem apply_forward_origin {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro)
    (r : NodeState (goldilocksNode sp ro) × List (Cut (goldilocksNode sp ro)))
    (q : Time × List (Wire sp.n)) (hq : q ∈ (apply st r).forwards) :
    q ∈ st.forwards ∨ ∃ B, ∃ p : Option (Wire sp.n), .fg (.block B true) ∈ r.2 ∧
      q = (st.now, p.toList ++ [blockObj sp B]) := by
  have hfold : ∀ (cs : List (Cut (goldilocksNode sp ro))) (s : State sp ro),
      q ∈ (cs.foldl (fun s c => match c with
        | .fg (.block B true) => queueAccepted s B | _ => s) s).forwards →
      q ∈ s.forwards ∨ ∃ B, ∃ p : Option (Wire sp.n), .fg (.block B true) ∈ cs ∧
        q = (s.now, p.toList ++ [blockObj sp B]) := by
    intro cs
    induction cs with
    | nil => intro s h; exact Or.inl h
    | cons c cs ih =>
      intro s h
      simp only [List.foldl_cons] at h
      cases c with
      | ac _ =>
        rcases ih s h with h | ⟨B, p, hm, he⟩
        · exact Or.inl h
        · exact Or.inr ⟨B, p, List.mem_cons_of_mem _ hm, he⟩
      | fg c =>
        cases c with
        | attest src signed =>
          rcases ih s h with h | ⟨B, p, hm, he⟩
          · exact Or.inl h
          · exact Or.inr ⟨B, p, List.mem_cons_of_mem _ hm, he⟩
        | attestation a =>
          rcases ih s h with h | ⟨B, p, hm, he⟩
          · exact Or.inl h
          · exact Or.inr ⟨B, p, List.mem_cons_of_mem _ hm, he⟩
        | block B accepted =>
          cases accepted with
          | false =>
            rcases ih s h with h | ⟨B, p, hm, he⟩
            · exact Or.inl h
            · exact Or.inr ⟨B, p, List.mem_cons_of_mem _ hm, he⟩
          | true =>
            rcases ih (queueAccepted s B) h with h | ⟨B', p, hm, he⟩
            · rcases queueAccepted_forward_origin s B q h with h | ⟨root, p, _, _, he⟩
              · exact Or.inl h
              · exact Or.inr ⟨B, p, List.mem_cons_self, he⟩
            · exact Or.inr ⟨B', p, List.mem_cons_of_mem _ hm,
                by simpa only [queueAccepted_now] using he⟩
  exact hfold r.2 st hq

/-- The durable wrapper-map invariant required at a block call: each held non-genesis
root has an own wrapper. This local invariant is to be proved along execution, never
added to the generic Accepted or network premises. -/
def WrappersCover {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) : Prop :=
  ∀ root, root ≠ sp.genesisRoot → (st.node.fg.blocks root).isSome →
    (st.wrappers root).isSome

/-- An actual successful block call cannot miss its parent wrapper when the map covers
held roots. The store's acceptance guard supplies a held parent; genesis needs no wrapper.
The node handler emits the acceptance before its AC cut, which cannot enqueue a block. -/
theorem onBlock_queues_acceptance {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (B : Blk sp)
    (hcover : WrappersCover st)
    (hacc : .fg (.block B true) ∈ (Node.onBlock st.self st.node st.now B).2) :
    ∃ p : Option (Wire sp.n),
      (apply st (Node.onBlock st.self st.node st.now B)).forwards =
        st.forwards ++ [(st.now, p.toList ++ [blockObj sp B])] := by
  unfold Node.onBlock at hacc ⊢
  split at hacc
  · simp at hacc
  · rename_i htime
    simp only [htime, ↓reduceIte]
    split at hacc
    · simp at hacc
    · rename_i fg' hfg
      rw [hfg]
      obtain ⟨root, _, hr, _, hheld, _, _, _⟩ := Store.onBlock_eq_some hfg
      have hp : ∃ p : Option (Wire sp.n),
          (if root = sp.genesisRoot then some none else (st.wrappers root).map some) =
            some p := by
        by_cases hg : root = sp.genesisRoot
        · exact ⟨none, ite_eq_left hg⟩
        · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hcover root hg hheld)
          exact ⟨some p, by simp only [hg, ↓reduceIte, hp, Option.map_some]⟩
      obtain ⟨p, hp⟩ := hp
      refine ⟨p, ?_⟩
      change (queueAccepted st B).forwards = _
      exact (queueAccepted_of_parent st B root p hr hp).2

/-- A successful block call grows the held-block map and wrapper map at the same root.
All other roots keep their existing wrappers; refusal leaves both maps unchanged. -/
theorem wrappersCover_onBlock {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (B : Blk sp)
    (hcover : WrappersCover st) :
    WrappersCover (apply st (Node.onBlock st.self st.node st.now B)) := by
  unfold Node.onBlock
  split
  · exact hcover
  · split
    · exact hcover
    · rename_i fg' hfg
      obtain ⟨root, σ, hr, _, hheld, _, _, hstore⟩ := Store.onBlock_eq_some hfg
      have hp : ∃ p : Option (Wire sp.n),
          (if root = sp.genesisRoot then some none else (st.wrappers root).map some) =
            some p := by
        by_cases hg : root = sp.genesisRoot
        · exact ⟨none, ite_eq_left hg⟩
        · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hcover root hg hheld)
          exact ⟨some p, by simp only [hg, ↓reduceIte, hp, Option.map_some]⟩
      obtain ⟨p, hp⟩ := hp
      have hw := (queueAccepted_of_parent st B root p hr hp).1
      have hb : fg'.blocks = Function.update st.node.fg.blocks B.root (some B) := by
        rw [hstore]
        obtain ⟨atts, he⟩ := Store.addAtts_eq _ B.fgPayload
        rw [he]
        exact (Store.updateFinality_spec _ σ).1
      intro r hrg hheld'
      change (fg'.blocks r).isSome at hheld'
      change ((queueAccepted st B).wrappers r).isSome
      rw [hw]
      rw [hb] at hheld'
      by_cases he : r = B.root
      · subst r
        simp
      · rw [Function.update_of_ne he] at hheld' ⊢
        exact hcover r hrg hheld'

private theorem wrappersCover_recordOwn {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) o hs
    (h : WrappersCover st) : WrappersCover (recordOwn st o hs) := by
  unfold recordOwn
  split
  · exact h
  · split
    · exact wrappersCover_onBlock _ _ h
    · exact h
  · exact h

private theorem wrappersCover_processOne {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) o hs
    (h : WrappersCover st) : WrappersCover (processOne hs st o) := by
  unfold processOne
  split
  · unfold relayIf
    dsimp only
    split <;> exact wrappersCover_onBlock _ _ h
  · unfold relayIf
    dsimp only
    split <;> exact h
  · rename_i a _
    obtain ⟨atts, he⟩ := Store.onAttestation_eq st.node.fg a
    simpa [relayIf, apply, Node.onAttestation, he, WrappersCover] using h
  · exact h

private theorem wrappersCover_fgUpdate {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro)
    (h : WrappersCover st) : WrappersCover (fgUpdate st) := by
  unfold fgUpdate
  dsimp only
  split
  · exact h
  · split
    · exact h
    · rename_i a record _
      obtain ⟨atts, he⟩ := Store.onAttestation_eq st.node.fg a
      simpa [Node.acToFG, Node.onAttestation, he, WrappersCover] using h

private theorem wrappersCover_poll {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) t
    (h : WrappersCover st) : WrappersCover (poll st t).1 := by
  unfold poll
  split <;> dsimp only <;> split
  all_goals first | exact h | exact wrappersCover_fgUpdate st h

private theorem wrappersCover_propose {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) s
    (h : WrappersCover st) : WrappersCover (propose st s).1 := by
  unfold propose
  dsimp only
  split <;> exact h

private theorem wrappersCover_nodeTick {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro)
    (h : WrappersCover st) : WrappersCover (nodeTick st) := by
  unfold nodeTick
  split <;> exact h

/-- The actual runtime's durable map covers every held non-genesis root at every event
boundary. Initially only genesis is held. Block acceptance updates both maps together;
all other handlers preserve them, including restart. No execution-validity assumption is
needed for this structural invariant. -/
theorem stateAt_wrappersCover {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) : ∀ i, WrappersCover (stateAt S rho hn v i)
  | 0 => by
    intro root hg hh
    change (if root = S.genesisRoot then some _ else none).isSome at hh
    simp only [show root ≠ S.genesisRoot from hg, ↓reduceIte, Option.isSome_none] at hh
    contradiction
  | i + 1 => by
    have ih := stateAt_wrappersCover S rho hn v i
    cases he : rho.events[i]? with
    | none => rw [stateAt_succ_none S rho hn v he]; exact ih
    | some ev =>
      by_cases hnode : ev.node = v
      · cases ev with
        | tick w t =>
          simp only [Model.Event.node] at hnode
          subst w
          rw [stateAt_tick S rho hn v he]
          exact tick_pres S rho hn WrappersCover wrappersCover_recordOwn
            wrappersCover_propose wrappersCover_nodeTick wrappersCover_poll v _ t ih
        | deliver w o t =>
          simp only [Model.Event.node] at hnode
          subst w
          rw [stateAt_deliver S rho hn v he]
          apply deliver_pres S rho hn WrappersCover wrappersCover_poll
            (fun st m cs hs h => wrappersCover_recordOwn st _ hs h)
          have hf : ∀ (xs : List (Wire (Fintype.card V)))
              (st : State (S.params (pubOf E) hn) (S.ro _)),
              WrappersCover st →
                WrappersCover (xs.foldl (processOne (digests rho.hash o)) st) := by
            intro xs
            induction xs with
            | nil => exact fun _ h => h
            | cons x xs hx => exact fun st h => hx _ (wrappersCover_processOne st x _ h)
          exact hf _ _ ih
        | restart w t =>
          simp only [Model.Event.node] at hnode
          subst w
          rw [stateAt_restart S rho hn v he]
          exact ih
      · rw [state_of_other S rho hn v i ev he hnode]
        exact ih

/-- One successful candidate of a release batch. `batch` orders actual batches within an event;
`index` names the candidate, including candidates rejected earlier in the batch. -/
structure Publication {pub : Public} {O : Type} (P : Protocol pub O) where
  event : Nat
  batch : Nat
  index : Nat
  origin : Key pub
  before : Model.Node P
  candidates : List P.Object
  object : P.Object
  candidate : candidates[index]? = some object

/-- Lexicographic release order; equal timestamps need not imply equal occurrences. -/
def Publication.Before {pub : Public} {O : Type} {P : Protocol pub O}
    (a b : Publication P) : Prop :=
  a.event < b.event ∨ a.event = b.event ∧
    (a.batch < b.batch ∨ a.batch = b.batch ∧ a.index < b.index)

/-- The publisher's linkage to actual execution. `actual` must be implemented from executed
duty/release batches, not chosen to make publication claims vacuous. `publisherExecution`
below supplies that linkage without assuming any acceptance provenance. -/
structure PublisherExecution {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) where
  actual : Publication (protoOf (compiled (family S)) E) → Prop
  eventTime : Nat → Time
  actual_event : ∀ r, actual r → rho.SendsAt (rho.key r.origin) r.event (eventTime r.event)
  actual_success : ∀ r, actual r →
    let nd := (Model.releaseAll (protoOf (compiled (family S)) E) rho.hash r.origin
      r.before (r.candidates.take r.index)).1
    Model.releasable nd.seen r.object = true ∧
      Model.protects (protoOf (compiled (family S)) E) r.origin nd.seen r.object = true ∧
      (protoOf (compiled (family S)) E).dependencies.ready (Model.closure nd.seen) r.object = true
  actual_release : ∀ r, actual r → r.object ∈ rho.releasesAt r.event

/-- A batch input and candidate list, before applying its release guard. -/
structure ReleaseBatch {pub : Public} {O : Type} (P : Protocol pub O) where
  before : Model.Node P
  candidates : List P.Object

/-- Enumerate actual selected duty batches, threading the same `dutyStep` states as the
engine. Empty/unselected duties retain their ordinal position as an empty batch. -/
noncomputable def dutyBatches {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {O : OutputSchema} {F : Family O} (rho : Model.Run F E) (v : V) :
    Model.Node (protoOf F E) → List (protoOf F E).Duty → List (ReleaseBatch (protoOf F E))
  | _, [] => []
  | nd, d :: ds =>
    let a := (protoOf F E).act nd.st d
    let batch := if rho.ownKey v ∈ rho.sel ((protoOf F E).role d) then
      ⟨⟨a.1, nd.seen⟩, rho.signedCandidate v d a.2⟩ else ⟨nd, []⟩
    batch :: dutyBatches rho v (rho.dutyStep v nd d).1 ds

/-- No duties produce no release batches. -/
theorem dutyBatches_nil {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {O : OutputSchema} {F : Family O} (rho : Model.Run F E) (v : V)
    (nd : Model.Node (protoOf F E)) : dutyBatches rho v nd [] = [] := by
  rfl

/-- The next batch retains its duty position even when unselected; later batches start
from the actual duty-step result. -/
theorem dutyBatches_cons {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {O : OutputSchema} {F : Family O} (rho : Model.Run F E) (v : V)
    (nd : Model.Node (protoOf F E)) (d : (protoOf F E).Duty)
    (ds : List (protoOf F E).Duty) :
    dutyBatches rho v nd (d :: ds) =
      (let a := (protoOf F E).act nd.st d
       let batch : ReleaseBatch (protoOf F E) :=
         if rho.ownKey v ∈ rho.sel ((protoOf F E).role d) then
           ⟨⟨a.1, nd.seen⟩, rho.signedCandidate v d a.2⟩ else ⟨nd, []⟩
       batch :: dutyBatches rho v (rho.dutyStep v nd d).1 ds) := by
  rfl

/-- Actual event batches, including the final gossip batch. No synthetic batch labels are
allowed: publication indices must select an entry in this list. -/
noncomputable def eventBatches {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {O : OutputSchema} {F : Family O} (rho : Model.Run F E) (i : Nat) :
    List (ReleaseBatch (protoOf F E)) :=
  match rho.events[i]? with
  | some (.tick v t) =>
    let nd := rho.stateBefore i v
    let start := ⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩
    if E.awake v t then
      let r := rho.runDuties v start ((protoOf F E).duties t)
      dutyBatches rho v start ((protoOf F E).duties t) ++
        [⟨r.1, gossipCandidates (protoOf F E) r.1.st t⟩]
    else []
  | some (.deliver v o t) =>
    let nd := rho.stateBefore i v
    let start := ⟨(protoOf F E).process nd.st o (digests rho.hash o), nd.seen ++ [o]⟩
    let r := rho.runDuties v start ((protoOf F E).deliverDuties t)
    dutyBatches rho v start ((protoOf F E).deliverDuties t) ++
      [⟨r.1, gossipCandidates (protoOf F E) r.1.st t⟩]
  | _ => []

/-- Characterization by the actual event, without exposing the implementation body. -/
theorem eventBatches_eq {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {O : OutputSchema} {F : Family O} (rho : Model.Run F E) (i : Nat) :
    eventBatches rho i = (match rho.events[i]? with
      | some (.tick v t) =>
        let nd := rho.stateBefore i v
        let start := ⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩
        if E.awake v t then
          let r := rho.runDuties v start ((protoOf F E).duties t)
          dutyBatches rho v start ((protoOf F E).duties t) ++
            [⟨r.1, gossipCandidates (protoOf F E) r.1.st t⟩]
        else []
      | some (.deliver v o t) =>
        let nd := rho.stateBefore i v
        let start := ⟨(protoOf F E).process nd.st o (digests rho.hash o), nd.seen ++ [o]⟩
        let r := rho.runDuties v start ((protoOf F E).deliverDuties t)
        dutyBatches rho v start ((protoOf F E).deliverDuties t) ++
          [⟨r.1, gossipCandidates (protoOf F E) r.1.st t⟩]
      | _ => []) := by
  rfl

/-- A real candidate prefix: ties both its state and candidates to the engine event. -/
def ExecutedPublication {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E)
    (r : Publication (protoOf (compiled (family S)) E)) : Prop :=
  (eventBatches rho r.event)[r.batch]? = some ⟨r.before, r.candidates⟩ ∧
  ∃ t, rho.SendsAt (rho.key r.origin) r.event t

/-- A successful candidate at its actual prefix occurs in the batch output. Rejected
earlier candidates still count towards the index; induction follows the engine's guard,
so the prefix state includes exactly the successful earlier releases. -/
theorem releaseAll_candidate_success {pub : Public} {O : Type} (P : Protocol pub O)
    (hash : P.Item → Nat) (origin : Key pub) (nd : Model.Node P)
    (cs : List P.Object) (i : Nat) (o : P.Object)
    (hi : cs[i]? = some o)
    (hs : let pre := (Model.releaseAll P hash origin nd (cs.take i)).1
      Model.releasable pre.seen o = true ∧
        Model.protects P origin pre.seen o = true ∧
        P.dependencies.ready (Model.closure pre.seen) o = true) :
    o ∈ (Model.releaseAll P hash origin nd cs).2 := by
  induction cs generalizing nd i with
  | nil => simp at hi
  | cons c cs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst c
      simp only [List.take_zero, Model.releaseAll] at hs
      simp only [Model.releaseAll, hs.1, hs.2.1, hs.2.2, Bool.and_self, ↓reduceIte]
      exact List.mem_cons_self
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      simp only [List.take_succ_cons, Model.releaseAll] at hs ⊢
      split at *
      · rename_i h
        simp only [h, ↓reduceIte]
        exact List.mem_cons_of_mem _ (ih _ i hi hs)
      · rename_i h
        simp only [h]
        exact ih _ i hi hs

/-- Each enumerated duty batch releases only objects released by the actual duty list.
The induction threads the same intermediate node as `runDuties`, including unselected
duties, which have an empty batch and leave the state unchanged. -/
theorem dutyBatches_release {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {O : OutputSchema} {F : Family O} (rho : Model.Run F E) (v : V)
    (nd : Model.Node (protoOf F E)) (ds : List (protoOf F E).Duty)
    (b : ReleaseBatch (protoOf F E)) (hb : b ∈ dutyBatches rho v nd ds)
    (o : (protoOf F E).Object)
    (ho : o ∈ (Model.releaseAll (protoOf F E) rho.hash (rho.ownKey v)
      b.before b.candidates).2) :
    o ∈ (rho.runDuties v nd ds).2 := by
  induction ds generalizing nd with
  | nil => simp [dutyBatches] at hb
  | cons d ds ih =>
    rw [Model.Run.runDuties_cons]
    simp only [dutyBatches, List.mem_cons] at hb
    rcases hb with rfl | hb
    · apply List.mem_append_left
      unfold Model.Run.dutyStep
      split
      · rename_i hsel
        simpa only [hsel, ↓reduceIte] using ho
      · simp_all [Model.releaseAll]
    · exact List.mem_append_right _ (ih _ hb)

/-- Actual event batches include the duty releases and final gossip, in engine order.
Thus a release from an enumerated batch is an actual event release, not a synthetic
candidate occurrence. This covers delivery events as well as awake ticks. -/
theorem eventBatches_release {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {O : OutputSchema} {F : Family O} (rho : Model.Run F E) (v : V) (i : Nat) (t : Time)
    (he : rho.SendsAt v i t) (b : ReleaseBatch (protoOf F E))
    (hb : b ∈ eventBatches rho i) (o : (protoOf F E).Object)
    (ho : o ∈ (Model.releaseAll (protoOf F E) rho.hash (rho.ownKey v)
      b.before b.candidates).2) : o ∈ rho.releasesAt i := by
  rcases he with he | ⟨obj, he⟩
  · simp only [eventBatches, he] at hb
    simp only [Model.Run.releasesAt, he, Model.Run.tick]
    split at hb
    · rename_i hawake
      simp only [hawake, ↓reduceIte]
      rcases List.mem_append.mp hb with hb | hb
      · exact List.mem_append_left _ (dutyBatches_release rho v _ _ b hb o ho)
      · simp only [List.mem_singleton] at hb
        subst b
        exact List.mem_append_right _ ho
    · simp at hb
  · simp only [eventBatches, he] at hb
    simp only [Model.Run.releasesAt, he, Model.Run.deliver]
    rcases List.mem_append.mp hb with hb | hb
    · exact List.mem_append_left _ (dutyBatches_release rho v _ _ b hb o ho)
    · simp only [List.mem_singleton] at hb
      subst b
      exact List.mem_append_right _ ho

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
  (tr : GoldilocksTrace (S.params (pubOf E) hn) (S.ro _)) (cutMap : Nat → Nat)
  (pubExec : PublisherExecution S rho)

/-- Concrete publication relation: all executed candidates passing the three guards at
their actual prefix, with the event's own time. No provenance or acceptance claim is used
to select publications. The batch lemmas above establish the actual release field. -/
noncomputable def publisherExecution : PublisherExecution S rho where
  actual r := ExecutedPublication S rho r ∧
    let nd := (Model.releaseAll (protoOf (compiled (family S)) E) rho.hash r.origin
      r.before (r.candidates.take r.index)).1
    Model.releasable nd.seen r.object = true ∧
      Model.protects (protoOf (compiled (family S)) E) r.origin nd.seen r.object = true ∧
      (protoOf (compiled (family S)) E).dependencies.ready (Model.closure nd.seen) r.object = true
  eventTime i := (rho.events[i]?).map Model.Event.time |>.getD 0
  actual_event r hr := by
    obtain ⟨t, ht⟩ := hr.1.2
    rcases ht with ht | ⟨o, ht⟩
    · simp only [ht, Option.map_some, Option.getD_some, Model.Event.time]
      exact Or.inl ht
    · simp only [ht, Option.map_some, Option.getD_some, Model.Event.time]
      exact Or.inr ⟨o, ht⟩
  actual_success r hr := hr.2
  actual_release r hr := by
    obtain ⟨t, ht⟩ := hr.1.2
    have ho := releaseAll_candidate_success _ rho.hash r.origin r.before r.candidates
      r.index r.object r.candidate hr.2
    have hk : rho.ownKey (rho.key r.origin) = r.origin := rho.key.symm_apply_apply _
    apply eventBatches_release rho (rho.key r.origin) r.event t ht
      ⟨r.before, r.candidates⟩ (List.mem_of_getElem? hr.1.1) r.object
    simpa only [hk] using ho

/-- The concrete relation includes every executed candidate passing its actual prefix
guards, not merely a chosen subset of successful publications. -/
theorem publisherExecution_actual_iff (r : Publication (protoOf (compiled (family S)) E)) :
    (publisherExecution S rho).actual r ↔ ExecutedPublication S rho r ∧
      let nd := (Model.releaseAll (protoOf (compiled (family S)) E) rho.hash r.origin
        r.before (r.candidates.take r.index)).1
      Model.releasable nd.seen r.object = true ∧
        Model.protects (protoOf (compiled (family S)) E) r.origin nd.seen r.object = true ∧
        (protoOf (compiled (family S)) E).dependencies.ready
          (Model.closure nd.seen) r.object = true := by
  rfl

/-- Publication time is the time of the actual indexed event. -/
theorem publisherExecution_eventTime_eq (i : Nat) :
    (publisherExecution S rho).eventTime i =
      ((rho.events[i]?).map Model.Event.time).getD 0 := by
  rfl

/-- OPEN: honest signed publication must originate in actual acceptance at the stamp.
Argument: only the acceptance handler queues these candidates; authentication rules out
other honest origins. The engine digest identifies the root omitted by the wire header
(#122); wire equality alone does not identify B. This remains a producer obligation. -/
def ForwardOrigin : Prop :=
  ∀ r, pubExec.actual r → rho.key r.origin ∈ rho.honest → ∀ t p B,
    decodeForward (S.params (pubOf E) hn) (Model.digests rho.hash r.object) r.object =
      some (r.origin, t, p, B) →
    ∃ k, tr.AcceptAt r.origin k B ∧ tr.time k = t ∧
      k < cutMap (r.event + 1) ∧ t = pubExec.eventTime r.event

/-- OPEN: acceptance queues and drains a wrapper in the same event, including own proposals.
The installed producer still needs missing-parent exclusion and successful release proofs. -/
def ForwardAtAcceptance : Prop :=
  ∀ x ∈ honestKeys S rho, ∀ k B, tr.AcceptAt x k B →
    ∃ r p, pubExec.actual r ∧ r.origin = x ∧
      cutMap r.event ≤ k ∧ k < cutMap (r.event + 1) ∧
      pubExec.eventTime r.event = tr.time k ∧
      r.object = forwardObj (S.params (pubOf E) hn) x (tr.time k) p B ∧
      decodeForward (S.params (pubOf E) hn) (Model.digests rho.hash r.object) r.object =
        some (x, tr.time k, p, B)

/-- OPEN: parent references are taken from the origin's previously released wrappers;
same-event publication order is candidate order, not strict timestamp order. -/
def ForwardParentEarlier : Prop :=
  ∀ r, pubExec.actual r → rho.key r.origin ∈ rho.honest → ∀ t p B,
    decodeForward (S.params (pubOf E) hn) (Model.digests rho.hash r.object) r.object =
      some (r.origin, t, some p, B) →
    ∃ q A pt pp ka kb, pubExec.actual q ∧ Publication.Before q r ∧ q.origin = r.origin ∧
      q.object = p ∧ p = forwardObj (S.params (pubOf E) hn) r.origin pt pp A ∧
      decodeForward (S.params (pubOf E) hn) (Model.digests rho.hash p) p =
        some (r.origin, pt, pp, A) ∧
      B.parent = some A.root ∧ tr.AcceptAt r.origin ka A ∧ tr.AcceptAt r.origin kb B ∧
      ka < kb ∧ tr.time ka = pt ∧ tr.time kb = t

/-- OPEN: recursive receipt processing turns prior authenticated holdings into prior calls;
own publications instead use actual acceptance. Refused calls do not establish acceptance. -/
def ForwardHeldProcessed : Prop :=
  ∀ y ∈ honestKeys S rho, ∀ i x t p B o,
    x ∈ honestKeys S rho →
    o ∈ Model.closure (rho.stateBefore i (rho.key y)).seen →
    decodeForward (S.params (pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B) →
    ∃ k < cutMap i, t ≤ tr.time k ∧
      (tr.BlockCallAt y k B ∨ y = x ∧ tr.AcceptAt y k B)

/-- OPEN: accepted canonical objects and exact parent wrappers are in the publisher's seen
closure at the actual candidate prefix; signing and dependency guards do not suppress it. -/
def AcceptedObjectsSeen : Prop :=
  ∀ r, pubExec.actual r → rho.key r.origin ∈ rho.honest →
    let nd := (Model.releaseAll (protoOf (compiled (family S)) E) rho.hash r.origin
      r.before (r.candidates.take r.index)).1
    ∀ o ∈ r.object.carried, o ∈ Model.closure nd.seen

/-- Carried objects of successful publications were held at the actual candidate prefix.
Paper argument: this is precisely the engine's `releasable` guard, supplied by
`actual_success`. It does not establish that every acceptance produces a successful release;
that independent completeness obligation belongs to `ForwardAtAcceptance`. -/
theorem accepted_objects_seen : AcceptedObjectsSeen S rho pubExec := by
  intro r hr _
  have h := (pubExec.actual_success r hr).1
  simpa only [Model.releasable, List.all_eq_true, decide_eq_true_eq] using h

/-- The installed publisher's concrete successful occurrences satisfy the carried-object
contract. No validity, network, collision, or acceptance assumption is required for this
guard fact; existence of a successful occurrence for each acceptance remains separate. -/
theorem publisherExecution_objects_seen :
    AcceptedObjectsSeen S rho (publisherExecution S rho) :=
  accepted_objects_seen S rho (publisherExecution S rho)

/-- The five obligations the concrete revised publisher must discharge. OPEN: no complete
instance is supplied, and this is not a new Accepted assumption. -/
structure ForwardingContracts : Prop where
  executed : ∀ r, pubExec.actual r → ExecutedPublication S rho r
  /-- Completeness prevents selecting only convenient successful publications. Every actual
  executed candidate passing all three guards belongs to the publication relation. -/
  complete : ∀ r, ExecutedPublication S rho r →
    let nd := (Model.releaseAll (protoOf (compiled (family S)) E) rho.hash r.origin
      r.before (r.candidates.take r.index)).1
    Model.releasable nd.seen r.object = true →
    Model.protects (protoOf (compiled (family S)) E) r.origin nd.seen r.object = true →
    (protoOf (compiled (family S)) E).dependencies.ready (Model.closure nd.seen) r.object = true →
    pubExec.actual r
  origin : ForwardOrigin S rho hn tr cutMap pubExec
  atAcceptance : ForwardAtAcceptance S rho hn tr cutMap pubExec
  parentEarlier : ForwardParentEarlier S rho hn tr pubExec
  heldProcessed : ForwardHeldProcessed S rho hn tr cutMap
  objectsSeen : AcceptedObjectsSeen S rho pubExec

end Consensus.Goldilocks.Refinement
