module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Interface
public import ConsensusLean.Lemmas.Model.Candidates
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ForwardingState
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EngineSteps
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outbox

public section

/-! # Forwarding queue and wrapper-map invariants of the revised publisher

Implementation invariants of the forwarding runtime, not paper proofs: a newly queued candidate
comes from this acceptance (`queueAccepted_forward_origin`), every durable wrapper has an earlier
publication witness or a pending envelope (`WrappersAccounted`), each pending envelope carries
only objects held before its queue position (`PendingReady`), and the durable wrapper map covers
every held non-genesis root at every event boundary (`WrappersCover`, `stateAt_wrappersCover`).
`Forwarding` states the publication contracts on them. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Shape Blocks
open Consensus.Model

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

/-- The immutable signed forwarding queue, before a poll clears its returned state. -/
def pendingWrappers {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (st : State sp ro) : List (Wire sp.n) :=
  st.forwards.map fun q => .mk (.signed st.self .poll) (.data (.forward q.1)) q.2

/-- The signed queue preserves the order of the runtime's pending payloads. -/
theorem pendingWrappers_eq {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (st : State sp ro) : pendingWrappers st =
      st.forwards.map (fun q => .mk (.signed st.self .poll) (.data (.forward q.1)) q.2) := by
  rfl

/-- Every durable entry has either an earlier publication witness (`prior`) or an exact
pending envelope. Parent-before-child ordering and child holdings are separate obligations. -/
def WrappersAccounted {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (prior : Wire sp.n → Prop) (st : State sp ro) : Prop :=
  ∀ root o, st.wrappers root = some o → prior o ∨ o ∈ pendingWrappers st

/-- Characterize the map/queue invariant without exporting its definition body. -/
theorem wrappersAccounted_iff {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (prior : Wire sp.n → Prop)
    (st : State sp ro) : WrappersAccounted prior st ↔
      ∀ root o, st.wrappers root = some o → prior o ∨ o ∈ pendingWrappers st := by
  rfl

/-- Enqueue preserves exact durable-entry provenance, retaining the new envelope as
pending rather than prematurely counting it as published. -/
theorem wrappersAccounted_queueAccepted {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (prior : Wire sp.n → Prop)
    (st : State sp ro) (B : Blk sp) (h : WrappersAccounted prior st) :
    WrappersAccounted prior (queueAccepted st B) := by
  rw [wrappersAccounted_iff] at h ⊢
  unfold queueAccepted
  split
  · exact h
  · rename_i root hr
    cases hp : (if root = sp.genesisRoot then some none else
        (st.wrappers root).map some) with
    | none => simpa only [hp] using h
    | some p =>
      intro r o ho
      change Function.update st.wrappers B.root
        (some (forwardObj sp st.self st.now p B)) r = some o at ho
      by_cases he : r = B.root
      · subst r
        rw [Function.update_self] at ho
        cases ho
        right
        simp only [pendingWrappers_eq, List.map_append, List.map_cons, List.map_nil,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        exact Or.inr rfl
      · rw [Function.update_of_ne he] at ho
        rcases h r o ho with ho | ho
        · exact Or.inl ho
        · right
          simp only [pendingWrappers_eq, List.map_append]
          rw [pendingWrappers_eq] at ho
          exact List.mem_append_left _ ho

/-- The exact selected non-genesis parent is already published or in the old queue;
it is never justified by the newly appended child's envelope. -/
theorem wrappersAccounted_parent {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (prior : Wire sp.n → Prop)
    (st : State sp ro) (h : WrappersAccounted prior st) (root : Nat) (p : Wire sp.n)
    (hp : (if root = sp.genesisRoot then some none else
      (st.wrappers root).map some) = some (some p)) :
    prior p ∨ p ∈ pendingWrappers st := by
  by_cases hg : root = sp.genesisRoot
  · simp only [hg, ↓reduceIte, Option.some.injEq] at hp
    cases hp
  · simp only [hg, ↓reduceIte, Option.map_eq_some_iff] at hp
    obtain ⟨q, hq, he⟩ := hp
    cases he
    exact (wrappersAccounted_iff prior st).mp h root p hq

/-- At enqueue, the selected parent and canonical child are available before the fresh
envelope: the parent is held or belongs to the old queue, while child holdings are supplied
by the actual block receipt or own-block release. No publication is inferred from storage. -/
theorem wrappersAccounted_carried {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (seen : List (Wire sp.n))
    (st : State sp ro) (B : Blk sp) (root : Nat) (p : Option (Wire sp.n))
    (h : WrappersAccounted (fun o => o ∈ seen.flatMap Obj.parts) st)
    (hp : (if root = sp.genesisRoot then some none else
      (st.wrappers root).map some) = some p)
    (hB : blockObj sp B ∈ seen.flatMap Obj.parts) :
    ∀ c ∈ p.toList ++ [blockObj sp B],
      c ∈ (seen ++ pendingWrappers st).flatMap Obj.parts := by
  intro c hc
  rw [List.flatMap_append, List.mem_append]
  rcases List.mem_append.mp hc with hc | hc
  · cases p with
    | none => simp at hc
    | some parent =>
      have he : c = parent := by simpa only [Option.toList_some, List.mem_singleton] using hc
      subst c
      rcases wrappersAccounted_parent _ st h root parent hp with hh | hh
      · exact Or.inl hh
      · exact Or.inr (List.mem_flatMap.mpr ⟨parent, hh, Obj.Contains.refl parent⟩)
  · have he := List.mem_singleton.mp hc
    exact Or.inl (he ▸ hB)

/-- Each pending envelope carries only objects held before its own queue position. -/
def PendingReady {n : Nat} (seen cs : List (Wire n)) : Prop :=
  ∀ i o, cs[i]? = some o → ∀ c ∈ o.carried,
    c ∈ (seen ++ cs.take i).flatMap Obj.parts

/-- Characterize ordered readiness without exporting its body. -/
theorem pendingReady_iff {n : Nat} (seen cs : List (Wire n)) : PendingReady seen cs ↔
    ∀ i o, cs[i]? = some o → ∀ c ∈ o.carried,
      c ∈ (seen ++ cs.take i).flatMap Obj.parts := by
  rfl

/-- Appending a child keeps all old prefix obligations unchanged; its own carried
objects may use the complete old queue, but not the child itself. -/
theorem pendingReady_append {n : Nat} (seen cs : List (Wire n)) (o : Wire n)
    (h : PendingReady seen cs)
    (ho : ∀ c ∈ o.carried, c ∈ (seen ++ cs).flatMap Obj.parts) :
    PendingReady seen (cs ++ [o]) := by
  rw [pendingReady_iff] at h ⊢
  intro i q hi c hc
  by_cases hil : i < cs.length
  · rw [List.getElem?_append_left hil] at hi
    simpa only [List.take_append_of_le_length (Nat.le_of_lt hil)] using h i q hi c hc
  · have hle : cs.length ≤ i := Nat.le_of_not_gt hil
    rw [List.getElem?_append_right hle] at hi
    have he : i = cs.length := by
      have hb := (List.getElem?_eq_some_iff.mp hi).1
      simp only [List.length_singleton] at hb
      omega
    subst i
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hi
    subst q
    simpa only [List.take_left] using ho c hc

/-- Acceptance appends a ready envelope when the canonical child is actually held.
The selected parent is justified by the old durable-map/queue invariant. -/
theorem pendingReady_queueAccepted {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (seen : List (Wire sp.n))
    (st : State sp ro) (B : Blk sp)
    (ha : WrappersAccounted (fun o => o ∈ seen.flatMap Obj.parts) st)
    (hr : PendingReady seen (pendingWrappers st))
    (hb : blockObj sp B ∈ seen.flatMap Obj.parts) :
    PendingReady seen (pendingWrappers (queueAccepted st B)) := by
  unfold queueAccepted
  cases hpar : B.parent with
  | none => exact hr
  | some root =>
    dsimp only
    cases hp : (if root = sp.genesisRoot then some none else
      (st.wrappers root).map some) with
    | none => exact hr
    | some p =>
      rw [pendingWrappers_eq]
      simp only [List.map_append, List.map_cons, List.map_nil]
      change PendingReady seen (pendingWrappers st ++ [forwardObj sp st.self st.now p B])
      apply pendingReady_append _ _ _ hr
      exact wrappersAccounted_carried seen st B root p ha hp hb

/-- Actual block handling preserves readiness, including refusal. Child holdings must
come from the engine receipt or own release, rather than the store's acceptance result. -/
theorem pendingReady_onBlock {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (seen : List (Wire sp.n))
    (st : State sp ro) (B : Blk sp)
    (ha : WrappersAccounted (fun o => o ∈ seen.flatMap Obj.parts) st)
    (hr : PendingReady seen (pendingWrappers st))
    (hb : blockObj sp B ∈ seen.flatMap Obj.parts) :
    PendingReady seen (pendingWrappers (apply st (Node.onBlock st.self st.node st.now B))) := by
  unfold Node.onBlock
  split
  · exact hr
  · split
    · exact hr
    · have hs : (queueAccepted st B).self = st.self := by
        unfold queueAccepted
        cases B.parent with
        | none => rfl
        | some root =>
          dsimp only
          cases (if root = sp.genesisRoot then some none else
            (st.wrappers root).map some) <;> rfl
      have hq := pendingReady_queueAccepted seen st B ha hr hb
      rw [pendingWrappers_eq, hs] at hq
      rw [pendingWrappers_eq]
      exact hq

/-- After a complete drain, every durable entry is held: old entries were held already
and every previously pending envelope is now in the actual release output. -/
theorem wrappersAccounted_drained {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (seen released : List (Wire sp.n))
    (st : State sp ro)
    (ha : WrappersAccounted (fun c => c ∈ seen.flatMap Obj.parts) st)
    (hrel : ∀ o ∈ pendingWrappers st, o ∈ released) :
    ∀ root o, st.wrappers root = some o →
      o ∈ (seen ++ released).flatMap Obj.parts := by
  intro root o ho
  rw [List.flatMap_append, List.mem_append]
  rcases (wrappersAccounted_iff _ st).mp ha root o ho with hh | hh
  · exact Or.inl hh
  · exact Or.inr (List.mem_flatMap.mpr ⟨o, hrel o hh, Obj.Contains.refl o⟩)

/-- Enlarging actual holdings preserves ordered queue readiness. -/
theorem pendingReady_mono {n : Nat} {seen seen' cs : List (Wire n)}
    (hseen : ∀ o ∈ seen.flatMap Obj.parts, o ∈ seen'.flatMap Obj.parts)
    (h : PendingReady seen cs) : PendingReady seen' cs := by
  rw [pendingReady_iff] at h ⊢
  intro i o hi c hc
  have hh := h i o hi c hc
  rw [List.flatMap_append, List.mem_append] at hh ⊢
  exact hh.elim (fun hh => Or.inl (hseen c hh)) Or.inr

/-- Handler cut folds preserve exact map/queue accounting. -/
theorem wrappersAccounted_apply {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (prior : Wire sp.n → Prop)
    (st : State sp ro)
    (r : NodeState (goldilocksNode sp ro) × List (Cut (goldilocksNode sp ro)))
    (h : WrappersAccounted prior st) : WrappersAccounted prior (apply st r) := by
  let step := fun (s : State sp ro) (c : Cut (goldilocksNode sp ro)) => match c with
    | .fg (.block B true) => queueAccepted s B
    | _ => s
  have hstep (s : State sp ro) (c : Cut (goldilocksNode sp ro))
      (hs : WrappersAccounted prior s) :
      WrappersAccounted prior (step s c) ∧ (step s c).self = s.self := by
    cases c with
    | ac l => exact ⟨hs, rfl⟩
    | fg l =>
      cases l with
      | attest C a => exact ⟨hs, rfl⟩
      | attestation a => exact ⟨hs, rfl⟩
      | block B accepted =>
        cases accepted with
        | false => exact ⟨hs, rfl⟩
        | true =>
          refine ⟨wrappersAccounted_queueAccepted prior s B hs, ?_⟩
          change (queueAccepted s B).self = s.self
          unfold queueAccepted
          cases B.parent with
          | none => rfl
          | some root =>
            dsimp only
            cases (if root = sp.genesisRoot then some none else
              (s.wrappers root).map some) <;> rfl
  have hfold (cs : List (Cut (goldilocksNode sp ro))) : ∀ s,
      WrappersAccounted prior s →
      WrappersAccounted prior (cs.foldl step s) ∧ (cs.foldl step s).self = s.self := by
    induction cs with
    | nil => intro s hs; exact ⟨hs, rfl⟩
    | cons c cs ih =>
      intro s hs
      have hc := hstep s c hs
      have ht := ih (step s c) hc.1
      exact ⟨ht.1, ht.2.trans hc.2⟩
  obtain ⟨hi, he⟩ := hfold r.2 st h
  rw [wrappersAccounted_iff] at hi ⊢
  intro root o ho
  rcases hi root o ho with hp | hp
  · exact Or.inl hp
  · right
    rw [pendingWrappers_eq] at hp ⊢
    rw [he] at hp
    exact hp

/-- A receipt's canonical child is held independently of whether its handler accepts it. -/
theorem pendingReady_processOne {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (seen : List (Wire sp.n))
    (st : State sp ro) (hs : List (Header Info × Nat)) (o : Wire sp.n)
    (ha : WrappersAccounted (fun c => c ∈ seen.flatMap Obj.parts) st)
    (hr : PendingReady seen (pendingWrappers st)) (ho : o ∈ seen.flatMap Obj.parts) :
    PendingReady seen (pendingWrappers (processOne hs st o)) := by
  unfold processOne
  split
  · rename_i B hB
    have he : o = blockObj sp B := by
      rcases canonEvent_eq_some hB with ⟨C, he, ho⟩ | ⟨v, he, _⟩ | ⟨a, he, _⟩
      · cases he; exact ho
      · cases he
      · cases he
    have h := pendingReady_onBlock seen st B ha hr (he ▸ ho)
    unfold relayIf
    dsimp only
    split <;> exact h
  · unfold Node.onMessage Node.acCall apply
    dsimp only
    exact hr
  · unfold relayIf Node.onAttestation apply
    simp only [↓reduceIte]
    exact hr
  · exact hr

/-- Receipt handlers retain exact map accounting; relay-buffer updates do not affect it. -/
theorem wrappersAccounted_processOne {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (prior : Wire sp.n → Prop)
    (st : State sp ro) (hs : List (Header Info × Nat)) (o : Wire sp.n)
    (ha : WrappersAccounted prior st) : WrappersAccounted prior (processOne hs st o) := by
  unfold processOne
  split
  · rename_i B hB
    have h := wrappersAccounted_apply prior st (Node.onBlock st.self st.node st.now B) ha
    unfold relayIf
    dsimp only
    split <;> exact h
  · rename_i v hv
    have h := wrappersAccounted_apply prior st (Node.onMessage st.self st.node st.now v) ha
    exact h
  · rename_i a ha'
    have h := wrappersAccounted_apply prior st (Node.onAttestation st.node a) ha
    unfold relayIf
    simp only [↓reduceIte]
    exact h
  · exact ha

/-- Recursive receipt processing preserves accounting and ordered readiness together.
All children are held by the enclosing engine receipt before any handler is executed. -/
theorem pendingReady_process {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (seen : List (Wire sp.n))
    (st : State sp ro) (hs : List (Header Info × Nat)) (o : Wire sp.n)
    (ha : WrappersAccounted (fun c => c ∈ seen.flatMap Obj.parts) st)
    (hr : PendingReady seen (pendingWrappers st))
    (ho : ∀ c ∈ o.parts, c ∈ seen.flatMap Obj.parts) :
    WrappersAccounted (fun c => c ∈ seen.flatMap Obj.parts) (process st o hs) ∧
      PendingReady seen (pendingWrappers (process st o hs)) := by
  have hf (xs : List (Wire sp.n)) : ∀ st : State sp ro,
      WrappersAccounted (fun c => c ∈ seen.flatMap Obj.parts) st →
      PendingReady seen (pendingWrappers st) →
      (∀ c ∈ xs, c ∈ seen.flatMap Obj.parts) →
      WrappersAccounted (fun c => c ∈ seen.flatMap Obj.parts)
          (xs.foldl (processOne hs) st) ∧
        PendingReady seen (pendingWrappers (xs.foldl (processOne hs) st)) := by
    induction xs with
    | nil => intro st ha hr _; exact ⟨ha, hr⟩
    | cons c cs ih =>
      intro st ha hr hh
      exact ih _ (wrappersAccounted_processOne _ st hs c ha)
        (pendingReady_processOne seen st hs c ha hr (hh c List.mem_cons_self))
        (fun d hd => hh d (List.mem_cons_of_mem c hd))
  exact hf o.parts st ha hr ho

/-- Own recording preserves readiness provided the actual decoded own block is held.
The caller must identify the generated canonical block; arbitrary signed headers do not
justify this premise merely by having been released. -/
theorem pendingReady_recordOwn {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (seen : List (Wire sp.n))
    (st : State sp ro) (o : Wire sp.n) (hs : List (Header Info × Nat))
    (ha : WrappersAccounted (fun c => c ∈ seen.flatMap Obj.parts) st)
    (hr : PendingReady seen (pendingWrappers st))
    (hb : ∀ k s hd cs, o = .mk (.signed k (.proposer s)) (.item hd) cs →
      ∀ atts p d, decodeInfo sp.n hd.info = some (atts, p) → rootOf hs hd = some d →
        blockObj sp (blockOf sp d hd k atts p) ∈ seen.flatMap Obj.parts) :
    PendingReady seen (pendingWrappers (recordOwn st o hs)) := by
  unfold recordOwn
  split
  · exact hr
  · rename_i original k s hd cs
    split
    · rename_i atts p d hdec hroot
      exact pendingReady_onBlock seen st _ ha hr (hb k s hd cs rfl atts p d hdec hroot)
    · exact hr
  · exact hr

/-- A generated proposal's decoded block has exactly the signed object just released.
This is an encoding identity, independent of payload validity and the release digest. -/
theorem proposal_blockObj {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (s : Slot)
    (par : ParentRef) (info : Info) (cs : List (Wire sp.n))
    (hp : (propose st s).2 = some (par, info, cs))
    (k : Fin sp.n) (x d : Nat) (atts : List (FG.Att sp.n)) (p : SA.Payload sp.n)
    (hd : decodeInfo sp.n info = some (atts, p)) :
    blockObj sp (blockOf sp d ⟨par, s, x, info⟩ k atts p) =
      .mk (.signed k (.proposer s)) (.item ⟨par, s, x, info⟩) cs := by
  unfold propose at hp
  dsimp only at hp
  split at hp
  · cases hp
  · cases hp
    rw [decodeInfo_encodeInfo] at hd
    cases hd
    simp only [blockObj, blockOf, headerOf, parentRoot_parentRef]

/-- The engine's proposal candidate supplies the canonical-child premise used by own
recording. It is identified from the actual duty, not inferred from an arbitrary header. -/
theorem signedCandidate_propose_canonical {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (goldilocks S)) E)) (s : Slot) (hs : 0 < s)
    (o : (protoOf (compiled (goldilocks S)) E).Object)
    (ho : o ∈ rho.signedCandidate v (.propose s hs)
      ((protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).2) :
    ∀ k s' hd cs, o = .mk (.signed k (.proposer s')) (.item hd) cs →
      ∀ atts p d, decodeInfo (Fintype.card V) hd.info = some (atts, p) →
        blockObj (S.params (pubOf E) hn)
          (blockOf (S.params (pubOf E) hn) d hd k atts p) = o := by
  obtain ⟨m, cs, hm, _, _, rfl⟩ := rho.mem_signedCandidate.mp ho
  rw [act_propose_snd S hn] at hm
  obtain ⟨q, hq, he⟩ := Option.mem_map.mp (Option.mem_toList.mp hm)
  cases he
  intro k s' hd cs' he atts p d hdec
  cases he
  exact proposal_blockObj (shapeOf S hn nd) s q.1 q.2.1 q.2.2 hq
    (rho.ownKey v) (encodeTxs nd.st.2) d atts p hdec

/-- Own recording preserves durable map provenance, including a new accepted block. -/
theorem wrappersAccounted_recordOwn {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (prior : Wire sp.n → Prop)
    (st : State sp ro) (o : Wire sp.n) (hs : List (Header Info × Nat))
    (ha : WrappersAccounted prior st) : WrappersAccounted prior (recordOwn st o hs) := by
  unfold recordOwn
  split
  · exact ha
  · split
    · exact wrappersAccounted_apply prior st _ ha
    · exact ha
  · exact ha

/-- A successful canonical own release supplies its child holding at the actual updated
seen prefix; map accounting and ordered readiness survive its `recordOwn` call together. -/
theorem pendingReady_own_release {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (seen : List (Wire sp.n)) (st : State sp ro) (o : Wire sp.n)
    (hs : List (Header Info × Nat))
    (ha : WrappersAccounted (fun c => c ∈ seen.flatMap Obj.parts) st)
    (hr : PendingReady seen (pendingWrappers st))
    (hc : ∀ k s hd cs, o = .mk (.signed k (.proposer s)) (.item hd) cs →
      ∀ atts p d, decodeInfo sp.n hd.info = some (atts, p) →
        blockObj sp (blockOf sp d hd k atts p) = o) :
    WrappersAccounted (fun c => c ∈ (seen ++ [o]).flatMap Obj.parts) (recordOwn st o hs) ∧
      PendingReady (seen ++ [o]) (pendingWrappers (recordOwn st o hs)) := by
  have hmono : ∀ c ∈ seen.flatMap Obj.parts, c ∈ (seen ++ [o]).flatMap Obj.parts := by
    intro c hc
    obtain ⟨a, ha, hc⟩ := List.mem_flatMap.mp hc
    exact List.mem_flatMap.mpr ⟨a, List.mem_append_left _ ha, hc⟩
  have ha' : WrappersAccounted (fun c => c ∈ (seen ++ [o]).flatMap Obj.parts) st := by
    rw [wrappersAccounted_iff] at ha ⊢
    intro root c hw
    exact (ha root c hw).imp (hmono c) id
  refine ⟨wrappersAccounted_recordOwn _ st o hs ha', ?_⟩
  apply pendingReady_recordOwn (seen ++ [o]) st o hs ha' (pendingReady_mono hmono hr)
  intro k s hd cs he atts p d hdec _
  rw [hc k s hd cs he atts p d hdec]
  exact List.mem_flatMap.mpr ⟨o, List.mem_append_right _ (List.mem_singleton_self o),
    Obj.Contains.refl o⟩

/-- Release induction uses actual successful prefixes. Rejected candidates leave both
invariants unchanged; each successful canonical candidate extends seen before recording. -/
theorem releaseAll_pendingReady {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (hn : 1 ≤ Fintype.card V) (hash : Header Info → Nat) (origin : Fin (Fintype.card V))
    (nd : Model.Node (protoOf (compiled (goldilocks S)) E))
    (cs : List (protoOf (compiled (goldilocks S)) E).Object)
    (ha : WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ nd.seen.flatMap Obj.parts) (shapeOf S hn nd))
    (hr : PendingReady nd.seen (pendingWrappers (shapeOf S hn nd)))
    (hc : ∀ o ∈ cs, ∀ k s hd children,
      o = .mk (.signed k (.proposer s)) (.item hd) children →
      ∀ atts p d, decodeInfo (Fintype.card V) hd.info = some (atts, p) →
        blockObj (S.params (pubOf E) hn)
          (blockOf (S.params (pubOf E) hn) d hd k atts p) = o) :
    let result := (Model.releaseAll (protoOf (compiled (goldilocks S)) E) hash origin nd cs).1
    WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ result.seen.flatMap Obj.parts) (shapeOf S hn result) ∧
      PendingReady result.seen (pendingWrappers (shapeOf S hn result)) := by
  induction cs generalizing nd with
  | nil => exact ⟨ha, hr⟩
  | cons o cs ih =>
    simp only [Model.releaseAll]
    split
    · have hh := pendingReady_own_release (sp := S.params (pubOf E) hn)
        (nd.seen : List (Wire (Fintype.card V))) (shapeOf S hn nd) o
        (Model.digests (P := protoOf (compiled (goldilocks S)) E) hash o)
        ha hr (hc o List.mem_cons_self)
      exact ih _ hh.1 hh.2 (fun c h => hc c (List.mem_cons_of_mem o h))
    · exact ih nd ha hr (fun c h => hc c (List.mem_cons_of_mem o h))

/-- Actual proposal duties preserve both invariants from their input state,
without an extra canonical-child assumption on their caller. -/
theorem dutyStep_propose_pendingReady {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (goldilocks S)) E)) (s : Slot) (hs : 0 < s)
    (ha : WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ nd.seen.flatMap Obj.parts) (shapeOf S hn nd))
    (hr : PendingReady nd.seen (pendingWrappers (shapeOf S hn nd))) :
    let result := (rho.dutyStep v nd (.propose s hs)).1
    WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ result.seen.flatMap Obj.parts) (shapeOf S hn result) ∧
      PendingReady result.seen (pendingWrappers (shapeOf S hn result)) := by
  unfold Model.Run.dutyStep
  split
  swap
  · exact ⟨ha, hr⟩
  apply releaseAll_pendingReady S hn rho.hash (rho.ownKey v)
  · change WrappersAccounted _ (((protoOf (compiled (goldilocks S)) E).act nd.st
      (.propose s hs)).1.1 hn)
    rw [shapeOf_act_propose S hn]
    unfold propose
    dsimp only
    split <;> exact ha
  · change PendingReady _ (pendingWrappers (((protoOf (compiled (goldilocks S)) E).act nd.st
      (.propose s hs)).1.1 hn))
    rw [shapeOf_act_propose S hn]
    unfold propose
    dsimp only
    split <;> exact hr
  · exact fun o ho => signedCandidate_propose_canonical S rho hn v nd s hs o ho

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
added to the generic `ShapeObligations` or network premises. -/
def WrappersCover {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) : Prop :=
  ∀ root, root ≠ sp.genesisRoot → (st.node.fg.blocks root).isSome →
    (st.wrappers root).isSome

/-- Coverage depends only on held roots and the durable wrapper map. -/
theorem wrappersCover_iff {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) :
    WrappersCover st ↔ ∀ root, root ≠ sp.genesisRoot →
      (st.node.fg.blocks root).isSome → (st.wrappers root).isSome := by rfl

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

/-- Retain the exact parent lookup together with the appended queue and updated map.
This lets a provenance invariant follow the selected parent, rather than merely knowing
that some wrapper was appended. -/
theorem onBlock_queues_acceptance_parent {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (B : Blk sp)
    (hcover : WrappersCover st)
    (hacc : .fg (.block B true) ∈ (Node.onBlock st.self st.node st.now B).2) :
    ∃ root p, B.parent = some root ∧
      (if root = sp.genesisRoot then some none else (st.wrappers root).map some) = some p ∧
      (apply st (Node.onBlock st.self st.node st.now B)).wrappers =
        Function.update st.wrappers B.root (some (forwardObj sp st.self st.now p B)) ∧
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
      exact ⟨root, p, hr, hp, queueAccepted_of_parent st B root p hr hp⟩

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

/-- Each receipt call preserves coverage of held non-genesis roots by own wrappers. -/
theorem wrappersCover_processOne {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) o hs
    (h : WrappersCover st) : WrappersCover (processOne hs st o) := by
  unfold processOne
  split
  · unfold relayIf
    dsimp only
    split <;> exact wrappersCover_onBlock _ _ h
  · exact h
  · rename_i a _
    obtain ⟨atts, he⟩ := Store.onAttestation_eq st.node.fg a
    simpa only [WrappersCover, ne_eq, relayIf, ↓reduceIte, apply, Node.onAttestation, he,
      List.foldl_cons, List.foldl_nil, not_and_self, decide_false, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.dedup_nil, List.filter_nil, List.map_nil] using h
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
      simpa only [WrappersCover, ne_eq, Node.onAttestation, Node.acToFG, he] using h

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

/-- Every actual duty prefix preserves coverage, including an own block's recording. -/
theorem runDuties_wrappersCover {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (goldilocks S)) E))
    (ds : List (protoOf (compiled (goldilocks S)) E).Duty)
    (h : WrappersCover (shapeOf S hn nd)) :
    WrappersCover (shapeOf S hn (rho.runDuties v nd ds).1) := by
  exact runDuties_pres S rho hn WrappersCover wrappersCover_recordOwn wrappersCover_propose
    wrappersCover_nodeTick wrappersCover_poll v nd ds h

/-- The actual runtime's durable map covers every held non-genesis root at every event
boundary. Initially only genesis is held. Block acceptance updates both maps together;
all other handlers preserve them, including restart. No execution-validity assumption is
needed for this structural invariant. -/
theorem stateAt_wrappersCover {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) : ∀ i, WrappersCover (stateAt S rho hn v i)
  | 0 => by
    rw [stateAt_zero]
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
          rw [stateAt_eq] at ih
          exact tick_pres S rho hn WrappersCover wrappersCover_recordOwn
            wrappersCover_propose wrappersCover_nodeTick wrappersCover_poll v _ t ih
        | deliver w o t =>
          simp only [Model.Event.node] at hnode
          subst w
          rw [stateAt_deliver S rho hn v he]
          rw [stateAt_eq] at ih
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

end Consensus.Goldilocks.Simulation
