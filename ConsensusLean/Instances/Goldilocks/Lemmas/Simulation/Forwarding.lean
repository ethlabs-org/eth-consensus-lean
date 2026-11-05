module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Interface
public import ConsensusLean.Lemmas.Model.Candidates
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ForwardingState
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EngineSteps
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outbox

public section

/-! # Publication contracts for the revised publisher

OPEN implementation arguments, not paper proofs. The paper's forwarding rule motivates these
interfaces but does not prove engine candidate ordering or signed-object provenance. In
particular installing the signed publisher does not prove these contracts. The obligations
assembly must construct an implementation and discharge every field, never assume this bundle
as an additional regime premise. Parameters remain explicit until run-selected simulation lands.
-/

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
  obtain ⟨m, cs, hm, _, rfl⟩ := rho.mem_signedCandidate.mp ho
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
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) where
  actual : Publication (protoOf (compiled (goldilocks S)) E) → Prop
  eventTime : Nat → Time
  actual_event : ∀ r, actual r → rho.SendsAt (rho.key r.origin) r.event (eventTime r.event)
  actual_success : ∀ r, actual r →
    let nd := (Model.releaseAll (protoOf (compiled (goldilocks S)) E) rho.hash r.origin
      r.before (r.candidates.take r.index)).1
    Model.releasable nd.seen r.object = true ∧
      Model.protects (protoOf (compiled (goldilocks S)) E) r.origin nd.seen r.object = true ∧
      (protoOf (compiled (goldilocks S)) E).dependencies.ready (Model.closure nd.seen) r.object =
          true
  actual_release : ∀ r, actual r → r.object ∈ rho.releasesAt r.event

/-- A batch input and candidate list, before applying its release guard. -/
structure ReleaseBatch {pub : Public} {O : Type} (P : Protocol pub O) where
  before : Model.Node P
  candidates : List P.Object

/-- Enumerate actual selected duty batches, threading the same `dutyStep` states as the
engine. Empty/unselected duties retain their ordinal position as an empty batch. -/
noncomputable def dutyBatches {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {O : OutputSchema} {F : ProtocolFamily O} (rho : Model.Run F E) (v : V) :
    Model.Node (protoOf F E) → List (protoOf F E).Duty → List (ReleaseBatch (protoOf F E))
  | _, [] => []
  | nd, d :: ds =>
    let a := (protoOf F E).act nd.st d
    let batch := if rho.ownKey v ∈ rho.sel ((protoOf F E).role d) then
      ⟨⟨a.1, nd.seen⟩, rho.signedCandidate v d a.2⟩ else ⟨nd, []⟩
    batch :: dutyBatches rho v (rho.dutyStep v nd d).1 ds

/-- No duties produce no release batches. -/
theorem dutyBatches_nil {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {O : OutputSchema} {F : ProtocolFamily O} (rho : Model.Run F E) (v : V)
    (nd : Model.Node (protoOf F E)) : dutyBatches rho v nd [] = [] := by
  rfl

/-- The next batch retains its duty position even when unselected; later batches start
from the actual duty-step result. -/
theorem dutyBatches_cons {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {O : OutputSchema} {F : ProtocolFamily O} (rho : Model.Run F E) (v : V)
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
    {O : OutputSchema} {F : ProtocolFamily O} (rho : Model.Run F E) (i : Nat) :
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
    {O : OutputSchema} {F : ProtocolFamily O} (rho : Model.Run F E) (i : Nat) :
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
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (r : Publication (protoOf (compiled (goldilocks S)) E)) : Prop :=
  (eventBatches rho r.event)[r.batch]? = some ⟨r.before, r.candidates⟩ ∧
  ∃ t, rho.SendsAt (rho.key r.origin) r.event t

/-- Characterize the actual batch and sending event without exposing the definition. -/
theorem executedPublication_iff {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (r : Publication (protoOf (compiled (goldilocks S)) E)) :
    ExecutedPublication S rho r ↔
      (eventBatches rho r.event)[r.batch]? = some ⟨r.before, r.candidates⟩ ∧
        ∃ t, rho.SendsAt (rho.key r.origin) r.event t := by rfl

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

/-- A batch drains completely when its guards hold against the immutable candidate
prefix. Earlier candidates become actual holdings by induction, not by assumption. -/
theorem releaseAll_of_prefix_guards {pub : Public} {O : Type} (P : Protocol pub O)
    (hash : P.Item → Nat) (x : Key pub) (nd : Model.Node P) (cs : List P.Object)
    (hready : ∀ i o, cs[i]? = some o →
      Model.releasable (P := P) (nd.seen ++ cs.take i) o = true ∧
      Model.protects P x (nd.seen ++ cs.take i) o = true ∧
      P.dependencies.ready (Model.closure (nd.seen ++ cs.take i)) o = true) :
    (Model.releaseAll P hash x nd cs).2 = cs ∧
      (Model.releaseAll P hash x nd cs).1.seen = nd.seen ++ cs := by
  induction cs generalizing nd with
  | nil => exact ⟨rfl, (List.append_nil _).symm⟩
  | cons o cs ih =>
    have hg := hready 0 o (by simp)
    simp only [List.take_zero, List.append_nil] at hg
    simp only [Model.releaseAll, hg.1, hg.2.1, hg.2.2, Bool.and_self, ↓reduceIte]
    have ht := ih
      (nd := ⟨P.recordOwn nd.st o (Model.digests hash o), nd.seen ++ [o]⟩)
      (by
        intro i c hc
        have hC := hready (i + 1) c
          (by simpa only [List.getElem?_cons_succ] using hc)
        simpa only [List.take_succ_cons, List.append_assoc, List.singleton_append] using hC)
    exact ⟨congrArg (List.cons _) ht.1,
      ht.2.trans (by simp only [List.append_assoc, List.singleton_append])⟩

/-- Ordered readiness discharges every guard for a batch of canonical block envelopes. -/
theorem forward_batch_guards {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (hn : 1 ≤ Fintype.card V) (x : Fin (Fintype.card V))
    (seen cs : List (Wire (Fintype.card V))) (hr : PendingReady seen cs)
    (hshape : ∀ o ∈ cs, ∃ t p B, o = forwardObj (S.params (pubOf E) hn) x t p B) :
    ∀ i o, cs[i]? = some o →
      Model.releasable (P := protoOf (compiled (goldilocks S)) E) (seen ++ cs.take i) o = true ∧
      Model.protects (protoOf (compiled (goldilocks S)) E) x (seen ++ cs.take i) o = true ∧
      (protoOf (compiled (goldilocks S)) E).dependencies.ready
        (Model.closure (seen ++ cs.take i)) o = true := by
  intro i o hi
  obtain ⟨t, p, B, he⟩ := hshape o (List.mem_of_getElem? hi)
  have hh := (pendingReady_iff seen cs).mp hr i o hi
  subst o
  exact forwardObj_release_guards S hn (seen ++ cs.take i) x t p B hh

/-- A ready canonical forwarding suffix is released completely from its actual
post-prefix node. This allows an ordinary poll emission to precede the block queue. -/
theorem releaseAll_forward_batch {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (hn : 1 ≤ Fintype.card V) (hash : Header Info → Nat) (x : Fin (Fintype.card V))
    (nd : Model.Node (protoOf (compiled (goldilocks S)) E))
    (cs : List (protoOf (compiled (goldilocks S)) E).Object)
    (hr : PendingReady nd.seen cs)
    (hshape : ∀ o ∈ cs, ∃ t p B, o = forwardObj (S.params (pubOf E) hn) x t p B) :
    (Model.releaseAll (protoOf (compiled (goldilocks S)) E) hash x nd cs).2 = cs ∧
      (Model.releaseAll (protoOf (compiled (goldilocks S)) E) hash x nd cs).1.seen =
        nd.seen ++ cs := by
  apply releaseAll_of_prefix_guards
  exact forward_batch_guards S hn x nd.seen cs hr hshape

/-- Ordinary poll candidates may succeed or fail: either way they preserve holdings,
so a ready block-envelope suffix drains completely after their actual release prefix. -/
theorem releaseAll_forward_suffix {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (hn : 1 ≤ Fintype.card V) (hash : Header Info → Nat) (x : Fin (Fintype.card V))
    (nd : Model.Node (protoOf (compiled (goldilocks S)) E))
    (pre cs : List (protoOf (compiled (goldilocks S)) E).Object)
    (hr : PendingReady nd.seen cs)
    (hshape : ∀ o ∈ cs, ∃ t p B, o = forwardObj (S.params (pubOf E) hn) x t p B) :
    (Model.releaseAll (protoOf (compiled (goldilocks S)) E) hash x nd (pre ++ cs)).2 =
      (Model.releaseAll (protoOf (compiled (goldilocks S)) E) hash x nd pre).2 ++ cs := by
  rw [Model.releaseAll_append (P := protoOf (compiled (goldilocks S)) E) hash x nd pre cs]
  have hseen := Model.releaseAll_seen (P := protoOf (compiled (goldilocks S)) E)
    hash x nd pre
  have hr' : PendingReady
      (Model.releaseAll (protoOf (compiled (goldilocks S)) E) hash x nd pre).1.seen cs := by
    rw [hseen]
    apply pendingReady_mono (h := hr)
    intro o ho
    obtain ⟨c, hc, ho⟩ := List.mem_flatMap.mp ho
    exact List.mem_flatMap.mpr ⟨c, List.mem_append_left _ hc, ho⟩
  rw [(releaseAll_forward_batch S hn hash x _ cs hr' hshape).1]

/-- Actual selected poll candidates retain the old signed block queue after the ordinary
emission. The self-key premise is the runtime identity, not a new service assumption. -/
theorem signedCandidate_poll_eq {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (goldilocks S)) E)) (t : Nat)
    (hsel : rho.ownKey v ∈ rho.sel .poll)
    (hself : (shapeOf S hn nd).self = rho.ownKey v) :
    rho.signedCandidate v (.poll t) ((protoOf (compiled (goldilocks S)) E).act nd.st (.poll t)).2 =
      ((poll (shapeOf S hn nd) t).2.toList.map fun q =>
        Obj.mk (.signed (rho.ownKey v) .poll) (.data q.1) q.2) ++
        pendingWrappers (shapeOf S hn nd) ++
      ((shapeOf S hn nd).voteForwards.map fun q =>
        Obj.mk (.signed (rho.ownKey v) .poll) (.data (.voteForward q.1 (encodeVote q.2)))
          [voteObj q.2]) := by
  rw [act_poll_snd S hn]
  simp only [Model.Run.signedCandidate,
    show (protoOf (compiled (goldilocks S)) E).role (.poll t) = .poll from rfl,
    hsel, ↓reduceIte, Option.toList_map, pendingWrappers_eq, hself]
  erw [List.map_append, List.map_append, List.map_map, List.map_map, List.map_map]
  rfl

/-- A selected actual poll releases every ready canonical pending block wrapper. The ordinary
emission may fail; later vote envelopes cannot undo releases from the block prefix. -/
theorem dutyStep_poll_pending {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (goldilocks S)) E)) (t : Nat)
    (hsel : rho.ownKey v ∈ rho.sel .poll)
    (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (hr : PendingReady nd.seen (pendingWrappers (shapeOf S hn nd)))
    (hshape : ∀ o ∈ pendingWrappers (shapeOf S hn nd), ∃ τ p B,
      o = forwardObj (S.params (pubOf E) hn) (rho.ownKey v) τ p B) :
    ∀ o ∈ pendingWrappers (shapeOf S hn nd), o ∈ (rho.dutyStep v nd (.poll t)).2 := by
  intro o ho
  unfold Model.Run.dutyStep
  simp only [show (protoOf (compiled (goldilocks S)) E).role (.poll t) = .poll from rfl,
    hsel, ↓reduceIte]
  rw [signedCandidate_poll_eq S rho hn v nd t hsel hself]
  erw [Model.releaseAll_append (P := protoOf (compiled (goldilocks S)) E)]
  apply List.mem_append_left
  erw [releaseAll_forward_suffix S hn rho.hash (rho.ownKey v)
    ⟨((protoOf (compiled (goldilocks S)) E).act nd.st (.poll t)).1, nd.seen⟩ _ _ hr hshape]
  exact List.mem_append_right _ ho

/-- Poll's block map is durable while the pending queue is cleared. -/
theorem poll_wrappers {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (t : Time) :
    (poll st t).1.wrappers = st.wrappers ∧ (poll st t).1.forwards = [] := by
  unfold poll
  have hf : (fgUpdate st).wrappers = st.wrappers := by
    unfold fgUpdate
    dsimp only
    split
    · rfl
    · split <;> rfl
  dsimp only
  split <;> constructor
  · dsimp only; split <;> first | exact hf | rfl
  · rfl
  · dsimp only; split <;> first | exact hf | rfl
  · rfl

/-- After the real poll, every durable wrapper is held, not merely pending. -/
theorem dutyStep_poll_wrappers_held {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (goldilocks S)) E)) (t : Nat)
    (hsel : rho.ownKey v ∈ rho.sel .poll) (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (ha : WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ nd.seen.flatMap Obj.parts) (shapeOf S hn nd))
    (hr : PendingReady nd.seen (pendingWrappers (shapeOf S hn nd)))
    (hc : ∀ o ∈ pendingWrappers (shapeOf S hn nd), ∃ τ p B,
      o = forwardObj (S.params (pubOf E) hn) (rho.ownKey v) τ p B) :
    ∀ root o, (shapeOf S hn (rho.dutyStep v nd (.poll t)).1).wrappers root = some o →
      o ∈ (rho.dutyStep v nd (.poll t)).1.seen.flatMap Obj.parts := by
  intro root o hw
  rw [dutyStep_poll S rho hn v nd t hsel, (poll_wrappers _ _).1] at hw
  have hh := wrappersAccounted_drained (sp := S.params (pubOf E) hn)
    (nd.seen : List (Wire (Fintype.card V))) (rho.dutyStep v nd (.poll t)).2
    (shapeOf S hn nd) ha (dutyStep_poll_pending S rho hn v nd t hsel hself hr hc) root o hw
  have he : (rho.dutyStep v nd (.poll t)).1.seen = nd.seen ++ (rho.dutyStep v nd (.poll t)).2 := by
    unfold Model.Run.dutyStep
    simp only [show (protoOf (compiled (goldilocks S)) E).role (.poll t) = .poll from rfl,
      hsel, ↓reduceIte]
    exact Model.releaseAll_seen _ _ _ _
  rw [he]
  exact hh

/-- Each enumerated duty batch releases only objects released by the actual duty list.
The induction threads the same intermediate node as `runDuties`, including unselected
duties, which have an empty batch and leave the state unchanged. -/
theorem dutyBatches_release {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {O : OutputSchema} {F : ProtocolFamily O} (rho : Model.Run F E) (v : V)
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
    {O : OutputSchema} {F : ProtocolFamily O} (rho : Model.Run F E) (v : V) (i : Nat) (t : Time)
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
  (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
  (tr : GoldilocksTrace (S.params (pubOf E) hn) (S.ro _)) (cutMap : Nat → Nat)
  (pubExec : PublisherExecution S rho)

/-- Concrete publication relation: all executed candidates passing the three guards at
their actual prefix, with the event's own time. No provenance or acceptance claim is used
to select publications. The batch lemmas above establish the actual release field. -/
noncomputable def publisherExecution : PublisherExecution S rho where
  actual r := ExecutedPublication S rho r ∧
    let nd := (Model.releaseAll (protoOf (compiled (goldilocks S)) E) rho.hash r.origin
      r.before (r.candidates.take r.index)).1
    Model.releasable nd.seen r.object = true ∧
      Model.protects (protoOf (compiled (goldilocks S)) E) r.origin nd.seen r.object = true ∧
      (protoOf (compiled (goldilocks S)) E).dependencies.ready (Model.closure nd.seen) r.object =
          true
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
theorem publisherExecution_actual_iff (r : Publication (protoOf (compiled (goldilocks S)) E)) :
    (publisherExecution S rho).actual r ↔ ExecutedPublication S rho r ∧
      let nd := (Model.releaseAll (protoOf (compiled (goldilocks S)) E) rho.hash r.origin
        r.before (r.candidates.take r.index)).1
      Model.releasable nd.seen r.object = true ∧
        Model.protects (protoOf (compiled (goldilocks S)) E) r.origin nd.seen r.object = true ∧
        (protoOf (compiled (goldilocks S)) E).dependencies.ready
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

/-- Characterize the origin obligation without exposing its definition body. -/
theorem forwardOrigin_iff : ForwardOrigin S rho hn tr cutMap pubExec ↔
    ∀ r, pubExec.actual r → rho.key r.origin ∈ rho.honest → ∀ t p B,
      decodeForward (S.params (pubOf E) hn) (Model.digests rho.hash r.object) r.object =
        some (r.origin, t, p, B) →
      ∃ k, tr.AcceptAt r.origin k B ∧ tr.time k = t ∧
        k < cutMap (r.event + 1) ∧ t = pubExec.eventTime r.event := by
  rfl

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

/-- Characterize acceptance completeness without exposing its definition body. -/
theorem forwardAtAcceptance_iff : ForwardAtAcceptance S rho hn tr cutMap pubExec ↔
    ∀ x ∈ honestKeys S rho, ∀ k B, tr.AcceptAt x k B →
      ∃ r p, pubExec.actual r ∧ r.origin = x ∧
        cutMap r.event ≤ k ∧ k < cutMap (r.event + 1) ∧
        pubExec.eventTime r.event = tr.time k ∧
        r.object = forwardObj (S.params (pubOf E) hn) x (tr.time k) p B ∧
        decodeForward (S.params (pubOf E) hn) (Model.digests rho.hash r.object) r.object =
          some (x, tr.time k, p, B) := by
  rfl

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

/-- Characterize prior processing without exposing its definition body. -/
theorem forwardHeldProcessed_iff : ForwardHeldProcessed S rho hn tr cutMap ↔
    ∀ y ∈ honestKeys S rho, ∀ i x t p B o,
      x ∈ honestKeys S rho →
      o ∈ Model.closure (rho.stateBefore i (rho.key y)).seen →
      decodeForward (S.params (pubOf E) hn) (Model.digests rho.hash o) o =
        some (x, t, p, B) →
      ∃ k < cutMap i, t ≤ tr.time k ∧
        (tr.BlockCallAt y k B ∨ y = x ∧ tr.AcceptAt y k B) := by
  rfl

/-- OPEN: accepted canonical objects and exact parent wrappers are in the publisher's seen
closure at the actual candidate prefix; signing and dependency guards do not suppress it. -/
def AcceptedObjectsSeen : Prop :=
  ∀ r, pubExec.actual r → rho.key r.origin ∈ rho.honest →
    let nd := (Model.releaseAll (protoOf (compiled (goldilocks S)) E) rho.hash r.origin
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
instance is supplied, and this is not a new obligations assumption. -/
structure ForwardingContracts : Prop where
  executed : ∀ r, pubExec.actual r → ExecutedPublication S rho r
  /-- Completeness prevents selecting only convenient successful publications. Every actual
  executed candidate passing all three guards belongs to the publication relation. -/
  complete : ∀ r, ExecutedPublication S rho r →
    let nd := (Model.releaseAll (protoOf (compiled (goldilocks S)) E) rho.hash r.origin
      r.before (r.candidates.take r.index)).1
    Model.releasable nd.seen r.object = true →
    Model.protects (protoOf (compiled (goldilocks S)) E) r.origin nd.seen r.object = true →
    (protoOf (compiled (goldilocks S)) E).dependencies.ready (Model.closure nd.seen) r.object =
        true →
    pubExec.actual r
  origin : ForwardOrigin S rho hn tr cutMap pubExec
  atAcceptance : ForwardAtAcceptance S rho hn tr cutMap pubExec
  parentEarlier : ForwardParentEarlier S rho hn tr pubExec
  heldProcessed : ForwardHeldProcessed S rho hn tr cutMap
  objectsSeen : AcceptedObjectsSeen S rho pubExec

end Consensus.Goldilocks.Simulation
