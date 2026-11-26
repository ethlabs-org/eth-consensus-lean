module
public import ConsensusLean.Instances.Goldilocks.Results.Spec.NodeCanonicalTrace
public import ConsensusLean.Lemmas.Model.Objects
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts

public section

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Blocks Shape Node

section Traversal

variable {P : Params} {A : NodeAC P} {K I B S : Type} [DecidableEq I]
variable (C : WireCodec A K I B) (D : Adapter A K I B S) (hs : List (Header I × Nat))

mutual
private theorem visit_parts (st : S) (o : ShapeObj P.n K I B) :
    (visit C D hs st o).1 ⊆ o.parts := by
  cases o with
  | mk a m cs =>
    rw [visit]
    split
    · intro x hx
      rw [List.mem_singleton.mp hx]
      exact Model.Obj.Contains.refl _
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Model.Obj.Contains.refl _
      · obtain ⟨c, hc, hx⟩ := List.mem_flatMap.mp (visitList_parts _ _ hx)
        exact Model.Obj.Contains.step hc hx

private theorem visitList_parts (st : S) (os : List (ShapeObj P.n K I B)) :
    (visitList C D hs st os).1 ⊆ os.flatMap Model.Obj.parts := by
  cases os with
  | nil => simp [visitList]
  | cons o os =>
    rw [visitList, List.flatMap_cons]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (visit_parts _ _ hx)
    · exact List.mem_append_right _ (visitList_parts _ _ hx)
end

/-- A handler label for a decoded object in the visit list has a replay cut. -/
theorem deliverRecs_label (pr : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (y : Fin P.n) (t : Time) (i : Nat) (ev : Event A) (Q : Cut A → Prop)
    (os : List (ShapeObj P.n K I B)) (st : NodeState A) (sub : Nat)
    (hm : ∃ o ∈ os, canonEvent C hs o = some ev)
    (hlabel : ∀ s, ∃ l ls, (exec pr dg y s t ev).2 = l :: ls ∧ Q l) :
    ∃ r ∈ deliverRecs C pr dg hs y t i os st sub, Q r.label := by
  induction os generalizing st sub with
  | nil => simp at hm
  | cons o os ih =>
    obtain ⟨w, hw, hc⟩ := hm
    rw [deliverRecs_cons]
    rcases List.mem_cons.mp hw with rfl | hw
    · rw [hc]
      obtain ⟨l, ls, hl, hQ⟩ := hlabel st
      simp only [groupRecs_eq, hl, cutPosts_cons, List.zip_cons_cons, List.mapIdx_cons]
      exact ⟨_, List.mem_append_left _ List.mem_cons_self, hQ⟩
    · cases he : canonEvent C hs o with
      | none => exact ih st (sub + 1) ⟨w, hw, hc⟩
      | some ev =>
        obtain ⟨r, hr, hQ⟩ := ih _ (sub + 1) ⟨w, hw, hc⟩
        exact ⟨r, List.mem_append_right _ hr, hQ⟩

/-- A decoded message in the visit list has its own replay cut. -/
theorem deliverRecs_message_call (pr : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (y : Fin P.n) (t : Time) (i : Nat) (m : A.Msg)
    (os : List (ShapeObj P.n K I B)) (st : NodeState A) (sub : Nat)
    (hm : ∃ o ∈ os, canonEvent C hs o = some (.message m)) :
    ∃ r ∈ deliverRecs C pr dg hs y t i os st sub, ∃ l, r.label = .ac l ∧ l.call = .message m :=
  deliverRecs_label C hs pr dg y t i (.message m) (fun c => ∃ l, c = .ac l ∧ l.call = .message m)
    os st sub hm (by intro s; simp [exec, onMessage, acCall])

/-- Any object visited by a receipt is in the received object's recursive closure. -/
theorem contains_of_mem_delivered {st : S} {o w : ShapeObj P.n K I B}
    (hw : w ∈ delivered C D hs st o) : Model.Obj.Contains o w :=
  visit_parts C D hs st o hw

/-- The received root itself is visited, even on refusal. -/
theorem mem_delivered_self (st : S) (o : ShapeObj P.n K I B) : o ∈ delivered C D hs st o := by
  cases o with
  | mk a m cs =>
    rw [delivered, visit]
    split <;> exact List.mem_cons_self

/-- A delivery cut comes from the handler after replaying the preceding visited objects. -/
theorem mem_deliverRecs_prefix (pr : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload)
    (y : Fin P.n) (t : Time) (i : Nat) (os : List (ShapeObj P.n K I B)) (st : NodeState A)
    (sub : Nat) {r : CutRec A} (hr : r ∈ deliverRecs C pr dg hs y t i os st sub) :
    ∃ pre w post ev s, os = pre ++ w :: post ∧ canonEvent C hs w = some ev ∧ sub ≤ s ∧
      r ∈ groupRecs pr dg y (pre.foldl (fun σ o => ((canonEvent C hs o).map
        (fun e => (exec pr dg y σ t e).1)).getD σ) st) t (Nat.pair i s) ev := by
  induction os generalizing st sub with
  | nil => rw [deliverRecs_nil] at hr; cases hr
  | cons o os ih =>
    rw [deliverRecs_cons] at hr
    cases he : canonEvent C hs o with
    | none =>
      rw [he] at hr
      obtain ⟨pre, w, post, ev, s, hm, hcanon, hle, hl⟩ := ih st (sub + 1) hr
      exact ⟨o :: pre, w, post, ev, s, by rw [hm]; rfl, hcanon, by omega,
        by simpa only [List.foldl_cons, he, Option.map_none, Option.getD_none] using hl⟩
    | some ev =>
      rw [he] at hr
      rcases List.mem_append.mp hr with hg | hr
      · exact ⟨[], o, os, ev, sub, rfl, he, le_rfl, hg⟩
      · obtain ⟨pre, w, post, ev', s, hm, hcanon, hle, hl⟩ := ih _ (sub + 1) hr
        exact ⟨o :: pre, w, post, ev', s, by rw [hm]; rfl, hcanon, by omega,
          by simpa only [List.foldl_cons, he, Option.map_some, Option.getD_some] using hl⟩

private theorem mem_deliverRecs_group (pr : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload)
    (y : Fin P.n) (t : Time) (i : Nat) (os : List (ShapeObj P.n K I B)) (st : NodeState A)
    (sub : Nat) {r : CutRec A} (hr : r ∈ deliverRecs C pr dg hs y t i os st sub) :
    ∃ w ev st' s, w ∈ os ∧ canonEvent C hs w = some ev ∧ sub ≤ s ∧
      r ∈ groupRecs pr dg y st' t (Nat.pair i s) ev := by
  obtain ⟨pre, w, post, ev, s, rfl, hc, hle, hg⟩ :=
    mem_deliverRecs_prefix C hs pr dg y t i os st sub hr
  exact ⟨w, ev, _, s, List.mem_append_right _ List.mem_cons_self, hc, hle, hg⟩

/-- A delivery cut comes from the handler invocation for one of the delivered objects. -/
theorem mem_deliverRecs_exec (pr : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (y : Fin P.n) (t : Time) (i : Nat) (os : List (ShapeObj P.n K I B)) (st : NodeState A)
    (sub : Nat) {r : CutRec A} (hr : r ∈ deliverRecs C pr dg hs y t i os st sub) :
    ∃ w ev st', w ∈ os ∧ canonEvent C hs w = some ev ∧ r.label ∈ (exec pr dg y st' t ev).2 := by
  obtain ⟨w, ev, st', _, hm, he, _, hg⟩ := mem_deliverRecs_group C hs pr dg y t i os st sub hr
  rw [groupRecs_eq] at hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  rw [List.getElem_mapIdx, List.getElem_zip]
  exact ⟨w, ev, st', hm, he, List.getElem_mem _⟩

end Traversal

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
variable {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
variable {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
variable {hn : 1 ≤ Fintype.card V}
variable {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)} (e : Encoding F E p hN hn A)
variable (rho : Model.Run (compiled F) E)

omit [DecidableEq V] in
private theorem cast_selSpec {s q : ChainShape (Model.pubOf E) O.Id I} (h : s = q)
    (r : (compile q).Role) :
    (compile s).selSpec (cast (congrArg (fun x => (compile x).Role) h.symm) r) =
      (compile q).selSpec r := by
  cases h
  rfl

omit [DecidableEq V] in
/-- Selection uses the skeleton's specification for the encoded role. -/
theorem selSpec_engineRole (r : ShapeRole e.skel.Kind) :
    (Model.protoOf (compiled F) E).selSpec (engineRole e r) = e.skel.selSpec r := by
  rw [engineRole_eq]
  exact cast_selSpec e.shape_eq r

omit [DecidableEq V] in
private theorem cast_proposer {s q : ChainShape (Model.pubOf E) O.Id I} (h : s = q) (j : Slot) :
    (cast (congrArg (fun x => (compile x).Role) h.symm)
      (.proposer j : (compile q).Role) : (compile s).Role) = .proposer j := by
  cases h
  rfl

omit [DecidableEq V] in
/-- The encoded proposer role is the compiled proposer's role at the same slot. -/
theorem engineRole_proposer (s : Slot) :
    engineRole e (.proposer s) = (.proposer s : (Model.protoOf (compiled F) E).Role) :=
  (engineRole_eq e _).trans (cast_proposer e.shape_eq s)

omit [DecidableEq V] in
/-- A singleton proposer selection in an admitted run is exactly its run proposer. -/
theorem selValid_proposer (hsel : rho.SelValid) (s : Slot)
    (hs : e.skel.proposerSel s = .sized 1) :
    rho.sel (engineRole e (.proposer s)) = {runProposer rho hn s} := by
  have h := hsel (engineRole e (.proposer s))
  rw [selSpec_engineRole] at h
  simp only [Skeleton.selSpec, hs, Model.SelSpec.Admits, min_eq_left hn] at h
  rw [engineRole_proposer] at h ⊢
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h
  simp [runProposer_eq, hk]

/-- Observation coverage includes every time up to the engine horizon, even without actions. -/
theorem inHorizon_of_le {t : Time} (ht : t ≤ rho.horizon) : (simTrace e rho).InHorizon t := by
  refine ⟨(allCuts e rho).length, Or.inr ⟨rho.horizon, simTrace_observationHorizon e rho, ht⟩, ?_⟩
  rw [simTrace_time, List.getElem?_length, Option.elim_none]
  unfold Time at *
  omega

/-- Awake nodes are within the observation horizon. -/
theorem awake_in_horizon {y : Fin (Fintype.card V)} {t : Time}
    (hw : (simTrace e rho).awake y t) : (simTrace e rho).InHorizon t :=
  inHorizon_of_le e rho ((simTrace_awake_iff e rho y t).mp hw).2.2

/-- The handler origin of a delivery cut, expressed as a part of the actual engine object. -/
theorem delivery_origin {v : V} {i : Nat} {t : Time}
    {o : (Model.protoOf (compiled F) E).Object} (he : rho.events[i]? = some (.deliver v o t))
    {r : CutRec A} (hr : r ∈ eventCuts e rho i) :
    ∃ w ev st, (engineObj e w) ∈ o.parts ∧
      canonEvent (receiverCodec e rho v) (Model.digests rho.hash o) w = some ev ∧
      r.label ∈ (exec (runProposer rho hn) (digestOf e rho) (rho.ownKey v) st t ev).2 := by
  rw [eventCuts_deliver e rho i v o t he] at hr
  obtain ⟨w, ev, st, hm, hc, hl⟩ := mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ _ hr
  have hp := contains_of_mem_delivered _ _ _ hm
  refine ⟨w, ev, st, ?_, hc, hl⟩
  rw [← engineObj_wireOf e o, engineObj_parts]
  exact List.mem_map_of_mem hp

/-- An AC message cut of a delivery comes from a carried object decoded as that message,
not from a block. -/
theorem msgCall_delivered {v : V} {i : Nat} {t : Time}
    {o : (Model.protoOf (compiled F) E).Object} (he : rho.events[i]? = some (.deliver v o t))
    {r : CutRec A} (hr : r ∈ eventCuts e rho i) {l : ACLabel A} {m : A.Msg}
    (hl : r.label = .ac l) (hm : l.call = .message m) :
    ∃ w, engineObj e w ∈ o.parts ∧ (receiverCodec e rho v).message w = some m ∧
      decodeBlock e.codec.decode e.codec.carried A.validPayload (Model.digests rho.hash o) w =
        none := by
  obtain ⟨w, ev, st, hw, hce, hc⟩ := delivery_origin e rho he hr
  rw [hl] at hc
  have hcanon : ev = .message m := by
    cases ev with
    | tick x fgDue => unfold canonEvent at hce; split at hce <;> cases hce
    | restart => unfold canonEvent at hce; split at hce <;> cases hce
    | attestation a => simp [exec, onAttestation] at hc
    | message m' =>
      simp only [exec, onMessage, acCall, List.mem_singleton, Cut.ac.injEq] at hc
      subst l
      cases hm
      rfl
    | block b =>
      simp only [exec, onBlock] at hc
      split at hc
      · cases hc
      · split at hc <;> simp [acCall] at hc
        subst l
        cases hm
  subst ev
  refine ⟨w, hw, ?_⟩
  unfold canonEvent at hce
  split at hce <;> cases hce
  simp only [receiverCodec_eq] at *
  exact ⟨by assumption, by assumption⟩

/-- A delivery's FG block cut or AC block call comes from a part that decodes to that block. -/
theorem blockLabel_delivered {v : V} {i : Nat} {t : Time}
    {o : (Model.protoOf (compiled F) E).Object} (he : rho.events[i]? = some (.deliver v o t))
    {r : CutRec A} (hr : r ∈ eventCuts e rho i) {b : A.Blk}
    (hl : (∃ acc, r.label = .fg (.block b acc)) ∨ ∃ l, r.label = .ac l ∧ l.call = .block b) :
    ∃ w, engineObj e w ∈ o.parts ∧
      decodeBlock e.codec.decode e.codec.carried A.validPayload (Model.digests rho.hash o) w =
        some b := by
  obtain ⟨w, ev, st, hw, hce, hc⟩ := delivery_origin e rho he hr
  have hcanon : ev = .block b := by
    rcases hl with ⟨acc, hl⟩ | ⟨l, hl, hb⟩ <;> rw [hl] at hc
    · cases ev with
      | tick x fgDue => unfold canonEvent at hce; split at hce <;> cases hce
      | restart => simp [exec, Node.restart, acCall] at hc
      | attestation a => simp [exec, onAttestation] at hc
      | message m => simp [exec, onMessage, acCall] at hc
      | block b' =>
        simp only [exec, onBlock] at hc
        split at hc
        · cases hc
        · split at hc <;> simp [acCall] at hc <;> simp [hc.1]
    cases ev with
    | tick x fgDue => unfold canonEvent at hce; split at hce <;> cases hce
    | restart => unfold canonEvent at hce; split at hce <;> cases hce
    | attestation a => simp [exec, onAttestation] at hc
    | message m =>
      simp [exec, onMessage, acCall] at hc
      subst l
      cases hb
    | block b' =>
      simp only [exec, onBlock] at hc
      split at hc
      · cases hc
      · split at hc <;> simp [acCall] at hc
        subst l
        cases hb
        rfl
  subst ev
  refine ⟨w, hw, ?_⟩
  unfold canonEvent at hce
  simp only [receiverCodec_eq] at hce
  split at hce <;> cases hce
  assumption

/-- A delivery's FG block cut comes from a part that decodes to that block. -/
theorem blockCall_delivered {v : V} {i : Nat} {t : Time}
    {o : (Model.protoOf (compiled F) E).Object} (he : rho.events[i]? = some (.deliver v o t))
    {r : CutRec A} (hr : r ∈ eventCuts e rho i) {b : A.Blk} {acc : Bool}
    (hl : r.label = .fg (.block b acc)) :
    ∃ w, engineObj e w ∈ o.parts ∧
      decodeBlock e.codec.decode e.codec.carried A.validPayload (Model.digests rho.hash o) w =
        some b :=
  blockLabel_delivered e rho he hr (Or.inl ⟨acc, hl⟩)

omit [Countable I] in
/-- Successful decoding checks that the wire carries exactly the block's payload objects. -/
theorem carried_of_decodeBlock {Q : Params} {K B Payload : Type}
    {decode : I → Option (List (FG.Att Q.n) × Payload)}
    {carried : List (FG.Att Q.n) → Payload → List (ShapeObj Q.n K I B)}
    {valid : NodeBlock Q Payload → Prop} {hs : List (Header I × Nat)}
    {w : ShapeObj Q.n K I B} {b : NodeBlock Q Payload}
    (h : decodeBlock decode carried valid hs w = some b) :
    w.carried = carried b.fgPayload b.acPayload := by
  unfold decodeBlock at h
  split at h
  · split at h
    · simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h
      obtain ⟨⟨_, hc, _, _⟩, rfl⟩ := h
      exact hc
    · cases h
  · cases h

omit [Countable I] in
/-- Encode-after-decode recovers the canonical object of the decoded block. -/
theorem blockObj_of_decodeBlock {Q : Params} {K B Payload : Type}
    {encode : List (FG.Att Q.n) → Payload → I}
    {decode : I → Option (List (FG.Att Q.n) × Payload)}
    {carried : List (FG.Att Q.n) → Payload → List (ShapeObj Q.n K I B)}
    {valid : NodeBlock Q Payload → Prop} {hs : List (Header I × Nat)}
    {w : ShapeObj Q.n K I B} {b : NodeBlock Q Payload}
    (hd : decodeBlock decode carried valid hs w = some b)
    (hcodec : ∀ {info atts payload}, decode info = some (atts, payload) →
      encode atts payload = info) : blockObj encode carried b = w := by
  unfold decodeBlock at hd
  split at hd
  · rename_i k s header cs
    split at hd
    · rename_i atts payload root hdec hroot
      simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hd
      obtain ⟨⟨hpos, rfl, -, -⟩, rfl⟩ := hd
      obtain ⟨par, pos, input, info⟩ := header
      simp only at hpos hdec
      subst s
      simp only [blockObj, headerOf, blockOf, hcodec hdec]
      congr
      cases par with
      | root => simp [parentRoot, parentRef]
      | digest d =>
        simp only [parentRoot, parentRef, rawRoot, taggedRoot]
        split_ifs <;> simp_all <;> omega
    · cases hd
  · cases hd

/-- The canonical object of a replayed block occurs in the delivered object's closure.
The codec's encode-after-decode law recovers the header of the visited object. -/
theorem blockObj_delivered {v : V} {i : Nat} {t : Time}
    {o : (Model.protoOf (compiled F) E).Object} (he : rho.events[i]? = some (.deliver v o t))
    {r : CutRec A} (hr : r ∈ eventCuts e rho i) {b : A.Blk} {acc : Bool}
    (hl : r.label = .fg (.block b acc))
    (hcodec : ∀ {info atts payload}, e.codec.decode info = some (atts, payload) →
      e.codec.encode atts payload = info) :
    engineObj e (blockObj e.codec.encode e.codec.carried b) ∈ o.parts := by
  obtain ⟨w, hw, hd⟩ := blockCall_delivered e rho he hr hl
  rwa [blockObj_of_decodeBlock hd hcodec]

/-- The replay cut map is monotone: each next event appends its cuts. -/
theorem cutMap_mono : Monotone (cutMap e rho) :=
  monotone_nat_of_le_succ fun i => by rw [cutMap_succ]; exact Nat.le_add_right _ _

/-- Ordered cuts bounded by two event intervals force the same order on the event indices. -/
theorem cutMap_index_le {i i' k k' : Nat} (hk : cutMap e rho i ≤ k)
    (hk' : k' < cutMap e rho (i' + 1)) (h : k ≤ k') : i ≤ i' := by
  by_contra hlt
  have := cutMap_mono e rho (show i' + 1 ≤ i by omega)
  omega

/-- The engine cut map counts all replay cuts in the event prefix. -/
theorem prefix_cuts (n : Nat) :
    ((List.range n).flatMap (eventCuts e rho)).length = cutMap e rho n := by
  induction n with
  | zero => simp [cutMap_zero]
  | succ n ih => simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.length_append, ih, cutMap_succ]

/-- A cut in a prefix lies inside the cut-map interval of its engine event. -/
theorem cut_event_range (n k : Nat) (r : CutRec A)
    (hr : ((List.range n).flatMap (eventCuts e rho))[k]? = some r) :
    ∃ i < n, cutMap e rho i ≤ k ∧ k < cutMap e rho (i + 1) ∧
      (eventCuts e rho i)[k - cutMap e rho i]? = some r := by
  induction n with
  | zero => simp at hr
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] at hr
    by_cases hk : k < ((List.range n).flatMap (eventCuts e rho)).length
    · rw [List.getElem?_append_left hk] at hr
      obtain ⟨i, hi, hstart, hend, hm⟩ := ih hr
      exact ⟨i, by omega, hstart, hend, hm⟩
    · rw [List.getElem?_append_right (Nat.le_of_not_gt hk)] at hr
      rw [prefix_cuts e rho n] at hr hk
      have hlen := (List.getElem?_eq_some_iff.mp hr).1
      exact ⟨n, Nat.lt_succ_self _, by omega, by rw [cutMap_succ]; omega, hr⟩

/-- The indexed cut of an engine event occurs at the prefix length plus its local index. -/
theorem allCuts_getElem?_add (i j : Nat) (hi : i < rho.events.length)
    (hj : j < (eventCuts e rho i).length) :
    (allCuts e rho)[cutMap e rho i + j]? = (eventCuts e rho i)[j]? := by
  rw [allCuts_eq]
  generalize rho.events.length = n at hi ⊢
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have h := cutMap_mono e rho (Nat.succ_le_of_lt hi)
      rw [cutMap_succ] at h
      rw [List.getElem?_append_left (by rw [prefix_cuts]; omega), ih hi]
    · rw [List.getElem?_append_right (by rw [prefix_cuts]; omega), prefix_cuts,
        Nat.add_sub_cancel_left]

/-- A cut in a prefix belongs to an engine event in that prefix. -/
theorem cut_event (n k : Nat) (r : CutRec A)
    (hr : ((List.range n).flatMap (eventCuts e rho))[k]? = some r) :
    ∃ i < n, cutMap e rho i ≤ k ∧ r ∈ eventCuts e rho i := by
  obtain ⟨i, hi, hk, _, hm⟩ := cut_event_range e rho n k r hr
  exact ⟨i, hi, hk, List.mem_of_getElem? hm⟩

private theorem group_label_time {Q : Params} {N : NodeAC Q}
    (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (y : Fin Q.n) (st : NodeState N) (t : Time) (i : Nat) (ev : Node.Event N)
    {r : CutRec N} (hr : r ∈ groupRecs pr dg y st t i ev) :
    r.label ∈ (exec pr dg y st t ev).2 ∧ r.time = t ∧ r.node = y := by
  rw [groupRecs_eq] at hr
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
  rw [List.getElem_mapIdx, List.getElem_zip]
  exact ⟨List.getElem_mem _, rfl, rfl⟩

/-- A cut of an engine tick of `v` at `t` is a cut of its public tick group, or an own
admission (`mem_admitRecs`). -/
theorem mem_eventCuts_tick {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) {r : CutRec A} (hr : r ∈ eventCuts e rho i) :
    ((paramsAtCount p (Fintype.card V) hN hn).IsPublic t ∧
      r ∈ groupRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
        (e.adapter.node (stateAt e rho v i)) t (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t)) (e.adapter.sign (rho.ownKey v) t))) ∨
    ∃ j ≤ i, ∃ w : V, rho.events[j]? = some (.tick w t) ∧ ∃ a ∈ admitsAt e rho w j,
      ∃ (st : NodeState A) (s : Nat), 1 ≤ s ∧
        r ∈ groupRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey w) st t (Nat.pair j s)
          (.attestation a) := by
  rw [eventCuts_tick e rho i v t he] at hr
  rcases List.mem_append.mp hr with hr | hr
  · split at hr
    · exact Or.inl ⟨by assumption, hr⟩
    · cases hr
  · obtain ⟨a, ha, st, s, hs, hg⟩ := mem_admitRecs _ _ _ _ _ _ _ _ _ hr
    exact Or.inr ⟨i, le_rfl, v, he, a, ha, st, s, hs, hg⟩

omit [Countable I] in
private theorem delivery_node_time {Q : Params} {N : NodeAC Q} {K B : Type}
    (C : WireCodec N K I B) (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (hs : List (Header I × Nat)) (y : Fin Q.n) (t : Time) (i : Nat)
    (os : List (ShapeObj Q.n K I B)) (st : NodeState N) (sub : Nat)
    {r : CutRec N} (hr : r ∈ deliverRecs C pr dg hs y t i os st sub) :
    r.time = t ∧ r.node = y := by
  obtain ⟨_, _, _, _, _, _, _, hg⟩ := mem_deliverRecs_group C hs pr dg y t i os st sub hr
  exact (group_label_time _ _ _ _ _ _ _ hg).2

/-- A replay cut has the time of its enclosing engine event, and its node key, except an own
admission of the time's tick phase: the `.attestation` cut of the node of a tick at that time at
an event `j ≤ i`. -/
theorem eventCut_node_time {i : Nat} {ev : Model.Event V (Model.protoOf (compiled F) E).Object}
    (he : rho.events[i]? = some ev) {r : CutRec A} (hr : r ∈ eventCuts e rho i) :
    r.time = ev.time ∧ (r.node = rho.ownKey ev.node ∨ (∃ v, ev = .tick v ev.time) ∧
      ∃ j ≤ i, ∃ w : V, rho.events[j]? = some (.tick w ev.time) ∧ r.node = rho.ownKey w ∧
        ∃ a, r.label = .fg (.attestation a)) := by
  cases ev with
  | tick v t =>
    rcases mem_eventCuts_tick e rho he hr with ⟨-, hr⟩ | ⟨j, hj, w, hw, a, -, st, s, -, hr⟩
    · exact ⟨(group_label_time _ _ _ _ _ _ _ hr).2.1,
        Or.inl (group_label_time _ _ _ _ _ _ _ hr).2.2⟩
    · obtain ⟨hl, ht, hn⟩ := group_label_time _ _ _ _ _ _ _ hr
      refine ⟨ht, Or.inr ⟨⟨v, rfl⟩, j, hj, w, hw, hn, a, ?_⟩⟩
      simpa [exec, onAttestation] using hl
  | restart v t =>
    rw [eventCuts_restart e rho i v t he] at hr
    exact ⟨(group_label_time _ _ _ _ _ _ _ hr).2.1,
      Or.inl (group_label_time _ _ _ _ _ _ _ hr).2.2⟩
  | deliver v o t =>
    rw [eventCuts_deliver e rho i v o t he] at hr
    exact ⟨(delivery_node_time _ _ _ _ _ _ _ _ _ _ hr).1,
      Or.inl (delivery_node_time _ _ _ _ _ _ _ _ _ _ hr).2⟩

/-- A labelled trace cut lies in an engine event with the same time and node. -/
theorem labelled_cut_origin {k : Nat} {l : Cut A} (hl : (simTrace e rho).label k = some l) :
    ∃ i ev r, rho.events[i]? = some ev ∧ cutMap e rho i ≤ k ∧
      (eventCuts e rho i)[k - cutMap e rho i]? = some r ∧ r.label = l ∧
      (simTrace e rho).time k = ev.time ∧ ((simTrace e rho).node k = rho.ownKey ev.node ∨
        (∃ v, ev = .tick v ev.time) ∧ ∃ j ≤ i, ∃ w : V, rho.events[j]? = some (.tick w ev.time) ∧
          (simTrace e rho).node k = rho.ownKey w ∧ ∃ a, l = .fg (.attestation a)) ∧
      (simTrace e rho).pos k = r.pos ∧ (allCuts e rho)[k]? = some r ∧
      k < cutMap e rho (i + 1) := by
  rw [simTrace_label] at hl
  cases hk : (allCuts e rho)[k]? with
  | none => simp [hk] at hl
  | some r =>
    rw [hk] at hl
    have h := hk
    rw [allCuts_eq] at h
    obtain ⟨i, hi, hstart, hend, hr⟩ := cut_event_range e rho _ _ _ h
    have he := List.getElem?_eq_getElem hi
    obtain ⟨ht, hn⟩ := eventCut_node_time e rho he (List.mem_of_getElem? hr)
    rw [simTrace_time, simTrace_node, simTrace_pos, hk]
    have hrl := Option.some.inj hl
    refine ⟨i, _, r, he, hstart, hr, hrl, ht, ?_, rfl, rfl, hend⟩
    rcases hn with hn | ⟨hev, j, hj, w, hw, hn, a, ha⟩
    · exact Or.inl hn
    · exact Or.inr ⟨hev, j, hj, w, hw, hn, a, hrl ▸ ha⟩

private theorem group_id {Q : Params} {N : NodeAC Q}
    (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (y : Fin Q.n) (st : NodeState N) (t : Time) (id : Nat) (ev : Node.Event N)
    {r : CutRec N} (hr : r ∈ groupRecs pr dg y st t id ev) : r.event = id := by
  rw [groupRecs_eq] at hr
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
  rw [List.getElem_mapIdx]

/-- A cut of a handler group carries one of the handler's labels, the group's time, node and id. -/
theorem mem_groupRecs_fields {Q : Params} {N : NodeAC Q}
    (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (y : Fin Q.n) (st : NodeState N) (t : Time) (id : Nat) (ev : Node.Event N)
    {r : CutRec N} (hr : r ∈ groupRecs pr dg y st t id ev) :
    r.label ∈ (exec pr dg y st t ev).2 ∧ r.time = t ∧ r.node = y ∧ r.event = id :=
  ⟨(group_label_time pr dg y st t id ev hr).1, (group_label_time pr dg y st t id ev hr).2.1,
    (group_label_time pr dg y st t id ev hr).2.2, group_id pr dg y st t id ev hr⟩

omit [DecidableEq V] [DecidableEq I] [Countable I] in
/-- An `.attestation` handler group is one cut. -/
theorem groupRecs_attestation_length {Q : Params} {N : NodeAC Q}
    (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (y : Fin Q.n) (st : NodeState N) (t : Time) (id : Nat) (a : FG.Att Q.n) :
    (groupRecs pr dg y st t id (.attestation a)).length = 1 := by
  rw [groupRecs_eq]
  simp [exec, onAttestation, cutPosts_cons, cutPosts_nil]

omit [DecidableEq V] [DecidableEq I] [Countable I] in
/-- **The indexed own-admission replay** (records): one record per admitted attestation, the
`m`-th being the single cut of the `.attestation L[m]` group under the id `Nat.pair i (sub + m)`,
from the `on_attestation` fold of the first `m` attestations. -/
theorem admitRecs_getElem? {Q : Params} {N : NodeAC Q}
    (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (y : Fin Q.n) (t : Time) (i : Nat) :
    ∀ (L : List (FG.Att Q.n)) (st : NodeState N) (sub : Nat),
      (admitRecs pr dg y t i L st sub).length = L.length ∧
      ∀ m (hm : m < L.length), (admitRecs pr dg y t i L st sub)[m]? =
        (groupRecs pr dg y ((L.take m).foldl (fun n a => (exec pr dg y n t (.attestation a)).1)
          st) t (Nat.pair i (sub + m)) (.attestation L[m]))[0]?
  | [], st, sub => ⟨by rw [admitRecs_nil]; rfl, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
  | a :: L, st, sub => by
    obtain ⟨hlen, hget⟩ := admitRecs_getElem? pr dg y t i L
      (exec pr dg y st t (.attestation a)).1 (sub + 1)
    rw [admitRecs_cons]
    have hg1 := groupRecs_attestation_length pr dg y st t (Nat.pair i sub) a
    refine ⟨by rw [List.length_append, hg1, hlen, List.length_cons]; omega, fun m hm => ?_⟩
    rcases m with _ | m
    · rw [List.getElem?_append_left (by omega)]
      simp
    · rw [List.getElem?_append_right (by omega), hg1, Nat.add_sub_cancel,
        hget m (by simp at hm; omega)]
      simp only [List.take_succ_cons, List.foldl_cons, List.getElem_cons_succ]
      rw [show sub + 1 + m = sub + (m + 1) by omega]

omit [Countable I] in
/-- The subindex of a cut in a delivery suffix is at least the suffix's starting subindex. -/
theorem deliverRecs_id {Q : Params} {N : NodeAC Q} {K B : Type}
    (C : WireCodec N K I B) (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (hs : List (Header I × Nat)) (y : Fin Q.n) (t : Time) (i : Nat)
    (os : List (ShapeObj Q.n K I B)) (st : NodeState N) (sub : Nat) {r : CutRec N}
    (hr : r ∈ deliverRecs C pr dg hs y t i os st sub) :
    ∃ s, sub ≤ s ∧ r.event = Nat.pair i s := by
  obtain ⟨_, _, _, s, _, _, hle, hg⟩ := mem_deliverRecs_group _ _ _ _ _ _ _ _ _ _ hr
  exact ⟨s, hle, group_id _ _ _ _ _ _ _ hg⟩

/-- **The origin of a replay cut**: at its engine event's time, either at the event's node
under an id `Nat.pair i s`, or an own admission of a tick event `j ≤ i` at that time: an
`.attestation` cut of the tick's node under an id `Nat.pair j s` with `1 ≤ s`, inside a tick. -/
theorem eventCut_origin {i : Nat} {ev : Model.Event V (Model.protoOf (compiled F) E).Object}
    (he : rho.events[i]? = some ev) {r : CutRec A} (hr : r ∈ eventCuts e rho i) :
    r.time = ev.time ∧ ((r.node = rho.ownKey ev.node ∧ ∃ s, r.event = Nat.pair i s) ∨
      (∃ v, ev = .tick v ev.time) ∧ (∃ a, r.label = .fg (.attestation a)) ∧
        ∃ j ≤ i, ∃ w : V, rho.events[j]? = some (.tick w ev.time) ∧ r.node = rho.ownKey w ∧
          ∃ s, 1 ≤ s ∧ r.event = Nat.pair j s) := by
  cases ev with
  | tick v t =>
    rcases mem_eventCuts_tick e rho he hr with ⟨-, hr⟩ | ⟨j, hj, w, hw, a, -, st, s, hs, hr⟩
    · obtain ⟨-, ht, hn⟩ := group_label_time _ _ _ _ _ _ _ hr
      exact ⟨ht, Or.inl ⟨hn, 0, group_id _ _ _ _ _ _ _ hr⟩⟩
    · obtain ⟨hl, ht, hn⟩ := group_label_time _ _ _ _ _ _ _ hr
      refine ⟨ht, Or.inr ⟨⟨v, rfl⟩, ⟨a, ?_⟩, j, hj, w, hw, hn, s, hs, group_id _ _ _ _ _ _ _ hr⟩⟩
      simpa [exec, onAttestation] using hl
  | restart v t =>
    rw [eventCuts_restart e rho i v t he] at hr
    obtain ⟨-, ht, hn⟩ := group_label_time _ _ _ _ _ _ _ hr
    exact ⟨ht, Or.inl ⟨hn, 0, group_id _ _ _ _ _ _ _ hr⟩⟩
  | deliver v o t =>
    rw [eventCuts_deliver e rho i v o t he] at hr
    obtain ⟨s, _, hid⟩ := deliverRecs_id _ _ _ _ _ _ _ _ _ _ hr
    obtain ⟨ht, hn⟩ := delivery_node_time _ _ _ _ _ _ _ _ _ _ hr
    exact ⟨ht, Or.inl ⟨hn, s, hid⟩⟩

private def cutPhase {Q : Params} {N : NodeAC Q} : Cut N → Nat
  | .ac l => match l.call with
    | .restart => 0
    | .tick => 1
    | _ => 2
  | .fg _ => 2

private theorem cutPhase_exec {Q : Params} {N : NodeAC Q}
    (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (y : Fin Q.n) (st : NodeState N) (t : Time) (ev : Node.Event N) {c : Cut N}
    {cs : List (Cut N)} (hc : (exec pr dg y st t ev).2 = c :: cs) :
    cutPhase c = ev.phase := by
  cases ev with
  | tick x fgDue =>
    obtain ⟨l, _, _, hl, hs, _, _⟩ := Compose.tick_order pr dg y st t x fgDue
    change (onTick pr dg y st t x fgDue).2 = _ at hc
    rw [hs] at hc
    obtain ⟨rfl, -⟩ := List.cons.inj hc
    simp [cutPhase, hl, Node.Event.phase]
  | block b =>
    simp only [exec, onBlock, acCall] at hc
    split_ifs at hc
    all_goals first | cases hc | (split at hc <;> (obtain ⟨rfl, -⟩ := List.cons.inj hc; rfl))
  | message m =>
    simp only [exec, onMessage, acCall] at hc
    obtain ⟨rfl, -⟩ := List.cons.inj hc
    rfl
  | attestation a =>
    simp only [exec, onAttestation] at hc
    obtain ⟨rfl, -⟩ := List.cons.inj hc
    rfl
  | restart =>
    simp only [exec, Node.restart, acCall] at hc
    obtain ⟨rfl, -⟩ := List.cons.inj hc
    rfl

private theorem first_group_phase {Q : Params} {N : NodeAC Q}
    (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (y : Fin Q.n) (st : NodeState N) (t : Time) (id : Nat) (ev : Node.Event N)
    {r : CutRec N} (hr : r ∈ groupRecs pr dg y st t id ev) (h0 : r.pos = 0) :
    cutPhase r.label = ev.phase := by
  rw [groupRecs_eq] at hr
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
  rw [List.getElem_mapIdx] at h0 ⊢
  change k = 0 at h0
  subst k
  rw [List.getElem_zip]
  simp only [List.length_mapIdx, List.length_zip, lt_min_iff] at hk
  have hpos : 0 < (exec pr dg y st t ev).2.length := hk.1
  obtain ⟨c, cs, hs⟩ := List.exists_cons_of_length_pos hpos
  change cutPhase (exec pr dg y st t ev).2[0] = ev.phase
  rw [List.getElem_of_eq hs]
  exact cutPhase_exec pr dg y st t ev hs

/-- The first cut of a handler group identifies the handler's phase. -/
theorem groupRecs_phase_of_pos_zero {Q : Params} {N : NodeAC Q}
    (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (y : Fin Q.n) (st : NodeState N) (t : Time) (id : Nat) (ev : Node.Event N)
    {r : CutRec N} (hr : r ∈ groupRecs pr dg y st t id ev) (h0 : r.pos = 0)
    {pr' : Nat → Fin Q.n} {dg' : Digest (List (FG.Att Q.n)) N.Payload} {y' : Fin Q.n}
    {st' : NodeState N} {t' : Time} {ev' : Node.Event N} {cs : List (Cut N)}
    (hc : (exec pr' dg' y' st' t' ev').2 = r.label :: cs) : ev'.phase = ev.phase :=
  (cutPhase_exec pr' dg' y' st' t' ev' hc).symm.trans (first_group_phase pr dg y st t id ev hr h0)

/-- The handler identified by the first cut of a replay group has the enclosing event's phase,
except an own admission of a tick's time, an attestation (the delivery phase). -/
theorem phase_of_pos_zero {i : Nat}
    {ev : Model.Event V (Model.protoOf (compiled F) E).Object}
    (he : rho.events[i]? = some ev) {r : CutRec A} (hr : r ∈ eventCuts e rho i)
    (h0 : r.pos = 0) {dg : Digest (List (FG.Att (Fintype.card V))) A.Payload}
    {y : Fin (Fintype.card V)} {st : NodeState A} {t : Time} {ev' : Node.Event A}
    {cs : List (Cut A)} {pr : Nat → Fin (Fintype.card V)}
    (hc : (exec pr dg y st t ev').2 = r.label :: cs) :
    ev'.phase = ev.phase ∨ ((∃ v t, ev = .tick v t) ∧ ev'.phase = 2) := by
  have hphase : cutPhase r.label = ev'.phase :=
    cutPhase_exec (N := A) pr dg y st t ev' hc
  rw [← hphase]
  cases ev with
  | tick v t =>
    rcases mem_eventCuts_tick e rho he hr with ⟨-, hr⟩ | ⟨j, -, w, -, a, -, st, s, -, hr⟩
    · exact Or.inl (first_group_phase (N := A) _ _ _ _ _ _ _ hr h0)
    · exact Or.inr ⟨⟨v, t, rfl⟩, first_group_phase (N := A) _ _ _ _ _ _ _ hr h0⟩
  | restart v t =>
    rw [eventCuts_restart e rho i v t he] at hr
    exact Or.inl (first_group_phase (N := A) _ _ _ _ _ _ _ hr h0)
  | deliver v o t =>
    rw [eventCuts_deliver e rho i v o t he] at hr
    obtain ⟨w, ev, st', s, _, hw, _, hg⟩ := mem_deliverRecs_group _ _ _ _ _ _ _ _ _ _ hr
    left
    rw [first_group_phase (N := A) _ _ _ _ _ _ _ hg h0]
    unfold canonEvent at hw
    split at hw <;> cases hw <;> rfl

private theorem restart_of_mem_exec {Q : Params} {N : NodeAC Q}
    (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (y : Fin Q.n) (st : NodeState N) (t : Time) (ev : Node.Event N) {l : ACLabel N}
    (hc : Cut.ac l ∈ (exec pr dg y st t ev).2) (hl : l.call = .restart) : ev = .restart := by
  cases ev with
  | tick x fgDue =>
    obtain ⟨l₀, pc, uc, hl₀, hcs, hp, hu⟩ := Compose.tick_order pr dg y st t x fgDue
    change _ ∈ (onTick pr dg y st t x fgDue).2 at hc
    rw [hcs] at hc
    exfalso
    rcases List.mem_cons.mp hc with h | h
    · cases h; simp [hl] at hl₀
    rcases List.mem_append.mp h with h | h
    · rcases hp with ⟨-, rfl⟩ | ⟨-, l₂, hl₂, hp⟩
      · simp at h
      rcases hp with rfl | ⟨B, -, -, rfl | ⟨l₃, hl₃, rfl⟩⟩
      · simp only [List.mem_singleton, Cut.ac.injEq] at h; subst h; simp [hl] at hl₂
      · simp only [List.mem_cons, Cut.ac.injEq, reduceCtorEq, List.not_mem_nil, or_false] at h
        subst h; simp [hl] at hl₂
      · simp only [List.mem_cons, Cut.ac.injEq, reduceCtorEq, List.not_mem_nil, or_false,
          false_or] at h
        rcases h with rfl | rfl
        · simp [hl] at hl₂
        · simp [hl] at hl₃
    · cases fgDue
      · change uc = [] at hu
        simp [hu] at h
      · obtain ⟨l₁, hl₁, hu⟩ := (show Compose.UpdateCuts uc from hu)
        rcases hu with rfl | ⟨C, rfl⟩ | ⟨C, a, rfl⟩ <;>
        simp only [List.mem_cons, Cut.ac.injEq, reduceCtorEq, List.not_mem_nil, or_false] at h <;>
        (subst h; simp [hl] at hl₁)
  | block B =>
    simp only [exec, onBlock, acCall] at hc
    exfalso
    split_ifs at hc
    · simp at hc
    · split at hc
      · simp at hc
      · simp only [List.mem_cons, reduceCtorEq, Cut.ac.injEq, List.not_mem_nil, or_false,
          false_or] at hc
        subst hc; simp at hl
  | message m =>
    simp only [exec, onMessage, acCall, List.mem_singleton, Cut.ac.injEq] at hc
    subst hc; simp at hl
  | attestation a => simp [exec, onAttestation] at hc
  | restart => rfl

/-- Only the replay of an engine restart contains a restart cut. -/
theorem restart_of_mem_eventCuts {i : Nat}
    {ev : Model.Event V (Model.protoOf (compiled F) E).Object}
    (he : rho.events[i]? = some ev) {r : CutRec A} (hr : r ∈ eventCuts e rho i)
    {l : ACLabel A} (hlabel : r.label = .ac l) (hl : l.call = .restart) :
    ∃ v t, ev = .restart v t := by
  cases ev with
  | restart v t => exact ⟨v, t, rfl⟩
  | tick v t =>
    rcases mem_eventCuts_tick e rho he hr with ⟨-, hr⟩ | ⟨j, -, w, -, a, -, st, s, -, hr⟩ <;>
    · have hc := (group_label_time _ _ _ _ _ _ _ hr).1
      rw [hlabel] at hc
      cases restart_of_mem_exec _ _ _ _ _ _ hc hl
  | deliver v o t =>
    rw [eventCuts_deliver e rho i v o t he] at hr
    obtain ⟨w, ev, st, _, he, hc⟩ := mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ _ hr
    rw [hlabel] at hc
    rw [restart_of_mem_exec _ _ _ _ _ _ hc hl] at he
    unfold canonEvent at he
    split at he <;> cases he

private theorem tick_no_message {Q : Params} {N : NodeAC Q}
    (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (y : Fin Q.n) (st : NodeState N) (t : Time) (x : Nat) {fgDue : Bool}
    {l : ACLabel N} {m : N.Msg}
    (hc : Cut.ac l ∈ (exec pr dg y st t (.tick x fgDue)).2) (hm : l.call = .message m) : False := by
  obtain ⟨l₀, pc, uc, hl₀, hcs, hp, hu⟩ := Compose.tick_order pr dg y st t x fgDue
  change Cut.ac l ∈ (onTick pr dg y st t x fgDue).2 at hc
  rw [hcs] at hc
  rcases List.mem_cons.mp hc with h | h
  · cases h; rw [hm] at hl₀; cases hl₀
  rcases List.mem_append.mp h with h | h
  · rcases hp with ⟨-, rfl⟩ | ⟨-, l₂, hl₂, hp⟩
    · simp at h
    rcases hp with rfl | ⟨_, -, -, rfl | ⟨l₃, hl₃, rfl⟩⟩
    · simp only [List.mem_singleton, Cut.ac.injEq] at h
      subst h; rw [hm] at hl₂; cases hl₂
    · simp only [List.mem_cons, Cut.ac.injEq, reduceCtorEq, List.not_mem_nil, or_false] at h
      subst h; rw [hm] at hl₂; cases hl₂
    · simp only [List.mem_cons, Cut.ac.injEq, reduceCtorEq, List.not_mem_nil, or_false,
        false_or] at h
      rcases h with rfl | rfl
      · rw [hm] at hl₂; cases hl₂
      · rw [hm] at hl₃; cases hl₃
  · cases fgDue
    · change uc = [] at hu
      simp [hu] at h
    · obtain ⟨l₁, hl₁, hu⟩ := (show Compose.UpdateCuts uc from hu)
      rcases hu with rfl | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;>
      simp only [List.mem_cons, Cut.ac.injEq, reduceCtorEq, List.not_mem_nil, or_false] at h <;>
      (subst h; rw [hm] at hl₁; cases hl₁)

/-- A message call of the full canonical trace is a cut of a delivery of a part decoding to
that message. The cut starts no earlier than the engine event's mapped index. -/
theorem simTraceAt_msgCall_delivered {y : Fin (Fintype.card V)} {k : Nat} {m : A.Msg}
    (hc : (simTraceAt e rho).MsgCallAt y k m) :
    ∃ i v o t w, rho.events[i]? = some (.deliver v o t) ∧ engineObj e w ∈ o.parts ∧
      (receiverCodec e rho v).message w = some m ∧
      cutMap e rho i ≤ k ∧ (simTraceAt e rho).time k = t := by
  rw [simTraceAt_eq] at hc ⊢
  obtain ⟨l, ⟨_, hl⟩, hm⟩ := hc
  rw [simTrace_label] at hl
  cases hr : (allCuts e rho)[k]? with
  | none => simp [hr] at hl
  | some r =>
    rw [hr] at hl
    have hrl : r.label = .ac l := Option.some.inj hl
    have hcut := hr
    rw [allCuts_eq] at hcut
    obtain ⟨i, hi, hstart, hmem⟩ := cut_event e rho _ _ _ hcut
    cases he : rho.events[i] with
    | tick v t =>
      have ht : rho.events[i]? = some (.tick v t) :=
        (List.getElem?_eq_getElem hi).trans (congrArg some he)
      rcases mem_eventCuts_tick e rho ht hmem with ⟨-, hmem⟩ | ⟨j, -, w, -, a, -, st, s, -, hmem⟩
      · exact (tick_no_message _ _ _ _ _ _ (hrl ▸ (group_label_time _ _ _ _ _ _ _ hmem).1) hm).elim
      · have hh := (group_label_time _ _ _ _ _ _ _ hmem).1
        rw [hrl] at hh
        simp [exec, onAttestation] at hh
    | restart v t =>
      have ht : rho.events[i]? = some (.restart v t) :=
        (List.getElem?_eq_getElem hi).trans (congrArg some he)
      rw [eventCuts_restart e rho i v t ht] at hmem
      have hh := (group_label_time _ _ _ _ _ _ _ hmem).1
      rw [hrl] at hh
      simp [exec, Node.restart, acCall] at hh
      subst l
      cases hm
    | deliver v o t =>
      have ht : rho.events[i]? = some (.deliver v o t) :=
        (List.getElem?_eq_getElem hi).trans (congrArg some he)
      obtain ⟨w, hw, hd, _⟩ := msgCall_delivered e rho ht hmem hrl hm
      rw [simTrace_time, hr]
      exact ⟨i, v, o, t, w, ht, hw, hd, hstart, (eventCut_node_time e rho ht hmem).1⟩

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace
