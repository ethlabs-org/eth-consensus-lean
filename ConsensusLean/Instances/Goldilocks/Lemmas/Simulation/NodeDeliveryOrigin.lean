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

/-- Any object visited by a receipt is in the received object's recursive closure. -/
theorem contains_of_mem_delivered {st : S} {o w : ShapeObj P.n K I B}
    (hw : w ∈ delivered C D hs st o) : Model.Obj.Contains o w :=
  visit_parts C D hs st o hw

/-- A delivery cut comes from the handler invocation for one of the delivered objects. -/
theorem mem_deliverRecs_exec (pr : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (y : Fin P.n) (t : Time) (i : Nat) (os : List (ShapeObj P.n K I B)) (st : NodeState A)
    (sub : Nat) {r : CutRec A} (hr : r ∈ deliverRecs C pr dg hs y t i os st sub) :
    ∃ w ev st', w ∈ os ∧ canonEvent C hs w = some ev ∧ r.label ∈ (exec pr dg y st' t ev).2 := by
  induction os generalizing st sub with
  | nil => rw [deliverRecs_nil] at hr; cases hr
  | cons o os ih =>
    rw [deliverRecs_cons] at hr
    cases he : canonEvent C hs o with
    | none =>
      rw [he] at hr
      obtain ⟨w, ev, st', hm, hcanon, hl⟩ := ih st (sub + 1) hr
      exact ⟨w, ev, st', List.mem_cons_of_mem _ hm, hcanon, hl⟩
    | some ev =>
      rw [he] at hr
      rcases List.mem_append.mp hr with hg | hr
      · rw [groupRecs_eq] at hg
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
        rw [List.getElem_mapIdx, List.getElem_zip]
        exact ⟨o, ev, st, List.mem_cons_self, he, List.getElem_mem _⟩
      · obtain ⟨w, ev', st', hm, hcanon, hl⟩ := ih _ (sub + 1) hr
        exact ⟨w, ev', st', List.mem_cons_of_mem _ hm, hcanon, hl⟩

end Traversal

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
variable {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
variable {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
variable {hn : 1 ≤ Fintype.card V}
variable {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)} (e : Encoding F E p hN hn A)
variable (rho : Model.Run (compiled F) E)

/-- The handler origin of a delivery cut, expressed as a part of the actual engine object. -/
theorem delivery_origin {v : V} {i : Nat} {t : Time}
    {o : (Model.protoOf (compiled F) E).Object} (he : rho.events[i]? = some (.deliver v o t))
    {r : CutRec A} (hr : r ∈ eventCuts e rho i) :
    ∃ w ev st, (engineObj e w) ∈ o.parts ∧
      canonEvent e.codec (Model.digests rho.hash o) w = some ev ∧
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
    ∃ w, engineObj e w ∈ o.parts ∧ e.codec.message w = some m ∧
      decodeBlock e.codec.decode e.codec.carried A.validPayload (Model.digests rho.hash o) w =
        none := by
  obtain ⟨w, ev, st, hw, hce, hc⟩ := delivery_origin e rho he hr
  rw [hl] at hc
  have hcanon : ev = .message m := by
    cases ev with
    | tick x => unfold canonEvent at hce; split at hce <;> cases hce
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
      | tick x => unfold canonEvent at hce; split at hce <;> cases hce
      | restart => simp [exec, Node.restart, acCall] at hc
      | attestation a => simp [exec, onAttestation] at hc
      | message m => simp [exec, onMessage, acCall] at hc
      | block b' =>
        simp only [exec, onBlock] at hc
        split at hc
        · cases hc
        · split at hc <;> simp [acCall] at hc <;> simp [hc.1]
    cases ev with
    | tick x => unfold canonEvent at hce; split at hce <;> cases hce
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
      suffices heq : blockObj e.codec.encode e.codec.carried
          (blockOf root ⟨par, pos, input, info⟩ k atts payload) =
          .mk (.signed k (.proposer pos)) (.item ⟨par, pos, input, info⟩)
            (e.codec.carried atts payload) by
        rw [heq]
        exact hw
      simp only [blockObj, headerOf, blockOf, hcodec hdec]
      congr
      cases par with
      | root => simp [parentRoot, parentRef]
      | digest d =>
        simp only [parentRoot, parentRef, rawRoot, taggedRoot]
        split_ifs <;> simp_all <;> omega
    · cases hd
  · cases hd

private theorem prefix_cuts (n : Nat) :
    ((List.range n).flatMap (eventCuts e rho)).length = cutMap e rho n := by
  induction n with
  | zero => simp [cutMap_zero]
  | succ n ih => simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.length_append, ih, cutMap_succ]

private theorem cut_event (n k : Nat) (r : CutRec A)
    (hr : ((List.range n).flatMap (eventCuts e rho))[k]? = some r) :
    ∃ i < n, cutMap e rho i ≤ k ∧ r ∈ eventCuts e rho i := by
  induction n with
  | zero => simp at hr
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] at hr
    by_cases hk : k < ((List.range n).flatMap (eventCuts e rho)).length
    · rw [List.getElem?_append_left hk] at hr
      obtain ⟨i, hi, hstart, hm⟩ := ih hr
      exact ⟨i, by omega, hstart, hm⟩
    · rw [List.getElem?_append_right (Nat.le_of_not_gt hk)] at hr
      exact ⟨n, Nat.lt_succ_self _, (prefix_cuts e rho n).symm ▸ Nat.le_of_not_gt hk,
        List.mem_of_getElem? hr⟩

private theorem group_label_time {Q : Params} {N : NodeAC Q}
    (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (y : Fin Q.n) (st : NodeState N) (t : Time) (i : Nat) (ev : Node.Event N)
    {r : CutRec N} (hr : r ∈ groupRecs pr dg y st t i ev) :
    r.label ∈ (exec pr dg y st t ev).2 ∧ r.time = t := by
  rw [groupRecs_eq] at hr
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
  rw [List.getElem_mapIdx, List.getElem_zip]
  exact ⟨List.getElem_mem _, rfl⟩

omit [Countable I] in
private theorem delivery_time {Q : Params} {N : NodeAC Q} {K B : Type}
    (C : WireCodec N K I B) (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (hs : List (Header I × Nat)) (y : Fin Q.n) (t : Time) (i : Nat)
    (os : List (ShapeObj Q.n K I B)) (st : NodeState N) (sub : Nat)
    {r : CutRec N} (hr : r ∈ deliverRecs C pr dg hs y t i os st sub) : r.time = t := by
  induction os generalizing st sub with
  | nil => rw [deliverRecs_nil] at hr; cases hr
  | cons o os ih =>
    rw [deliverRecs_cons] at hr
    cases he : canonEvent C hs o with
    | none => rw [he] at hr; exact ih _ _ hr
    | some ev =>
      rw [he] at hr
      rcases List.mem_append.mp hr with hg | hr
      · exact (group_label_time _ _ _ _ _ _ _ hg).2
      · exact ih _ _ hr

private theorem tick_no_message {Q : Params} {N : NodeAC Q}
    (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (y : Fin Q.n) (st : NodeState N) (t : Time) (x : Nat) {l : ACLabel N} {m : N.Msg}
    (hc : Cut.ac l ∈ (exec pr dg y st t (.tick x)).2) (hm : l.call = .message m) : False := by
  obtain ⟨l₀, pc, uc, hl₀, hcs, hp, ⟨l₁, hl₁, hu⟩⟩ := Compose.tick_order pr dg y st t x
  change Cut.ac l ∈ (onTick pr dg y st t x).2 at hc
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
  · rcases hu with rfl | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;>
      simp only [List.mem_cons, Cut.ac.injEq, reduceCtorEq, List.not_mem_nil, or_false] at h <;>
      (subst h; rw [hm] at hl₁; cases hl₁)

/-- A message call of the full canonical trace is a cut of a delivery of a part decoding to
that message. The cut starts no earlier than the engine event's mapped index. -/
theorem simTraceAt_msgCall_delivered {y : Fin (Fintype.card V)} {k : Nat} {m : A.Msg}
    (hc : (simTraceAt e rho).MsgCallAt y k m) :
    ∃ i v o t w, rho.events[i]? = some (.deliver v o t) ∧ engineObj e w ∈ o.parts ∧
      e.codec.message w = some m ∧ cutMap e rho i ≤ k ∧ (simTraceAt e rho).time k = t := by
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
      rw [eventCuts_tick e rho i v t ht] at hmem
      split at hmem
      · exact (tick_no_message _ _ _ _ _ _ (hrl ▸ (group_label_time _ _ _ _ _ _ _ hmem).1) hm).elim
      · cases hmem
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
      rw [eventCuts_deliver e rho i v o t ht] at hmem
      rw [simTrace_time, hr]
      exact ⟨i, v, o, t, w, ht, hw, hd, hstart, delivery_time _ _ _ _ _ _ _ _ _ _ hmem⟩

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace
