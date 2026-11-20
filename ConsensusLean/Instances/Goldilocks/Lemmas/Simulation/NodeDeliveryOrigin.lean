module
public import ConsensusLean.Instances.Goldilocks.Results.Spec.NodeCanonicalTrace
public import ConsensusLean.Lemmas.Model.Objects

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

/-- A delivery's FG block cut comes from a part that decodes to that block. -/
theorem blockCall_delivered {v : V} {i : Nat} {t : Time}
    {o : (Model.protoOf (compiled F) E).Object} (he : rho.events[i]? = some (.deliver v o t))
    {r : CutRec A} (hr : r ∈ eventCuts e rho i) {b : A.Blk} {acc : Bool}
    (hl : r.label = .fg (.block b acc)) :
    ∃ w, engineObj e w ∈ o.parts ∧
      decodeBlock e.codec.decode e.codec.carried A.validPayload (Model.digests rho.hash o) w =
        some b := by
  obtain ⟨w, ev, st, hw, hce, hc⟩ := delivery_origin e rho he hr
  rw [hl] at hc
  have hcanon : ev = .block b := by
    cases ev with
    | tick x => unfold canonEvent at hce; split at hce <;> cases hce
    | restart => simp [exec, Node.restart, acCall] at hc
    | attestation a => simp [exec, onAttestation] at hc
    | message m => simp [exec, onMessage, acCall] at hc
    | block b' =>
      simp only [exec, onBlock] at hc
      split at hc
      · cases hc
      · split at hc <;> simp [acCall] at hc <;> simp [hc.1]
  subst ev
  refine ⟨w, hw, ?_⟩
  unfold canonEvent at hce
  split at hce <;> cases hce
  assumption

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

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace
