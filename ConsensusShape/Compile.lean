module
public import ConsensusShape.Protocol
public import Mathlib.Logic.Equiv.List
public import ConsensusModel.System
@[expose] public section

namespace Consensus.Shape
open AvailableChain (Slot Time)

def encodeTxs (xs : List Nat) : Nat := Encodable.encode xs

def decodeTxs (n : Nat) : List Nat := (Encodable.decode n).getD []

@[simp] theorem decode_encodeTxs (xs : List Nat) : decodeTxs (encodeTxs xs) = xs := by
  simp [decodeTxs, encodeTxs]

/-- Keep the first occurrence, including across block boundaries. -/
def keepFresh (seen : List Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => if x ∈ seen then keepFresh seen xs else x :: keepFresh (x :: seen) xs

def keepFirst (xs : List Nat) : List Nat := keepFresh [] xs

theorem keepFresh_append (seen xs ys : List Nat) :
    ∃ zs, keepFresh seen (xs ++ ys) = keepFresh seen xs ++ zs := by
  induction xs generalizing seen with
  | nil => exact ⟨keepFresh seen ys, rfl⟩
  | cons x xs ih =>
    simp only [List.cons_append, keepFresh]
    split
    · exact ih seen
    · obtain ⟨zs, hz⟩ := ih (x :: seen)
      exact ⟨zs, by rw [hz]; rfl⟩

theorem mem_keepFresh (x : Nat) (seen xs : List Nat) :
    x ∈ keepFresh seen xs ↔ x ∈ xs ∧ x ∉ seen := by
  classical
  induction xs generalizing seen with
  | nil => simp [keepFresh]
  | cons y ys ih =>
    simp only [keepFresh]
    by_cases hxy : x = y
    · subst y; by_cases hx : x ∈ seen <;> simp [hx, ih]
    · by_cases hy : y ∈ seen <;> simp [hy, ih, hxy]

theorem keepFirst_prefix {xs ys : List Nat} (h : xs <+: ys) :
    keepFirst xs <+: keepFirst ys := by
  obtain ⟨zs, rfl⟩ := h
  obtain ⟨ws, hw⟩ := keepFresh_append [] xs zs
  exact ⟨ws, hw.symm⟩

def ledgerOf (c : Chain) : Ledger := keepFirst (c.flatMap (decodeTxs ∘ Header.input))

theorem ledgerOf_prefix {c d : Chain} (h : c <+: d) : ledgerOf c <+: ledgerOf d := by
  obtain ⟨es, rfl⟩ := h
  apply keepFirst_prefix
  exact ⟨es.flatMap (decodeTxs ∘ Header.input), by simp⟩

@[simp] theorem mem_ledgerOf (x : Tx) (c : Chain) :
    x ∈ ledgerOf c ↔ ∃ h ∈ c, x ∈ decodeTxs h.input := by
  simp [ledgerOf, keepFirst, mem_keepFresh, List.mem_flatMap, Function.comp_def]

def compile {pub : Model.Public} (P : ShapeProtocol pub) : Model.Protocol pub where
  State := P.State × List Tx
  Label := P.Label ⊕ Slot
  Duty := P.Duty ⊕ Slot
  Item := Header
  Body := P.Body
  Durable := P.Durable
  decLabel := inferInstance
  decItem := inferInstance
  decBody := inferInstance
  encItem := inferInstance
  seats := shapeSeats pub.n
  label := Sum.elim (Sum.inl ∘ P.label) Sum.inr
  actTime := Sum.elim P.actTime P.proposalTime
  duties t := (P.slotAt? t).toList.map Sum.inr ++ (P.duties t).map Sum.inl
  duties_spec := by
    intro d t
    cases d with
    | inl d => simp [P.duties_spec]
    | inr s => simp [P.slotAt?_eq_some]
  duties_nodup := by
    intro t
    simp only [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · exact (Option.toList_nodup _).map Sum.inr_injective
    · exact (P.duties_nodup t).map Sum.inl_injective
    · simp
  init := (P.init, [])
  clock st t xs := (P.clock st.1 t, xs)
  act st d := match d with
    | .inl d => (P.act st.1 d).map fun (b, cs) => (.data b, cs)
    | .inr s => (P.propose st.1 s).map fun (par, aux, cs) =>
        (.item ⟨par, s, encodeTxs st.2, aux⟩, cs)
  gossip st t := P.gossip st.1 t
  process st o hs := (P.process st.1 o hs, st.2)
  recordOwn st o hs := (P.recordOwn st.1 o hs, st.2)
  durable st := P.durable st.1
  restore d t := (P.restore d t, [])
  out g st := ledgerOf (match g with
    | .confirmed => P.confirmed st.1
    | .stable => P.stable st.1
    | .finalized => P.finalized st.1)
  conflicts := P.conflicts

end Consensus.Shape
end
