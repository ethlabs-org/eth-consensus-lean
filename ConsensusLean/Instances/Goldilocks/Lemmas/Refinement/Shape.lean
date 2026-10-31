module
public import ConsensusLean.Instances.Goldilocks.Statements.Refinement
public import ConsensusLean.Lemmas.Model.Objects

public section

/-! # Goldilocks Refinement: the shape's pure steps

The obligations on the Goldilocks shape (`Refinement/Defs`) that involve no run: the canonical
objects decode back to what they encode, so a delivered canonical object is the node's event
(`canonEvent`); the slashing rule is E1/E2 (`ConflictsIff`); the engine's own-object guard
`protects` passes every block and vote (only two attestation objects ever `conflict`).

Each theorem is a named step. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape
open SA (SAParams ReplayOrder Vote Payload)

/-! ## Encoding round-trips -/

/-- An encoded attestation decodes to itself. -/
theorem decodeAtt_encodeAtt {n : Nat} (a : FG.Att n) : decodeAtt n (encodeAtt a) = some a := by
  simp [decodeAtt, encodeAtt, a.val.isLt]

/-- An encoded vote decodes to itself. -/
theorem decodeVote_encodeVote {n : Nat} (v : Vote n) : decodeVote n (encodeVote v) = some v := by
  simp [decodeVote, encodeVote, v.val.isLt]

/-- Encoded block info (attestations and AC payload) decodes to itself. -/
theorem decodeInfo_encodeInfo {n : Nat} (atts : List (FG.Att n)) (p : Payload n) :
    decodeInfo n (encodeInfo atts p) = some (atts, p) := by
  have h1 : ∀ l : List (FG.Att n), l.mapM (decodeAtt n ∘ encodeAtt) = some l := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp [List.mapM_cons, ih, decodeAtt_encodeAtt]
  have h2 : ∀ l : List (Vote n), l.mapM (decodeVote n ∘ encodeVote) = some l := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp [List.mapM_cons, ih, decodeVote_encodeVote]
  simp [decodeInfo, encodeInfo, List.mapM_map, h1, h2]

/-- A decoded attestation was its own encoding. -/
theorem decodeAtt_eq_some {n : Nat} {w : WireAtt} {a : FG.Att n} (h : decodeAtt n w = some a) :
    encodeAtt a = w := by
  unfold decodeAtt at h
  split at h
  · cases h; rfl
  · exact absurd h (by simp)

/-- The parent root of the parent reference of a named root is that root. -/
theorem parentRoot_parentRef (g : Nat) (r : Nat) :
    parentRoot g (parentRef g (some r)) = some r := by
  by_cases h : r = g
  · subst h; simp [parentRef, parentRoot]
  · simp [parentRef, parentRoot, h]

/-- No parent reference is a digest of the genesis root. -/
theorem parentRef_ne_digest (g : Nat) (p : Option Nat) : parentRef g p ≠ .digest g := by
  cases p with
  | none => simp [parentRef]
  | some r =>
    by_cases h : r = g
    · subst h; simp [parentRef]
    · simp [parentRef, h]

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-! ## Decoding the canonical objects -/

/-- **`decodeBlock` round-trip.** The canonical object of a non-genesis block whose header the
engine's digests map to its root, with well-formed attestations and a valid AC payload, decodes
to the block. -/
theorem decodeBlock_blockObj (hs : List (Header Info × Nat)) (B : Blk sp)
    (hpar : B.parent ≠ none) (hroot : rootOf hs (headerOf sp B) = some B.root)
    (hwf : ∀ a ∈ B.fgPayload, a.WellFormed) (hval : SA.validPayload B) :
    decodeBlock sp hs (blockObj sp B) = some B := by
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hpar
  have hB : blockOf sp B.root (headerOf sp B) B.proposer B.fgPayload B.acPayload = B := by
    simp only [blockOf, headerOf, hr, parentRoot_parentRef]
    cases B; simp_all
  have hinfo : decodeInfo sp.n (headerOf sp B).info = some (B.fgPayload, B.acPayload) := by
    simp [headerOf, decodeInfo_encodeInfo]
  classical
  simp only [decodeBlock, blockObj, hinfo, hroot]
  rw [hB]
  simp [parentRef_ne_digest, hval, headerOf]
  exact hwf

/-- The canonical object of such a block stands for the node's `block` event. -/
theorem canonEvent_blockObj (hs : List (Header Info × Nat)) (B : Blk sp)
    (hpar : B.parent ≠ none) (hroot : rootOf hs (headerOf sp B) = some B.root)
    (hwf : ∀ a ∈ B.fgPayload, a.WellFormed) (hval : SA.validPayload B) :
    canonEvent sp ro hs (blockObj sp B) = some (.block B) := by
  simp [canonEvent, decodeBlock_blockObj hs B hpar hroot hwf hval]

/-- The canonical object of a vote decodes to the vote. -/
theorem decodeVoteObj_voteObj (v : Vote sp.n) : decodeVoteObj sp (voteObj v) = some v := by
  simp [decodeVoteObj, voteObj, decodeVote_encodeVote]

/-- The canonical object of a well-formed attestation decodes to the attestation. -/
theorem decodeAttObj_attObj (a : FG.Att sp.n) (hwf : a.WellFormed) :
    decodeAttObj sp (attObj a) = some a := by
  simp [decodeAttObj, attObj, decodeAtt_encodeAtt, hwf]

/-- The canonical object of a vote stands for the node's `message` event. -/
theorem canonEvent_voteObj (hs : List (Header Info × Nat)) (v : Vote sp.n) :
    canonEvent sp ro hs (voteObj v) = some (.message v) := by
  have h1 : decodeBlock sp hs (voteObj v) = none := by simp [decodeBlock, voteObj]
  simp only [canonEvent, h1, decodeVoteObj_voteObj]

/-- The canonical object of a well-formed attestation stands for the node's `attestation`
event. -/
theorem canonEvent_attObj (hs : List (Header Info × Nat)) (a : FG.Att sp.n)
    (hwf : a.WellFormed) : canonEvent sp ro hs (attObj a) = some (.attestation a) := by
  have h1 : decodeBlock sp hs (attObj a) = none := by simp [decodeBlock, attObj]
  have h2 : decodeVoteObj sp (attObj a) = none := by simp [decodeVoteObj, attObj]
  simp only [canonEvent, h1, h2, decodeAttObj_attObj a hwf]

/-! ## The slashing rule and the own-object guard -/

/-- **G1.5 (a).** `conflicts` holds of two objects exactly when they are the canonical objects
of two `slashable` attestations. -/
theorem conflicts_iff : ConflictsIff := by
  intro n o o'
  constructor
  · intro hc
    unfold conflicts at hc
    split at hc
    · rename_i k w k' w'
      split at hc
      · rename_i a b ha hb
        simp only [decide_eq_true_eq] at hc
        obtain ⟨hk, hk', hab⟩ := hc
        refine ⟨a, b, ?_, ?_, hab⟩
        · subst hk
          simp only [attObj]
          rw [decodeAtt_eq_some ha]
        · subst hk'
          simp only [attObj]
          rw [decodeAtt_eq_some hb]
      · exact absurd hc Bool.false_ne_true
    · exact absurd hc Bool.false_ne_true
  · rintro ⟨a, b, rfl, rfl, hab⟩
    simp [conflicts, attObj, decodeAtt_encodeAtt, hab]

/-- `conflicts` is false unless both objects are attestation data signed in the poll role:
here the first is not. -/
theorem conflicts_eq_false_of_not_att {n : Nat} (o o' : Wire n)
    (h : ∀ k w, o ≠ .mk (.signed k .poll) (.data (.att w)) []) : conflicts o o' = false := by
  unfold conflicts
  split
  · exact absurd rfl (h _ _)
  · rfl

/-- `conflicts` is false unless both objects are attestation data signed in the poll role:
here the second is not. -/
theorem conflicts_eq_false_of_not_att' {n : Nat} (o o' : Wire n)
    (h : ∀ k w, o' ≠ .mk (.signed k .poll) (.data (.att w)) []) : conflicts o o' = false := by
  unfold conflicts
  split
  · exact absurd rfl (h _ _)
  · rfl

/-- The engine's own-object guard passes any object that is not attestation data signed in the
poll role, against any seen list. -/
theorem protects_of_not_att {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (k : Fin (Fintype.card V)) (seen : List (Model.protoOf (compiled (family S)) E).Object)
    (c : (Model.protoOf (compiled (family S)) E).Object)
    (h : ∀ k w, c ≠ .mk (.signed k .poll) (.data (.att w)) []) :
    Model.protects (Model.protoOf (compiled (family S)) E) k seen c = true := by
  unfold Model.protects
  split
  · have hc : ∀ o, conflicts c o = false := fun o => conflicts_eq_false_of_not_att c o h
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨hc c, ?_⟩
    simp only [List.all_eq_true]
    intro o _
    have hc' : conflicts o c = false := conflicts_eq_false_of_not_att' o c h
    change (_ != _ || !(conflicts c o || conflicts o c)) = true
    simp [hc o, hc']
  · rfl

/-- The engine's own-object guard never blocks a block object: `protects` is true of `blockObj`
against any seen list. -/
theorem protects_blockObj {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (hn : 1 ≤ Fintype.card V) (k : Fin (Fintype.card V))
    (seen : List (Model.protoOf (compiled (family S)) E).Object)
    (B : Blk (S.params (Model.pubOf E) hn)) :
    Model.protects (Model.protoOf (compiled (family S)) E) k seen
      (blockObj (S.params (Model.pubOf E) hn) B) = true :=
  protects_of_not_att S k seen _ (fun _ _ h => by cases h)

/-- The engine's own-object guard never blocks a vote object. -/
theorem protects_voteObj {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (k : Fin (Fintype.card V)) (seen : List (Model.protoOf (compiled (family S)) E).Object)
    (v : Vote (Fintype.card V)) :
    Model.protects (Model.protoOf (compiled (family S)) E) k seen (voteObj v) = true :=
  protects_of_not_att S k seen _ (fun _ _ h => by cases h)

/-- A raw block with canonical vote/attestation payload has no forwarding dependencies. -/
theorem dependencies_item {n : Nat} (held : List (Wire n))
    (auth : Model.Auth n (ShapeRole Empty)) (h : Header Info)
    (atts : List (FG.Att n)) (p : Payload n) :
    (dependencies n).ready held (.mk auth (.item h) (payloadObjs atts p)) = true := by
  simp [dependencies, Model.Obj.parts, forwardParent?, payloadObjs]
  simp only [Model.Obj.partsList_eq]
  simp [attObj, voteObj, Model.Obj.parts, Model.Obj.parts.partsList]
  rintro x (⟨a, _, rfl⟩ | ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩) <;> rfl

/-- A dependency projected from a forwarding shape is a carried object. -/
theorem forwardParent_contains {n : Nat} (o parent : Wire n)
    (h : forwardParent? o = some parent) : Model.Obj.Contains o parent := by
  unfold forwardParent? at h
  split at h
  · cases h
    exact Model.Obj.Contains.step (by simp [Model.Obj.carried]) (.refl _)
  · cases h

/-- Relaying already-held objects cannot introduce an unmet wrapper dependency. -/
theorem dependencies_relay {n : Nat} (seen cs : List (Wire n))
    (h : ∀ c ∈ cs, c ∈ seen.flatMap Model.Obj.parts) :
    (dependencies n).ready (seen.flatMap Model.Obj.parts)
      (.mk .none (.data .relay) cs) = true := by
  simp only [dependencies, Model.Obj.parts, List.all_cons, forwardParent?, Bool.true_and,
    Model.Obj.partsList_eq, List.all_eq_true]
  intro part hp
  obtain ⟨c, hc, hp⟩ := List.mem_flatMap.mp hp
  change (match forwardParent? part with
    | none => true
    | some parent => decide (parent ∈ seen.flatMap Model.Obj.parts)) = true
  cases he : forwardParent? part with
  | none => rfl
  | some parent =>
    apply decide_eq_true
    obtain ⟨root, hr, hd⟩ := List.mem_flatMap.mp (h c hc)
    exact List.mem_flatMap.mpr
      ⟨root, hr, (show Model.Obj.Contains root c from hd).trans
        ((show Model.Obj.Contains c part from hp).trans (forwardParent_contains part parent he))⟩

/-- The parameter-free dependency projection preserves the exact parent reference. -/
theorem forwardParent_forwardObj (origin : Fin sp.n) (t : Time)
    (parent : Option (Wire sp.n)) (B : Blk sp) :
    forwardParent? (forwardObj sp origin t parent B) = parent := by
  cases parent <;> rfl

/-- A genesis-parent forwarding wrapper decodes under the explicit wire checks. -/
theorem decodeForward_genesis (hs : List (Header Info × Nat)) (origin : Fin sp.n)
    (t : Time) (B : Blk sp) (hb : decodeBlock sp hs (blockObj sp B) = some B)
    (hp : B.parent = some sp.genesisRoot) (ht : 0 ≤ t)
    (hslt : sp.toParams.slotTime B.slot ≤ t) :
    decodeForward sp hs (forwardObj sp origin t none B) = some (origin, t, none, B) := by
  simp [forwardObj, decodeForward, hb, hp, ht, hslt]

/-- A non-genesis forwarding wrapper retains the exact same-origin parent wrapper. -/
theorem decodeForward_parent (hs : List (Header Info × Nat)) (origin : Fin sp.n)
    (t pt : Time) (B A : Blk sp) (parent : Wire sp.n) (pp : Option (Wire sp.n))
    (hb : decodeBlock sp hs (blockObj sp B) = some B)
    (hparent : decodeForward sp hs parent = some (origin, pt, pp, A))
    (hp : B.parent = some A.root) (hg : A.root ≠ sp.genesisRoot)
    (hslot : A.slot < B.slot) (hpt : pt ≤ t) (ht : 0 ≤ t)
    (hslt : sp.toParams.slotTime B.slot ≤ t) :
    decodeForward sp hs (forwardObj sp origin t (some parent) B) =
      some (origin, t, some parent, B) := by
  simp [forwardObj, decodeForward, hb, hparent, hp, hg, hslot, hpt, ht, hslt]

/-- Successful parsing identifies the entire authenticated object, not only its timestamp. -/
theorem forwardObj_of_decodeForward (hs : List (Header Info × Nat)) (o : Wire sp.n)
    (origin : Fin sp.n) (t : Time) (parent : Option (Wire sp.n)) (B : Blk sp)
    (h : decodeForward sp hs o = some (origin, t, parent, B)) :
    o = forwardObj sp origin t parent B := by
  unfold decodeForward at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨C, _, h⟩ := h
    split at h <;> simp_all [forwardObj]
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨C, _, ⟨⟨k, pt, pp, A⟩, _, h⟩⟩ := h
    split at h <;> simp_all [forwardObj]
    rw [← h.2.2.1]
    rfl
  · simp at h

end Consensus.Goldilocks.Refinement

end
