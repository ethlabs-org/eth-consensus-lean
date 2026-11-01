module
public import ConsensusLean.Instances.Goldilocks.Statements.Refinement.Interface
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

theorem taggedRoot_ne (g h : Nat) : taggedRoot g h ≠ g := by
  simp only [taggedRoot]; split <;> omega

theorem rawRoot_taggedRoot (g h : Nat) : rawRoot g (taggedRoot g h) = h := by
  simp only [rawRoot, taggedRoot]; split <;> (try split) <;> omega

theorem taggedRoot_rawRoot (g r : Nat) (h : r ≠ g) : taggedRoot g (rawRoot g r) = r := by
  simp only [rawRoot, taggedRoot]; split <;> (try split) <;> omega

/-- The parent root of the parent reference of a named root is that root. -/
theorem parentRoot_parentRef (g : Nat) (r : Nat) :
    parentRoot g (parentRef g (some r)) = some r := by
  by_cases h : r = g
  · subst h; simp [parentRef, parentRoot]
  · simp [parentRef, parentRoot, h, taggedRoot_rawRoot g r h]

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-! ## Decoding the canonical objects -/

/-- **`decodeBlock` round-trip.** The canonical object of a non-genesis block whose header the
engine's digests map to its root, with well-formed attestations and a valid AC payload, decodes
to the block. -/
theorem decodeBlock_blockObj (hs : List (Header Info × Nat)) (B : Blk sp)
    (hpar : B.parent ≠ none) (hne : B.root ≠ sp.genesisRoot)
    (hroot : rootOf hs (headerOf sp B) = some (rawRoot sp.genesisRoot B.root))
    (hwf : ∀ a ∈ B.fgPayload, a.WellFormed) (hval : SA.validPayload B) :
    decodeBlock sp hs (blockObj sp B) = some B := by
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hpar
  have hB : blockOf sp (rawRoot sp.genesisRoot B.root) (headerOf sp B)
      B.proposer B.fgPayload B.acPayload = B := by
    simp only [blockOf, headerOf, hr, parentRoot_parentRef, taggedRoot_rawRoot _ _ hne]
    cases B; simp_all
  have hinfo : decodeInfo sp.n (headerOf sp B).info = some (B.fgPayload, B.acPayload) := by
    simp [headerOf, decodeInfo_encodeInfo]
  classical
  simp only [decodeBlock, blockObj, hinfo, hroot]
  rw [hB]
  simp [hval, headerOf]
  exact hwf

/-- The canonical object of such a block stands for the node's `block` event. -/
theorem canonEvent_blockObj (hs : List (Header Info × Nat)) (B : Blk sp)
    (hpar : B.parent ≠ none) (hne : B.root ≠ sp.genesisRoot)
    (hroot : rootOf hs (headerOf sp B) = some (rawRoot sp.genesisRoot B.root))
    (hwf : ∀ a ∈ B.fgPayload, a.WellFormed) (hval : SA.validPayload B) :
    canonEvent sp ro hs (blockObj sp B) = some (.block B) := by
  simp [canonEvent, decodeBlock_blockObj hs B hpar hne hroot hwf hval]

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

/-- Vote-forward envelopes never conflict with attestations, irrespective of the vote author. -/
theorem protects_voteForward {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (k x : Fin (Fintype.card V)) (seen : List (Model.protoOf (compiled (family S)) E).Object)
    (t : Time) (v : Vote (Fintype.card V)) :
    Model.protects (Model.protoOf (compiled (family S)) E) k seen
      (.mk (.signed x .poll) (.data (.voteForward t (encodeVote v))) [voteObj v]) = true :=
  protects_of_not_att S k seen _ (fun _ _ h => by cases h)

/-- A vote-forward envelope has no parent dependency, including in its carried canonical vote. -/
theorem dependencies_voteForward {n : Nat} (held : List (Wire n))
    (x : Fin n) (t : Time) (v : Vote n) :
    (dependencies n).ready held
      (.mk (.signed x .poll) (.data (.voteForward t (encodeVote v))) [voteObj v]) = true := by
  simp [dependencies, Model.Obj.parts, Model.Obj.parts.partsList, forwardParent?, voteObj]

/-- The only release-holdings obligation is the canonical carried vote at the actual prefix. -/
theorem releasable_voteForward {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (x : Fin (Fintype.card V)) (seen : List (Model.protoOf (compiled (family S)) E).Object)
    (t : Time) (v : Vote (Fintype.card V)) (hv : voteObj v ∈ Model.closure seen) :
    Model.releasable (P := Model.protoOf (compiled (family S)) E) seen
      (.mk (.signed x .poll) (.data (.voteForward t (encodeVote v))) [voteObj v]) = true := by
  classical
  simp only [Model.releasable, Model.Obj.carried, List.all_eq_true, decide_eq_true_eq]
  intro o ho
  obtain rfl := List.mem_singleton.mp ho
  exact hv

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

/-- A forwarding wrapper passes the dependency guard once its exact carried objects
are held. Nested dependencies are already contained in those held objects. -/
theorem dependencies_forwardObj (seen : List (Wire sp.n)) (origin : Fin sp.n) (t : Time)
    (parent : Option (Wire sp.n)) (B : Blk sp)
    (h : ∀ c ∈ parent.toList ++ [blockObj sp B], c ∈ seen.flatMap Model.Obj.parts) :
    (dependencies sp.n).ready (seen.flatMap Model.Obj.parts)
      (forwardObj sp origin t parent B) = true := by
  classical
  have htail := dependencies_relay seen (parent.toList ++ [blockObj sp B]) h
  simp only [dependencies, Model.Obj.parts, List.all_cons,
    Model.Obj.partsList_eq] at htail
  simp only [show forwardParent? (.mk .none (.data .relay)
    (parent.toList ++ [blockObj sp B])) = none from rfl, Bool.true_and] at htail
  have hparts : (forwardObj sp origin t parent B).parts =
      forwardObj sp origin t parent B ::
        (parent.toList ++ [blockObj sp B]).flatMap Model.Obj.parts := by
    simp only [forwardObj, Model.Obj.parts, Model.Obj.partsList_eq]
  simp only [dependencies, hparts, List.all_cons, forwardParent_forwardObj, Bool.and_eq_true]
  constructor
  · cases parent with
    | none => rfl
    | some p => exact decide_eq_true (h p (by simp))
  · exact htail

/-- Exact held parent and child suffice for all three forwarding release guards.
The remaining completeness obligation is to establish these holdings at each actual prefix. -/
theorem forwardObj_release_guards {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (hn : 1 ≤ Fintype.card V) (seen : List (Wire (Fintype.card V)))
    (x : Fin (Fintype.card V)) (t : Time) (p : Option (Wire (Fintype.card V)))
    (B : Blk (S.params (Model.pubOf E) hn))
    (h : ∀ c ∈ p.toList ++ [blockObj _ B], c ∈ seen.flatMap Model.Obj.parts) :
    Model.releasable (P := Model.protoOf (compiled (family S)) E) seen
        (forwardObj _ x t p B) = true ∧
      Model.protects (Model.protoOf (compiled (family S)) E) x seen
        (forwardObj _ x t p B) = true ∧
      (Model.protoOf (compiled (family S)) E).dependencies.ready (Model.closure seen)
        (forwardObj _ x t p B) = true := by
  classical
  refine ⟨?_, protects_of_not_att S x seen _ (fun _ _ he => by cases he), ?_⟩
  · change (p.toList ++ [blockObj _ B]).all _ = true
    apply List.all_eq_true.mpr
    intro c hc
    simp only [decide_eq_true_eq]
    exact h c hc
  · exact dependencies_forwardObj seen x t p B h

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

/-! ## Shape-level preservation -/

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- `apply` keeps the key. -/
theorem apply_self (st : State sp ro) r : (apply st r).self = st.self := rfl
/-- `apply` keeps the clock. -/
theorem apply_now (st : State sp ro) r : (apply st r).now = st.now := rfl
/-- `apply` keeps the FG-due flag. -/
theorem apply_fgDue (st : State sp ro) r : (apply st r).fgDue = st.fgDue := rfl
/-- `apply` installs the node state of its handler result. -/
theorem apply_node (st : State sp ro) r : (apply st r).node = r.1 := rfl

/-- A newly queued envelope has the handler's clock and an actual fresh pool insertion.
This is local queue provenance, not a release or service theorem. -/
theorem apply_voteForward_fresh (st : State sp ro) r (t : Time) (v : Vote sp.n)
    (h : (t, v) ∈ (apply st r).voteForwards)
    (hold : (t, v) ∉ st.voteForwards) :
    t = st.now ∧ v ∉ st.node.ac.pool v.slot ∧ v ∈ r.1.ac.pool v.slot := by
  classical
  simp only [apply, List.mem_append] at h
  obtain h | h := h
  · exact False.elim (hold h)
  obtain ⟨w, hw, he⟩ := List.mem_map.mp h
  cases he
  have hw := (List.mem_filter.mp hw).2
  exact ⟨rfl, of_decide_eq_true hw⟩

/-- Wire, block-payload and own-emission candidates surviving a fresh handler insertion
are queued at that handler's clock. Completeness of these candidates is a separate obligation. -/
theorem apply_voteForward_of_admission (st : State sp ro) r (v : Vote sp.n)
    (ℓ : ACLabel (goldilocksNode sp ro)) (hℓ : .ac ℓ ∈ r.2)
    (hsource : ℓ.call = .message v ∨
      (∃ B, ℓ.call = .block B ∧ v ∈ SA.blockVotes B) ∨ ∃ e ∈ ℓ.emits, e.msg = v)
    (hold : v ∉ st.node.ac.pool v.slot) (hnew : v ∈ r.1.ac.pool v.slot) :
    (st.now, v) ∈ (apply st r).voteForwards := by
  classical
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨v, List.mem_filter.mpr ⟨List.mem_dedup.mpr ?_, by simp [hold, hnew]⟩, rfl⟩
  apply List.mem_flatMap.mpr
  refine ⟨.ac ℓ, hℓ, ?_⟩
  rcases hsource with hm | ⟨B, hb, hv⟩ | ⟨e, he, hv⟩
  · simp [hm]
  · exact List.mem_append_left _ (by simpa only [hb] using hv)
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨e, he, hv⟩)

/-- A new queued vote comes from a real message/payload candidate or own emission in this
handler's cuts. This is not yet authenticated source provenance for an arbitrary received wire. -/
theorem apply_voteForward_source (st : State sp ro) r (t : Time) (v : Vote sp.n)
    (h : (t, v) ∈ (apply st r).voteForwards) (hold : (t, v) ∉ st.voteForwards) :
    ∃ ℓ : ACLabel (goldilocksNode sp ro), .ac ℓ ∈ r.2 ∧
      (ℓ.call = .message v ∨ (∃ B, ℓ.call = .block B ∧ v ∈ SA.blockVotes B) ∨
        ∃ e ∈ ℓ.emits, e.msg = v) := by
  classical
  simp only [apply, List.mem_append] at h
  obtain h | h := h
  · exact False.elim (hold h)
  obtain ⟨w, hw, he⟩ := List.mem_map.mp h
  cases he
  have hw := List.mem_dedup.mp (List.mem_filter.mp hw).1
  obtain ⟨c, hc, hv⟩ := List.mem_flatMap.mp hw
  cases c with
  | fg l => simp at hv
  | ac ℓ =>
    refine ⟨ℓ, hc, ?_⟩
    rcases List.mem_append.mp hv with hv | hv
    · cases hcall : ℓ.call <;> simp_all
    · exact Or.inr (Or.inr (List.mem_map.mp hv))

/-- A fresh wire admission is queued by its single-cut message handler. -/
theorem onMessage_voteForward (st : State sp ro) (m : Vote sp.n)
    (hold : m ∉ st.node.ac.pool m.slot)
    (hnew : m ∈ (Node.onMessage st.self st.node st.now m).1.ac.pool m.slot) :
    (st.now, m) ∈ (apply st (Node.onMessage st.self st.node st.now m)).voteForwards := by
  apply apply_voteForward_of_admission st _ m
    ⟨.message m, Node.frame st.node, _⟩
  · exact List.mem_singleton_self _
  · exact Or.inl rfl
  · exact hold
  · exact hnew

/-- A successful block handler has exactly one AC cut: the preceding FG acceptance does
not change the old AC pool, and the handler result is the AC cut's result. -/
theorem onBlock_voteForward (st : State sp ro) (B : Blk sp) (m : Vote sp.n)
    (hm : m ∈ SA.blockVotes B) (ht : ¬ sp.slot st.now < B.slot)
    (fg' : Store sp.toParams (Payload sp.n)) (hfg : st.node.fg.onBlock B = some fg')
    (hold : m ∉ st.node.ac.pool m.slot)
    (hnew : m ∈ (Node.onBlock st.self st.node st.now B).1.ac.pool m.slot) :
    (st.now, m) ∈ (apply st (Node.onBlock st.self st.node st.now B)).voteForwards := by
  apply apply_voteForward_of_admission st _ m
    ⟨.block B, Node.frame { st.node with fg := fg' }, _⟩
  · simp only [Node.onBlock, ht, ↓reduceIte, hfg]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · exact Or.inr (Or.inl ⟨B, rfl, hm⟩)
  · exact hold
  · exact hnew

/-- A message handler's sole AC cut transports fresh incoming or emitted votes directly
to the aggregate admission filter. Freshness remains an explicit reachability obligation. -/
theorem onMessage_voteForward_of_cut (st : State sp ro) (m : Vote sp.n)
    (ℓ : ACLabel (goldilocksNode sp ro))
    (hc : .ac ℓ ∈ (Node.onMessage st.self st.node st.now m).2) (v : Vote sp.n)
    (hsource : v = m ∨ ∃ e ∈ ℓ.emits, e.msg = v)
    (hold : v ∉ st.node.ac.pool v.slot)
    (hnew : v ∈ ((goldilocksNode sp ro).step st.self st.node.ac ℓ.frame
      st.now ℓ.call).1.pool v.slot) :
    (st.now, v) ∈ (apply st (Node.onMessage st.self st.node st.now m)).voteForwards := by
  have hc' := hc
  simp only [Node.onMessage, Node.acCall, List.mem_singleton, Cut.ac.injEq] at hc'
  subst ℓ
  apply apply_voteForward_of_admission st _ v _ hc
  · rcases hsource with rfl | he
    · exact Or.inl rfl
    · exact Or.inr (Or.inr he)
  · exact hold
  · exact hnew

/-- The AC cut of a block handler has exactly the handler's old and new AC states:
the preceding FG cut changes neither pool. Thus a fresh cut admission or emission
passes `apply`'s aggregate filter, without a collision or frame-coherence premise. -/
theorem onBlock_voteForward_of_cut (st : State sp ro) (B : Blk sp)
    (ℓ : ACLabel (goldilocksNode sp ro))
    (hc : .ac ℓ ∈ (Node.onBlock st.self st.node st.now B).2) (v : Vote sp.n)
    (hsource : v ∈ SA.blockVotes B ∨ ∃ e ∈ ℓ.emits, e.msg = v)
    (hold : v ∉ st.node.ac.pool v.slot)
    (hnew : v ∈ ((goldilocksNode sp ro).step st.self st.node.ac ℓ.frame
      st.now ℓ.call).1.pool v.slot) :
    (st.now, v) ∈ (apply st (Node.onBlock st.self st.node st.now B)).voteForwards := by
  have hc' := hc
  simp only [Node.onBlock] at hc'
  split_ifs at hc' with ht
  · simp at hc'
  · cases hfg : st.node.fg.onBlock B with
    | none => simp [hfg] at hc'
    | some fg' =>
      simp only [hfg, Node.acCall, List.mem_cons, List.not_mem_nil, or_false,
        reduceCtorEq, false_or, Cut.ac.injEq] at hc'
      subst ℓ
      apply apply_voteForward_of_admission st _ v _ hc
      · rcases hsource with hv | he
        · exact Or.inr (Or.inl ⟨B, rfl, hv⟩)
        · exact Or.inr (Or.inr he)
      · exact hold
      · simpa only [Node.onBlock, ht, ↓reduceIte, hfg, Node.acCall] using hnew

/-- `relayIf` keeps the key. -/
theorem relayIf_self (st : State sp ro) (c : Prop) [Decidable c] o :
    (relayIf st c o).self = st.self := by unfold relayIf; split <;> rfl
/-- `relayIf` keeps the clock. -/
theorem relayIf_now (st : State sp ro) (c : Prop) [Decidable c] o :
    (relayIf st c o).now = st.now := by unfold relayIf; split <;> rfl
/-- `relayIf` keeps the FG-due flag. -/
theorem relayIf_fgDue (st : State sp ro) (c : Prop) [Decidable c] o :
    (relayIf st c o).fgDue = st.fgDue := by unfold relayIf; split <;> rfl
/-- `relayIf` keeps the node state. -/
theorem relayIf_node (st : State sp ro) (c : Prop) [Decidable c] o :
    (relayIf st c o).node = st.node := by unfold relayIf; split <;> rfl

/-- Processing one delivered object keeps the key. -/
theorem processOne_self hs (st : State sp ro) o : (processOne hs st o).self = st.self := by
  unfold processOne; split <;> simp [relayIf_self, apply_self]
/-- Processing one delivered object keeps the clock. -/
theorem processOne_now hs (st : State sp ro) o : (processOne hs st o).now = st.now := by
  unfold processOne; split <;> simp [relayIf_now, apply_now]
/-- Processing one delivered object keeps the FG-due flag. -/
theorem processOne_fgDue hs (st : State sp ro) o : (processOne hs st o).fgDue = st.fgDue := by
  unfold processOne; split <;> simp [relayIf_fgDue, apply_fgDue]

/-- Processing one object preserves all previously queued admission envelopes. -/
theorem processOne_voteForwards_subset hs (st : State sp ro) o :
    st.voteForwards ⊆ (processOne hs st o).voteForwards := by
  unfold processOne
  split
  · dsimp only
    unfold relayIf
    split <;> exact List.subset_append_left _ _
  · exact List.subset_append_left _ _
  · unfold relayIf
    split <;> exact List.subset_append_left _ _
  · exact List.Subset.refl _

/-- A delivery handler either preserves an old queue entry or stamps a new one
with its actual clock. This does not assume first release or pool freshness. -/
theorem processOne_voteForward_stamp hs (st : State sp ro) o (t : Time) (m : Vote sp.n)
    (h : (t, m) ∈ (processOne hs st o).voteForwards) :
    (t, m) ∈ st.voteForwards ∨ t = st.now := by
  by_cases hold : (t, m) ∈ st.voteForwards
  · exact Or.inl hold
  right
  unfold processOne at h
  split at h
  · dsimp only at h
    unfold relayIf at h
    split at h <;> exact (apply_voteForward_fresh st _ t m h hold).1
  · exact (apply_voteForward_fresh st _ t m h hold).1
  · unfold relayIf at h
    split at h <;> exact (apply_voteForward_fresh st _ t m h hold).1
  · exact False.elim (hold h)

/-- Recursive receipt processing cannot introduce a vote stamp from a different
clock, including when several objects admit votes during the same delivery. -/
theorem foldl_processOne_voteForward_stamp hs (os : List (Wire sp.n))
    (st : State sp ro) (t : Time) (m : Vote sp.n)
    (h : (t, m) ∈ (os.foldl (processOne hs) st).voteForwards) :
    (t, m) ∈ st.voteForwards ∨ t = st.now := by
  induction os generalizing st with
  | nil => exact Or.inl h
  | cons o os ih =>
    rcases ih _ h with h | h
    · exact processOne_voteForward_stamp hs st o t m h
    · exact Or.inr (h.trans (processOne_now hs st o))

/-- Later objects in a delivery cannot remove an already queued admission envelope. -/
theorem foldl_processOne_voteForwards_subset hs (os : List (Wire sp.n)) (st : State sp ro) :
    st.voteForwards ⊆ (os.foldl (processOne hs) st).voteForwards := by
  induction os generalizing st with
  | nil => exact List.Subset.refl _
  | cons o os ih =>
    intro q hq
    exact ih _ (processOne_voteForwards_subset hs st o hq)

/-- A fresh canonical wire admission at any delivery prefix remains queued after the
whole delivery. The freshness test is at this handler's input, not the event boundary. -/
theorem process_message_voteForward (st : State sp ro) (o : Wire sp.n) hs
    (pre post : List (Wire sp.n)) (m : Vote sp.n)
    (hparts : delivered sp o = pre ++ voteObj m :: post)
    (hold : m ∉ (pre.foldl (processOne hs) st).node.ac.pool m.slot)
    (hnew : m ∈ (Node.onMessage (pre.foldl (processOne hs) st).self
      (pre.foldl (processOne hs) st).node st.now m).1.ac.pool m.slot) :
    (st.now, m) ∈ (process st o hs).voteForwards := by
  have hnow : (pre.foldl (processOne hs) st).now = st.now := by
    clear hparts hold hnew
    induction pre generalizing st with
    | nil => rfl
    | cons x xs ih => exact (ih _).trans (processOne_now hs st x)
  have hq := onMessage_voteForward (pre.foldl (processOne hs) st) m hold
    (by simpa only [hnow] using hnew)
  rw [hnow] at hq
  unfold process
  rw [hparts, List.foldl_append, List.foldl_cons]
  apply foldl_processOne_voteForwards_subset hs post _
  simpa only [processOne, canonEvent_voteObj, hnow] using hq

/-- Processing a list of delivered objects keeps the key. -/
theorem foldl_processOne_self hs (os : List (Wire sp.n)) (st : State sp ro) :
    (os.foldl (processOne hs) st).self = st.self := by
  induction os generalizing st with
  | nil => rfl
  | cons o os ih => simp [List.foldl_cons, ih, processOne_self]
/-- Processing a list of delivered objects keeps the clock. -/
theorem foldl_processOne_now hs (os : List (Wire sp.n)) (st : State sp ro) :
    (os.foldl (processOne hs) st).now = st.now := by
  induction os generalizing st with
  | nil => rfl
  | cons o os ih => simp [List.foldl_cons, ih, processOne_now]

/-- A fresh block-payload admission at a delivery prefix remains queued after all
later objects, whether or not the accepted block itself needs unsigned relay. -/
theorem process_block_voteForward (st : State sp ro) (o c : Wire sp.n) hs
    (pre post : List (Wire sp.n)) (B : Blk sp) (m : Vote sp.n)
    (hparts : delivered sp o = pre ++ c :: post)
    (hcanon : canonEvent sp ro hs c = some (.block B))
    (hm : m ∈ SA.blockVotes B) (ht : ¬ sp.slot st.now < B.slot)
    (fg' : Store sp.toParams (Payload sp.n))
    (hfg : (pre.foldl (processOne hs) st).node.fg.onBlock B = some fg')
    (hold : m ∉ (pre.foldl (processOne hs) st).node.ac.pool m.slot)
    (hnew : m ∈ (Node.onBlock (pre.foldl (processOne hs) st).self
      (pre.foldl (processOne hs) st).node st.now B).1.ac.pool m.slot) :
    (st.now, m) ∈ (process st o hs).voteForwards := by
  have hnow := foldl_processOne_now hs pre st
  have hq := onBlock_voteForward (pre.foldl (processOne hs) st) B m hm
    (by simpa only [hnow] using ht) fg' hfg hold
    (by simpa only [hnow] using hnew)
  rw [hnow] at hq
  unfold process
  rw [hparts, List.foldl_append, List.foldl_cons]
  apply foldl_processOne_voteForwards_subset hs post _
  simp only [processOne, hcanon]
  unfold relayIf
  split <;> simpa only [hnow] using hq

/-- Processing a list of delivered objects keeps the FG-due flag. -/
theorem foldl_processOne_fgDue hs (os : List (Wire sp.n)) (st : State sp ro) :
    (os.foldl (processOne hs) st).fgDue = st.fgDue := by
  induction os generalizing st with
  | nil => rfl
  | cons o os ih => simp [List.foldl_cons, ih, processOne_fgDue]

/-- A delivery keeps the key. -/
theorem process_self (st : State sp ro) o hs : (process st o hs).self = st.self :=
  foldl_processOne_self hs _ st
/-- A delivery keeps the clock. -/
theorem process_now (st : State sp ro) o hs : (process st o hs).now = st.now :=
  foldl_processOne_now hs _ st
/-- A delivery keeps the FG-due flag. -/
theorem process_fgDue (st : State sp ro) o hs : (process st o hs).fgDue = st.fgDue :=
  foldl_processOne_fgDue hs _ st

/-- Recording an own object keeps the key. -/
theorem recordOwn_self (st : State sp ro) o hs : (recordOwn st o hs).self = st.self := by
  unfold recordOwn; split <;> (try split) <;> rfl
/-- Recording an own object keeps the clock. -/
theorem recordOwn_now (st : State sp ro) o hs : (recordOwn st o hs).now = st.now := by
  unfold recordOwn; split <;> (try split) <;> rfl
/-- Recording an own object keeps the FG-due flag. -/
theorem recordOwn_fgDue (st : State sp ro) o hs : (recordOwn st o hs).fgDue = st.fgDue := by
  unfold recordOwn; split <;> (try split) <;> rfl

/-- The node's tick keeps the key. -/
theorem nodeTick_self (st : State sp ro) : (nodeTick st).self = st.self := by
  unfold nodeTick; split <;> rfl
/-- The node's tick keeps the clock. -/
theorem nodeTick_now (st : State sp ro) : (nodeTick st).now = st.now := by
  unfold nodeTick; split <;> rfl

/-- The slot proposal keeps the key. -/
theorem propose_self (st : State sp ro) s : (propose st s).1.self = st.self := by
  unfold propose; dsimp only; split <;> rfl
/-- The slot proposal keeps the clock. -/
theorem propose_now (st : State sp ro) s : (propose st s).1.now = st.now := by
  unfold propose; dsimp only; split <;> rfl
/-- The slot proposal keeps the FG-due flag. -/
theorem propose_fgDue (st : State sp ro) s : (propose st s).1.fgDue = st.fgDue := by
  unfold propose; dsimp only; split <;> rfl

/-- The FG update keeps the key. -/
theorem fgUpdate_self (st : State sp ro) : (fgUpdate st).self = st.self := by
  unfold fgUpdate; simp only; split
  · rfl
  · split <;> rfl
/-- The FG update keeps the clock. -/
theorem fgUpdate_now (st : State sp ro) : (fgUpdate st).now = st.now := by
  unfold fgUpdate; simp only; split
  · rfl
  · split <;> rfl
/-- The FG update clears the FG-due flag. -/
theorem fgUpdate_fgDue (st : State sp ro) : (fgUpdate st).fgDue = false := by
  unfold fgUpdate; simp only; split
  · rfl
  · split <;> rfl

/-- A poll step keeps the key. -/
theorem poll_self (st : State sp ro) t : (poll st t).1.self = st.self := by
  unfold poll; simp only; split <;> split <;> simp [fgUpdate_self]
/-- A poll step keeps the clock. -/
theorem poll_now (st : State sp ro) t : (poll st t).1.now = st.now := by
  unfold poll; simp only; split <;> split <;> simp [fgUpdate_now]
/-- After a poll step the FG update is not due: the step ran it if it was. -/
theorem poll_fgDue (st : State sp ro) t : (poll st t).1.fgDue = false := by
  unfold poll; simp only; split <;> split <;> simp_all [fgUpdate_fgDue]

/-- A restore sets the key to the restored one. -/
theorem restore_self (k : Fin sp.n) (d : State sp ro) t : (restore k d t).self = k := rfl
/-- A restore sets the clock to the restart time. -/
theorem restore_now (k : Fin sp.n) (d : State sp ro) t : (restore k d t).now = t := rfl
/-- A restore clears the FG-due flag. -/
theorem restore_fgDue (k : Fin sp.n) (d : State sp ro) t : (restore k d t).fgDue = false := rfl

end Consensus.Goldilocks.Refinement

end
