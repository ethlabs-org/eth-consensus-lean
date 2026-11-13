module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Interface
public import ConsensusLean.Lemmas.Model.Objects

public section

/-! # Goldilocks Simulation: the shape's pure steps

The obligations on the Goldilocks shape (`AsChainShape`) that involve no run: the canonical
objects decode back to what they encode, so a delivered canonical object is the node's event
(`canonEvent`); the slashing rule is E1/E2 (`ConflictsIff`); the engine's own-object guard
`protects` passes every block and vote (only two attestation objects ever `conflict`).

Each theorem is a named step. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape
open SA (SAParams ReplayOrder Vote Payload)

variable {binding : VoteBinding}

/-- The stock construction uses the whole population as its committee. -/
theorem params_committeeSize (S : Setup) (pub : Model.Public) (hn : 1 ≤ pub.n) :
    (S.params pub hn).committeeSize = (S.params pub hn).n := by rfl

/-! ## Encoding round-trips -/

/-- An encoded attestation decodes to itself. -/
theorem decodeAtt_encodeAtt {n : Nat} (a : FG.Att n) : decodeAtt n (encodeAtt a) = some a := by
  simp [decodeAtt, encodeAtt, a.val.isLt]

/-- A non-vote data body names no signing-role override, at every vote binding. -/
theorem candidateRole_of_not_vote (B : VoteBinding) (n : Nat) (d : ShapeDuty B.Kind) (b : Body)
    (h : ∀ w, b ≠ .vote w) : B.candidateRole n d (.data b) = none := by
  cases b with
  | vote w => exact absurd rfl (h w)
  | _ => cases hp : B.participationKind <;> simp [VoteBinding.candidateRole, hp]

/-- An item names no signing-role override, at every vote binding. -/
theorem candidateRole_item (B : VoteBinding) (n : Nat) (d : ShapeDuty B.Kind) (h : Header Info) :
    B.candidateRole n d (.item h) = none := by
  cases hp : B.participationKind <;> simp [VoteBinding.candidateRole, hp]

/-- The role in which a poll duty signs the body `b`: its effective candidate role (the
binding's override, else the poll role). -/
def pollRole (B : VoteBinding) (n : Nat) (b : Body) : ShapeRole B.Kind :=
  (B.candidateRole n (.poll 0) (.data b)).getD .poll

/-- The poll role is the effective candidate role of a poll duty: the binding's override, else
the poll role. -/
theorem pollRole_eq (B : VoteBinding) (n : Nat) (b : Body) :
    pollRole B n b = (B.candidateRole n (.poll 0) (.data b)).getD .poll := by
  rfl

/-- A poll signs a canonical vote body in the vote's role (F3). -/
theorem pollRole_vote (B : VoteBinding) {n : Nat} (m : Vote n) :
    pollRole B n (.vote (encodeVote m)) = B.voteRole m.slot :=
  B.candidateRole_poll_vote 0 m

/-- A poll signs every non-vote body in the poll role (F3′). -/
theorem pollRole_of_not_vote (B : VoteBinding) (n : Nat) {b : Body} (hb : ∀ w, b ≠ .vote w) :
    pollRole B n b = .poll :=
  B.candidateRole_poll_nonvote n 0 b hb

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
    decodeBlock sp (binding := binding) hs (blockObj sp (binding := binding) B) = some B := by
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hpar
  have hB : blockOf sp (rawRoot sp.genesisRoot B.root) (headerOf sp B)
      B.proposer B.fgPayload B.acPayload = B := by
    simp only [blockOf, headerOf, hr, parentRoot_parentRef, taggedRoot_rawRoot _ _ hne]
    cases B; simp_all only [ne_eq]
  have hinfo : decodeInfo sp.n (headerOf sp B).info = some (B.fgPayload, B.acPayload) := by
    simp [headerOf, decodeInfo_encodeInfo]
  classical
  simp only [decodeBlock, blockObj, hinfo, hroot]
  rw [hB]
  rw [ite_eq_left ⟨by trivial, by trivial, hwf, hval⟩]

/-- The canonical object of a vote decodes to the vote. -/
theorem decodeVoteObj_voteObj (v : Vote sp.n) :
    decodeVoteObj sp (binding := binding) (voteObj (binding := binding) v) = some v := by
  cases hp : binding.participationKind <;>
    simp [decodeVoteObj, voteObj, VoteBinding.voteRole, hp, decodeVote_encodeVote]

/-- The canonical object of a well-formed attestation decodes to the attestation. -/
theorem decodeAttObj_attObj (a : FG.Att sp.n) (hwf : a.WellFormed) :
    decodeAttObj sp (binding := binding) (attObj (binding := binding) a) = some a := by
  simp [decodeAttObj, attObj, decodeAtt_encodeAtt, hwf]

/-- The canonical object of a vote stands for the node's `message` event. -/
theorem canonEvent_voteObj (hs : List (Header Info × Nat)) (v : Vote sp.n) :
    canonEvent sp ro (binding := binding) hs (voteObj (binding := binding) v) =
      some (.message v) := by
  have h1 : decodeBlock sp (binding := binding) hs (voteObj (binding := binding) v) = none := by
    simp [decodeBlock, voteObj]
  simp only [canonEvent, h1, decodeVoteObj_voteObj]

/-- The canonical object of a well-formed attestation stands for the node's `attestation`
event. -/
theorem canonEvent_attObj (hs : List (Header Info × Nat)) (a : FG.Att sp.n)
    (hwf : a.WellFormed) :
    canonEvent sp ro (binding := binding) hs (attObj (binding := binding) a) =
      some (.attestation a) := by
  have h1 : decodeBlock sp (binding := binding) hs (attObj (binding := binding) a) = none := by
    simp [decodeBlock, attObj]
  have h2 : decodeVoteObj sp (binding := binding) (attObj (binding := binding) a) = none := by
    cases hp : binding.participationKind <;> simp [decodeVoteObj, attObj, hp]
  simp only [canonEvent, h1, h2, decodeAttObj_attObj a hwf]

/-! ## The slashing rule and the own-object guard -/

/-- **G1.5 (a).** `conflicts` holds of two objects exactly when they are the canonical objects
of two `slashable` attestations. -/
theorem conflicts_iff : ConflictsIff := by
  rw [conflictsIff_iff]
  intro B n o o'
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
theorem conflicts_eq_false_of_not_att {n : Nat} (o o' : Wire n binding)
    (h : ∀ k w, o ≠ .mk (.signed k .poll) (.data (.att w)) []) : conflicts o o' = false := by
  unfold conflicts
  split
  · exact absurd rfl (h _ _)
  · rfl

/-- `conflicts` is false unless both objects are attestation data signed in the poll role:
here the second is not. -/
theorem conflicts_eq_false_of_not_att' {n : Nat} (o o' : Wire n binding)
    (h : ∀ k w, o' ≠ .mk (.signed k .poll) (.data (.att w)) []) : conflicts o o' = false := by
  unfold conflicts
  split
  · exact absurd rfl (h _ _)
  · rfl

/-- The engine's own-object guard passes any object that is not attestation data signed in the
poll role, against any seen list. -/
theorem protects_of_not_att {V : Type} [Fintype V] {E : Env V} (S : BoundSetup)
    (k : Fin (Fintype.card V)) (seen : List (Model.protoOf (compiled (goldilocksWith S)) E).Object)
    (c : (Model.protoOf (compiled (goldilocksWith S)) E).Object)
    (h : ∀ k w, c ≠ .mk (.signed k .poll) (.data (.att w)) []) :
    Model.protects (Model.protoOf (compiled (goldilocksWith S)) E) k seen c = true := by
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

/-- Vote-forward envelopes never conflict with attestations, irrespective of the vote author. -/
theorem protects_voteForward {V : Type} [Fintype V] {E : Env V} (S : BoundSetup)
    (k x : Fin (Fintype.card V))
    (seen : List (Model.protoOf (compiled (goldilocksWith S)) E).Object)
    (t : Time) (v : Vote (Fintype.card V)) :
    Model.protects (Model.protoOf (compiled (goldilocksWith S)) E) k seen
      (.mk (.signed x .poll) (.data (.voteForward t (encodeVote v))) [voteObj v]) = true :=
  protects_of_not_att S k seen _ (fun _ _ h => by cases h)

/-- A vote-forward envelope has no parent dependency, including in its carried canonical vote. -/
theorem dependencies_voteForward {n : Nat} (held : List (Wire n binding))
    (x : Fin n) (t : Time) (v : Vote n) :
    (dependencies n).ready held
      (.mk (.signed x .poll) (.data (.voteForward t (encodeVote v))) [voteObj v]) = true := by
  cases hp : binding.participationKind <;>
    simp only [dependencies, forwardParent?, voteObj, VoteBinding.voteRole, hp,
      Model.Obj.parts, Model.Obj.parts.partsList,
      List.append_nil, List.all_cons, List.all_nil, Bool.and_self]

/-- The only release-holdings obligation is the canonical carried vote at the actual prefix. -/
theorem releasable_voteForward {V : Type} [Fintype V] {E : Env V} (S : BoundSetup)
    (x : Fin (Fintype.card V))
    (seen : List (Model.protoOf (compiled (goldilocksWith S)) E).Object)
    (t : Time) (v : Vote (Fintype.card V)) (hv : voteObj v ∈ Model.closure seen) :
    Model.releasable (P := Model.protoOf (compiled (goldilocksWith S)) E) seen
      (.mk (.signed x .poll) (.data (.voteForward t (encodeVote v))) [voteObj v]) = true := by
  classical
  simp only [Model.releasable, Model.Obj.carried, List.all_eq_true, decide_eq_true_eq]
  intro o ho
  obtain rfl := List.mem_singleton.mp ho
  exact hv

/-- A raw block with canonical vote/attestation payload has no forwarding dependencies. -/
theorem dependencies_item {n : Nat} (held : List (Wire n binding))
    (auth : Model.Auth n (ShapeRole binding.Kind)) (h : Header Info)
    (atts : List (FG.Att n)) (p : Payload n) :
    (dependencies n).ready held (.mk auth (.item h) (payloadObjs atts p)) = true := by
  simp only [dependencies, forwardParent?, payloadObjs, List.map_append, Model.Obj.parts,
      List.all_cons, Bool.true_and, List.all_eq_true]
  simp only [Model.Obj.partsList_eq]
  simp only [List.flatMap_append, List.mem_append, List.mem_flatMap, List.mem_map, attObj,
      exists_exists_and_eq_and, Model.Obj.parts, Model.Obj.parts.partsList, List.mem_cons,
      List.not_mem_nil, or_false, voteObj]
  rintro x (⟨a, _, rfl⟩ | ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩)
  · rfl
  all_goals cases hp : binding.participationKind <;> simp [VoteBinding.voteRole, hp]

/-- A dependency projected from a forwarding shape is a carried object. -/
theorem forwardParent_contains {n : Nat} (o parent : Wire n binding)
    (h : forwardParent? o = some parent) : Model.Obj.Contains o parent := by
  unfold forwardParent? at h
  split at h
  · cases h
    exact Model.Obj.Contains.step (by simp [Model.Obj.carried]) (.refl _)
  · cases h

/-- Relaying already-held objects cannot introduce an unmet wrapper dependency. -/
theorem dependencies_relay {n : Nat} (seen cs : List (Wire n binding))
    (h : ∀ c ∈ cs, c ∈ seen.flatMap Model.Obj.parts) :
    (dependencies n (binding := binding)).ready (seen.flatMap Model.Obj.parts)
      (.mk .none (.data .relay) cs) = true := by
  have hrelay : forwardParent? (binding := binding) (.mk .none (.data .relay) cs) = none := rfl
  simp only [dependencies, Model.Obj.parts, List.all_cons, hrelay, Bool.true_and,
    Model.Obj.partsList_eq, List.all_eq_true]
  intro part hp
  obtain ⟨c, hc, hp⟩ := List.mem_flatMap.mp hp
  cases he : forwardParent? (binding := binding) part with
  | none => rfl
  | some parent =>
    apply decide_eq_true
    obtain ⟨root, hr, hd⟩ := List.mem_flatMap.mp (h c hc)
    exact List.mem_flatMap.mpr
      ⟨root, hr, (show Model.Obj.Contains root c from hd).trans
        ((show Model.Obj.Contains c part from hp).trans (forwardParent_contains part parent he))⟩

/-- The parameter-free dependency projection preserves the exact parent reference. -/
theorem forwardParent_forwardObj (origin : Fin sp.n) (t : Time)
    (parent : Option (Wire sp.n binding)) (B : Blk sp) :
    forwardParent? (forwardObj sp origin t parent B) = parent := by
  cases parent <;> rfl

/-- A forwarding wrapper passes the dependency guard once its exact carried objects
are held. Nested dependencies are already contained in those held objects. -/
theorem dependencies_forwardObj (seen : List (Wire sp.n binding)) (origin : Fin sp.n) (t : Time)
    (parent : Option (Wire sp.n binding)) (B : Blk sp)
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
theorem forwardObj_release_guards {V : Type} [Fintype V] {E : Env V} (S : BoundSetup)
    (hn : 1 ≤ Fintype.card V) (seen : List (Wire (Fintype.card V) S.vote))
    (x : Fin (Fintype.card V)) (t : Time) (p : Option (Wire (Fintype.card V) S.vote))
    (B : Blk (S.params (Model.pubOf E) hn))
    (h : ∀ c ∈ p.toList ++ [blockObj _ B], c ∈ seen.flatMap Model.Obj.parts) :
    Model.releasable (P := Model.protoOf (compiled (goldilocksWith S)) E) seen
        (forwardObj _ x t p B) = true ∧
      Model.protects (Model.protoOf (compiled (goldilocksWith S)) E) x seen
        (forwardObj _ x t p B) = true ∧
      (Model.protoOf (compiled (goldilocksWith S)) E).dependencies.ready (Model.closure seen)
        (forwardObj _ x t p B) = true := by
  classical
  refine ⟨?_, protects_of_not_att S x seen _ (fun _ _ he => by cases he), ?_⟩
  · change (p.toList ++ [blockObj _ B]).all _ = true
    apply List.all_eq_true.mpr
    intro c hc
    simp only [decide_eq_true_eq]
    exact h c hc
  · exact dependencies_forwardObj seen x t p B h

variable (sp) in
open Classical in
/-- Parse a canonical authenticated forwarding chain, using the same engine digests for all
nested blocks. A parent wrapper has the same origin, an earlier slot and no later timestamp.
The genesis-root parent terminates the chain. These are wire checks only: actual acceptance
and first-release provenance must be established separately for honest origins. -/
noncomputable def decodeForward (hs : List (Header Info × Nat)) :
    Wire sp.n binding → Option (Fin sp.n × Time × Option (Wire sp.n binding) × Blk sp)
  | .mk (.signed origin .poll) (.data (.forward t)) [child] => do
      let B ← decodeBlock sp hs child
      if child = blockObj sp B ∧ B.parent = some sp.genesisRoot ∧
          0 ≤ t ∧ sp.toParams.slotTime B.slot ≤ t then
        some (origin, t, none, B)
      else none
  | .mk (.signed origin .poll) (.data (.forward t)) [parent, child] => do
      let B ← decodeBlock sp hs child
      let (parentOrigin, parentTime, _, A) ← decodeForward hs parent
      if child = blockObj sp B ∧ parentOrigin = origin ∧ B.parent = some A.root ∧
          A.root ≠ sp.genesisRoot ∧ A.slot < B.slot ∧ parentTime ≤ t ∧
          0 ≤ t ∧ sp.toParams.slotTime B.slot ≤ t then
        some (origin, t, some parent, B)
      else none
  | _ => none
termination_by o => sizeOf o

/-- A genesis-parent forwarding wrapper decodes under the explicit wire checks. -/
theorem decodeForward_genesis (hs : List (Header Info × Nat)) (origin : Fin sp.n)
    (t : Time) (B : Blk sp)
    (hb : decodeBlock sp (binding := binding) hs (blockObj sp (binding := binding) B) = some B)
    (hp : B.parent = some sp.genesisRoot) (ht : 0 ≤ t)
    (hslt : sp.toParams.slotTime B.slot ≤ t) :
    decodeForward sp hs (forwardObj sp (binding := binding) origin t none B) =
      some (origin, t, none, B) := by
  simp only [forwardObj, Option.toList_none, List.nil_append, decodeForward, hb, ht, true_and,
    Option.bind_eq_bind, Option.bind_some, hp, hslt, and_self, ↓reduceIte]

/-- A non-genesis forwarding wrapper retains the exact same-origin parent wrapper. -/
theorem decodeForward_parent (hs : List (Header Info × Nat)) (origin : Fin sp.n)
    (t pt : Time) (B A : Blk sp) (parent : Wire sp.n binding) (pp : Option (Wire sp.n binding))
    (hb : decodeBlock sp (binding := binding) hs (blockObj sp (binding := binding) B) = some B)
    (hparent : decodeForward sp hs parent = some (origin, pt, pp, A))
    (hp : B.parent = some A.root) (hg : A.root ≠ sp.genesisRoot)
    (hslot : A.slot < B.slot) (hpt : pt ≤ t) (ht : 0 ≤ t)
    (hslt : sp.toParams.slotTime B.slot ≤ t) :
    decodeForward sp hs (forwardObj sp origin t (some parent) B) =
      some (origin, t, some parent, B) := by
  simp only [forwardObj, Option.toList_some, List.cons_append, List.nil_append, decodeForward,
    hb, hparent, ne_eq, ht, true_and, Option.bind_eq_bind, Option.bind_some, hg, not_false_eq_true,
    hpt, hp, hslot, hslt, and_self, ↓reduceIte]

/-- Successful parsing identifies the entire authenticated object, not only its timestamp. -/
theorem forwardObj_of_decodeForward (hs : List (Header Info × Nat)) (o : Wire sp.n binding)
    (origin : Fin sp.n) (t : Time) (parent : Option (Wire sp.n binding)) (B : Blk sp)
    (h : decodeForward sp hs o = some (origin, t, parent, B)) :
    o = forwardObj sp origin t parent B := by
  unfold decodeForward at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨C, _, h⟩ := h
    split at h
    · simp_all only [Option.some.injEq, Prod.mk.injEq, forwardObj, Model.Obj.mk.injEq,
        List.self_eq_append_left, Option.toList_eq_nil_iff, and_self]
    · cases h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨C, _, ⟨⟨k, pt, pp, A⟩, _, h⟩⟩ := h
    split at h
    · simp_all only [ne_eq, Option.some.injEq, Prod.mk.injEq, forwardObj, Model.Obj.mk.injEq,
        true_and, not_false_eq_true, and_self]
      rw [← h.2.2.1]
      rfl
    · cases h
  · simp at h

/-- Decoding a forwarding envelope identifies its canonical child using the supplied
digests and bounds the child's slot by the acceptance stamp. -/
theorem decodeForward_child {hs : List (Header Info × Nat)} {o : Wire sp.n binding}
    {x : Fin sp.n} {t : Time} {p : Option (Wire sp.n binding)} {B : Blk sp}
    (h : decodeForward sp hs o = some (x, t, p, B)) :
    decodeBlock sp (binding := binding) hs (blockObj sp (binding := binding) B) = some B ∧
      sp.toParams.slotTime B.slot ≤ t := by
  unfold decodeForward at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨C, hc, h⟩ := h
    split at h
    · rename_i hp
      cases h
      exact ⟨by simpa only [hp.1] using hc, hp.2.2.2⟩
    · simp at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨C, hc, ⟨⟨y, pt, pp, A⟩, _, h⟩⟩ := h
    split at h
    · rename_i hp
      cases h
      exact ⟨by simpa only [hp.1] using hc, hp.2.2.2.2.2.2.2⟩
    · simp at h
  · simp at h

/-- The parser's recursive parent is authenticated by the same source, precedes the
child's slot and stamp, and names its exact parent root; the leaf names genesis. -/
theorem decodeForward_parent_cases {hs : List (Header Info × Nat)} {o : Wire sp.n binding}
    {x : Fin sp.n} {t : Time} {p : Option (Wire sp.n binding)} {B : Blk sp}
    (h : decodeForward sp hs o = some (x, t, p, B)) :
    (p = none ∧ B.parent = some sp.genesisRoot) ∨
      ∃ parent pt pp A, p = some parent ∧
        decodeForward sp hs parent = some (x, pt, pp, A) ∧
        B.parent = some A.root ∧ A.root ≠ sp.genesisRoot ∧ A.slot < B.slot ∧ pt ≤ t := by
  unfold decodeForward at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨C, _, h⟩ := h
    split at h
    · rename_i hp
      cases h
      exact Or.inl ⟨rfl, hp.2.1⟩
    · simp at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨C, _, ⟨⟨y, pt, pp, A⟩, hd, h⟩⟩ := h
    split at h
    · rename_i hp
      cases h
      exact Or.inr ⟨_, pt, pp, A, rfl, hp.2.1 ▸ hd,
        hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1⟩
    · simp at h
  · simp at h

/-- A decoded forwarding stamp is nonnegative. -/
theorem decodeForward_time_nonneg {hs : List (Header Info × Nat)} {o : Wire sp.n binding}
    {x : Fin sp.n} {t : Time} {p : Option (Wire sp.n binding)} {B : Blk sp}
    (h : decodeForward sp hs o = some (x, t, p, B)) : 0 ≤ t := by
  unfold decodeForward at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨C, _, h⟩ := h
    split at h
    · rename_i hp
      cases h
      exact hp.2.2.1
    · simp at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨C, _, ⟨⟨y, pt, pp, A⟩, _, h⟩⟩ := h
    split at h
    · rename_i hp
      cases h
      exact hp.2.2.2.2.2.2.1
    · simp at h
  · simp at h

/-- A successful decode of a constructed wrapper preserves its explicit stamp and parent
when the canonical child has already been decoded in that table. -/
theorem decoded_forward_fields {sp : SA.SAParams} (hs : List (Header Info × Nat))
    (x : Fin sp.n) (t : Time) (p : Option (Wire sp.n binding)) (B : Blk sp)
    (hb : decodeBlock sp (binding := binding) hs (blockObj sp (binding := binding) B) = some B)
    {u : Time} {q : Option (Wire sp.n binding)} {C : Blk sp}
    (hd : decodeForward sp hs (forwardObj sp x t p B) = some (x, u, q, C)) :
    (u, q, C) = (t, p, B) := by
  cases p with
  | none =>
    simp only [forwardObj, Option.toList_none, List.nil_append, decodeForward, hb,
      Option.bind_eq_bind, Option.bind_some] at hd
    split at hd
    · cases hd; rfl
    · cases hd
  | some parent =>
    simp only [forwardObj, Option.toList_some, List.cons_append, List.nil_append,
      decodeForward, hb, Option.bind_eq_bind, Option.bind_some] at hd
    cases hp : decodeForward sp hs parent with
    | none => simp [hp] at hd
    | some result =>
      obtain ⟨origin, stamp, pp, A⟩ := result
      simp only [hp, Option.bind_some] at hd
      split at hd
      · cases hd; rfl
      · cases hd

/-! ## Shape-level preservation -/

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- `apply` keeps the key. -/
theorem apply_self (st : State sp ro binding) r : (apply st r).self = st.self := rfl
/-- `apply` keeps the clock. -/
theorem apply_now (st : State sp ro binding) r : (apply st r).now = st.now := rfl
/-- `apply` keeps the FG-due flag. -/
theorem apply_fgDue (st : State sp ro binding) r : (apply st r).fgDue = st.fgDue := rfl
/-- `apply` installs the node state of its handler result. -/
theorem apply_node (st : State sp ro binding) r : (apply st r).node = r.1 := rfl

/-- A newly queued envelope has the handler's clock and an actual fresh pool insertion.
This is local queue provenance, not a release or service theorem. -/
theorem apply_voteForward_fresh (st : State sp ro binding) r (t : Time) (v : Vote sp.n)
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
theorem apply_voteForward_of_admission (st : State sp ro binding) r (v : Vote sp.n)
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
  · simp only [hm, List.cons_append, List.nil_append, List.mem_cons, List.mem_map, true_or]
  · exact List.mem_append_left _ (by simpa only [hb] using hv)
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨e, he, hv⟩)

/-- `relayIf` keeps the key. -/
theorem relayIf_self (st : State sp ro binding) (c : Prop) [Decidable c] o :
    (relayIf st c o).self = st.self := by unfold relayIf; split <;> rfl
/-- `relayIf` keeps the clock. -/
theorem relayIf_now (st : State sp ro binding) (c : Prop) [Decidable c] o :
    (relayIf st c o).now = st.now := by unfold relayIf; split <;> rfl
/-- `relayIf` keeps the FG-due flag. -/
theorem relayIf_fgDue (st : State sp ro binding) (c : Prop) [Decidable c] o :
    (relayIf st c o).fgDue = st.fgDue := by unfold relayIf; split <;> rfl
/-- `relayIf` keeps the node state. -/
theorem relayIf_node (st : State sp ro binding) (c : Prop) [Decidable c] o :
    (relayIf st c o).node = st.node := by unfold relayIf; split <;> rfl

/-- Processing one delivered object keeps the key. -/
theorem processOne_self hs (st : State sp ro binding) o : (processOne hs st o).self = st.self := by
  unfold processOne; split <;> simp [relayIf_self, apply_self]
/-- Processing one delivered object keeps the clock. -/
theorem processOne_now hs (st : State sp ro binding) o : (processOne hs st o).now = st.now := by
  unfold processOne; split <;> simp [relayIf_now, apply_now]
/-- Processing one delivered object keeps the FG-due flag. -/
theorem processOne_fgDue hs (st : State sp ro binding) o : (processOne hs st o).fgDue = st.fgDue
    := by
  unfold processOne; split <;> simp [relayIf_fgDue, apply_fgDue]

/-- Processing one object preserves all previously queued admission envelopes. -/
theorem processOne_voteForwards_subset hs (st : State sp ro binding) o :
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
theorem processOne_voteForward_stamp hs (st : State sp ro binding) o (t : Time) (m : Vote sp.n)
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
theorem foldl_processOne_voteForward_stamp hs (os : List (Wire sp.n binding))
    (st : State sp ro binding) (t : Time) (m : Vote sp.n)
    (h : (t, m) ∈ (os.foldl (processOne hs) st).voteForwards) :
    (t, m) ∈ st.voteForwards ∨ t = st.now := by
  induction os generalizing st with
  | nil => exact Or.inl h
  | cons o os ih =>
    rcases ih _ h with h | h
    · exact processOne_voteForward_stamp hs st o t m h
    · exact Or.inr (h.trans (processOne_now hs st o))

/-- Later objects in a delivery cannot remove an already queued admission envelope. -/
theorem foldl_processOne_voteForwards_subset hs (os : List (Wire sp.n binding))
    (st : State sp ro binding) :
    st.voteForwards ⊆ (os.foldl (processOne hs) st).voteForwards := by
  induction os generalizing st with
  | nil => exact List.Subset.refl _
  | cons o os ih =>
    intro q hq
    exact ih _ (processOne_voteForwards_subset hs st o hq)

/-- Processing a list of delivered objects keeps the key. -/
theorem foldl_processOne_self hs (os : List (Wire sp.n binding)) (st : State sp ro binding) :
    (os.foldl (processOne hs) st).self = st.self := by
  induction os generalizing st with
  | nil => rfl
  | cons o os ih => simp [List.foldl_cons, ih, processOne_self]
/-- Processing a list of delivered objects keeps the clock. -/
theorem foldl_processOne_now hs (os : List (Wire sp.n binding)) (st : State sp ro binding) :
    (os.foldl (processOne hs) st).now = st.now := by
  induction os generalizing st with
  | nil => rfl
  | cons o os ih => simp [List.foldl_cons, ih, processOne_now]

/-- Processing a list of delivered objects keeps the FG-due flag. -/
theorem foldl_processOne_fgDue hs (os : List (Wire sp.n binding)) (st : State sp ro binding) :
    (os.foldl (processOne hs) st).fgDue = st.fgDue := by
  induction os generalizing st with
  | nil => rfl
  | cons o os ih => simp [List.foldl_cons, ih, processOne_fgDue]

/-- A delivery keeps the key. -/
theorem process_self (st : State sp ro binding) o hs : (process st o hs).self = st.self :=
  foldl_processOne_self hs _ st
/-- A delivery keeps the clock. -/
theorem process_now (st : State sp ro binding) o hs : (process st o hs).now = st.now :=
  foldl_processOne_now hs _ st
/-- A delivery keeps the FG-due flag. -/
theorem process_fgDue (st : State sp ro binding) o hs : (process st o hs).fgDue = st.fgDue :=
  foldl_processOne_fgDue hs _ st

/-- Recording an own object keeps the key. -/
theorem recordOwn_self (st : State sp ro binding) o hs : (recordOwn st o hs).self = st.self := by
  unfold recordOwn; split <;> (try split) <;> rfl
/-- Recording an own object keeps the clock. -/
theorem recordOwn_now (st : State sp ro binding) o hs : (recordOwn st o hs).now = st.now := by
  unfold recordOwn; split <;> (try split) <;> rfl
/-- Recording an own object keeps the FG-due flag. -/
theorem recordOwn_fgDue (st : State sp ro binding) o hs : (recordOwn st o hs).fgDue = st.fgDue := by
  unfold recordOwn; split <;> (try split) <;> rfl

/-- Own-object callbacks do not drain queued vote envelopes. -/
theorem recordOwn_voteForwards_subset (st : State sp ro binding) o hs :
    st.voteForwards ⊆ (recordOwn st o hs).voteForwards := by
  unfold recordOwn
  split
  · exact List.Subset.refl _
  · split
    · exact List.subset_append_left _ _
    · exact List.Subset.refl _
  · exact List.Subset.refl _

/-- The node's tick keeps the key. -/
theorem nodeTick_self (st : State sp ro binding) : (nodeTick st).self = st.self := by
  unfold nodeTick; split <;> rfl
/-- The node's tick keeps the clock. -/
theorem nodeTick_now (st : State sp ro binding) : (nodeTick st).now = st.now := by
  unfold nodeTick; split <;> rfl

/-- The slot proposal keeps the key. -/
theorem propose_self (st : State sp ro binding) s : (propose st s).1.self = st.self := by
  unfold propose; dsimp only; split <;> rfl
/-- The slot proposal keeps the clock. -/
theorem propose_now (st : State sp ro binding) s : (propose st s).1.now = st.now := by
  unfold propose; dsimp only; split <;> rfl
/-- The slot proposal keeps the FG-due flag. -/
theorem propose_fgDue (st : State sp ro binding) s : (propose st s).1.fgDue = st.fgDue := by
  unfold propose; dsimp only; split <;> rfl

/-- Proposing does not drain the queue made by the preceding node tick. -/
theorem propose_voteForwards (st : State sp ro binding) s :
    (propose st s).1.voteForwards = st.voteForwards := by
  unfold propose; dsimp only; split <;> rfl

/-- The FG update keeps the key. -/
theorem fgUpdate_self (st : State sp ro binding) : (fgUpdate st).self = st.self := by
  unfold fgUpdate; simp only; split
  · rfl
  · split <;> rfl
/-- The FG update keeps the clock. -/
theorem fgUpdate_now (st : State sp ro binding) : (fgUpdate st).now = st.now := by
  unfold fgUpdate; simp only; split
  · rfl
  · split <;> rfl
/-- The FG update clears the FG-due flag. -/
theorem fgUpdate_fgDue (st : State sp ro binding) : (fgUpdate st).fgDue = false := by
  unfold fgUpdate; simp only; split
  · rfl
  · split <;> rfl

/-- A poll step keeps the key. -/
theorem poll_self (st : State sp ro binding) t : (poll st t).1.self = st.self := by
  unfold poll; simp only; split <;> split <;> simp [fgUpdate_self]
/-- A poll step keeps the clock. -/
theorem poll_now (st : State sp ro binding) t : (poll st t).1.now = st.now := by
  unfold poll; simp only; split <;> split <;> simp [fgUpdate_now]
/-- After a poll step the FG update is not due: the step ran it if it was. -/
theorem poll_fgDue (st : State sp ro binding) t : (poll st t).1.fgDue = false := by
  unfold poll; simp only; split <;> split <;> simp_all [fgUpdate_fgDue]

end Consensus.Goldilocks.Simulation

end
