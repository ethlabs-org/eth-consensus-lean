module
public import ConsensusModel.Objects
public import Mathlib.Logic.Equiv.List

@[expose] public section

/-! # Chains (building block)

Headers and chains. A header names its parent by an explicit root or by a
digest (no digest is reserved); its position is a slot or a height; its
`input` is the encoded payload, written by the engine; `info` is protocol
information (for example a round). A chain lists headers oldest first, the root
implicit before the first. Chains are compared structurally, never through
digests: linkage, increasing positions and provenance are predicates on a
chain, each closed under prefixes. -/

namespace Consensus.Blocks

/-- A parent reference: the explicit root, or a digest (no reserved digest). -/
inductive ParentRef where
  | root
  | digest (d : Nat)
  deriving DecidableEq, Repr

/-- `ParentRef ≃ Option Nat`, for the encoding. -/
def ParentRef.equiv : ParentRef ≃ Option Nat where
  toFun
    | .root => none
    | .digest d => some d
  invFun
    | none => .root
    | some d => .digest d
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

instance : Encodable ParentRef := Encodable.ofEquiv _ ParentRef.equiv

/-- A header: parent, position (slot or height), encoded payload (written by
the engine), protocol information (e.g. a round). -/
structure Header (Info : Type) where
  /-- The parent: the root or a digest. -/
  parent : ParentRef
  /-- The position: a slot or a height. -/
  pos : Nat
  /-- The encoded payload; the engine writes it. -/
  input : Nat
  /-- Protocol information. -/
  info : Info
  deriving DecidableEq

/-- `Header Info ≃ ParentRef × Nat × Nat × Info`, for the encoding. -/
def Header.equiv (Info : Type) : Header Info ≃ ParentRef × Nat × Nat × Info where
  toFun h := (h.parent, h.pos, h.input, h.info)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance {Info : Type} [Encodable Info] : Encodable (Header Info) :=
  Encodable.ofEquiv _ (Header.equiv Info)

/-- A chain: headers oldest first, the root implicit before the first. -/
abbrev Chain (Info : Type) := List (Header Info)

namespace Chain

variable {Info : Type}

/-- Each header names the previous one: the first names `prev`, each later one
the digest of its predecessor under `hash`. -/
def LinkedFrom (hash : Header Info → Nat) : ParentRef → Chain Info → Prop
  | _, [] => True
  | prev, h :: t => h.parent = prev ∧ LinkedFrom hash (.digest (hash h)) t

/-- The chain is linked from the root under `hash`. -/
def Linked (hash : Header Info → Nat) (c : Chain Info) : Prop := LinkedFrom hash .root c

/-- Positions strictly increase along the chain, starting above `start`. -/
def PosFrom : Nat → Chain Info → Prop
  | _, [] => True
  | prev, h :: t => prev < h.pos ∧ PosFrom h.pos t

/-- Positions strictly increase along the chain, starting above 0 (the root's
position). -/
def PosIncreasing (c : Chain Info) : Prop := PosFrom 0 c

/-- Provenance: every header is in `seen` as an item signed in a role that
`ok` accepts for it (the shape passes its closed `ProposalRole`, D-25). -/
def Provenant {n : Nat} {Role Body : Type} (seen : Set (Model.Obj n Role (Header Info) Body))
    (ok : Header Info → Role → Prop) (c : Chain Info) : Prop :=
  ∀ h ∈ c, ∃ k r cs, ok h r ∧ Model.Obj.mk (.signed k r) (.item h) cs ∈ seen

theorem linkedFrom_prefix {hash : Header Info → Nat} :
    ∀ {prev : ParentRef} {c d : Chain Info}, c <+: d → LinkedFrom hash prev d →
      LinkedFrom hash prev c
  | _, [], _, _, _ => trivial
  | _, _ :: _, [], hp, _ => absurd (List.eq_nil_of_prefix_nil hp) (by simp)
  | _, x :: c, y :: d, hp, hd => by
    obtain ⟨rfl, hp'⟩ := List.cons_prefix_cons.mp hp
    exact ⟨hd.1, linkedFrom_prefix hp' hd.2⟩

/-- Linkage is prefix-closed. -/
theorem linked_prefix {hash : Header Info → Nat} {c d : Chain Info} (h : c <+: d)
    (hd : Linked hash d) : Linked hash c :=
  linkedFrom_prefix h hd

theorem posFrom_prefix :
    ∀ {start : Nat} {c d : Chain Info}, c <+: d → PosFrom start d → PosFrom start c
  | _, [], _, _, _ => trivial
  | _, _ :: _, [], hp, _ => absurd (List.eq_nil_of_prefix_nil hp) (by simp)
  | _, x :: c, y :: d, hp, hd => by
    obtain ⟨rfl, hp'⟩ := List.cons_prefix_cons.mp hp
    exact ⟨hd.1, posFrom_prefix hp' hd.2⟩

/-- Increasing positions are prefix-closed. -/
theorem posIncreasing_prefix {c d : Chain Info} (h : c <+: d) (hd : PosIncreasing d) :
    PosIncreasing c :=
  posFrom_prefix h hd

/-- Provenance is prefix-closed. -/
theorem provenant_prefix {n : Nat} {Role Body : Type}
    {seen : Set (Model.Obj n Role (Header Info) Body)} {ok : Header Info → Role → Prop}
    {c d : Chain Info} (h : c <+: d) (hd : Provenant seen ok d) : Provenant seen ok c :=
  fun x hx => hd x (h.subset hx)

end Chain

end Consensus.Blocks
end
