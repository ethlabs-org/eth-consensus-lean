module
public import Mathlib.Data.List.Basic
public import AvailableChainModel.Objects.Codec
public import AvailableChainModel.Objects.Identifiers
public import AvailableChainModel.Objects.Time

@[expose] public section

/-! # Contract objects

Blocks, authentications and wire objects of the generic contract. Nothing here
is supplied by a protocol.

* `CBlock`: a chain block with an application `input` and protocol data `aux`.
  It has no root field: the root is computed from the content, so two blocks
  with the same root are equal (`CBlock.root_injective`). No claim needs a
  hash premise.
* `Auth`: who signed an object. Committee seats and slot proposers; the run
  maps them to validators. Honest code never chooses an `Auth`: the engine
  attaches it.
* `Msg`: a proposal of a `CBlock` (built only by the engine) or protocol data.
* `Obj`: an authentication, a message, and the objects it carries. The
  carried objects are structural: the body type is fixed before `Obj`, so a
  body cannot hide a signed object. -/

namespace AvailableChain.Contract

/-- A contract block. `input` is the application input of the proposal; `aux`
is protocol data (for example an encoding of the protocol's own block fields). -/
inductive CBlock where
  | genesis
  | node (parent : CBlock) (slot : Slot) (input : Nat) (aux : Nat)
  deriving DecidableEq, Repr

namespace CBlock

def slot : CBlock → Slot
  | genesis => 0
  | node _ s _ _ => s

def input : CBlock → Nat
  | genesis => 0
  | node _ _ x _ => x

def parent : CBlock → CBlock
  | genesis => genesis
  | node p _ _ _ => p

/-- The computed root: `0` for genesis, and an injective code of the parent
root and the content above it. -/
def root : CBlock → Nat
  | genesis => 0
  | node p s x a => epair (root p) (epair s (epair x a)) + 1

theorem root_injective : Function.Injective root := by
  intro B
  induction B with
  | genesis =>
      intro C h
      cases C with
      | genesis => rfl
      | node p s x a => simp [root] at h
  | node p s x a ih =>
      intro C h
      cases C with
      | genesis => simp [root] at h
      | node q u y b =>
          simp only [root, Nat.add_right_cancel_iff] at h
          obtain ⟨hp, h2⟩ := epair_inj h
          obtain ⟨hs, h3⟩ := epair_inj h2
          obtain ⟨hx, ha⟩ := epair_inj h3
          rw [ih hp, hs, hx, ha]

/-- The block and its ancestors, nearest first, ending with genesis. -/
def chain : CBlock → List CBlock
  | genesis => [genesis]
  | node p s x a => node p s x a :: chain p

/-- `B ⪯ C`: `B` is `C` or an ancestor of `C`. -/
def Preceq (B C : CBlock) : Prop := B ∈ C.chain

/-- `B ≺ C`: a strict ancestor. -/
def Prec (B C : CBlock) : Prop := Preceq B C ∧ B ≠ C

/-- Two blocks are on one chain. -/
def Compatible (B C : CBlock) : Prop := Preceq B C ∨ Preceq C B

instance (B C : CBlock) : Decidable (Preceq B C) :=
  inferInstanceAs (Decidable (B ∈ C.chain))

theorem genesis_mem_chain : ∀ B : CBlock, genesis ∈ B.chain
  | genesis => List.mem_singleton_self _
  | node p _ _ _ => List.mem_cons_of_mem _ (genesis_mem_chain p)

theorem genesis_preceq (B : CBlock) : Preceq genesis B := genesis_mem_chain B

theorem self_mem_chain : ∀ B : CBlock, B ∈ B.chain
  | genesis => List.mem_singleton_self _
  | node _ _ _ _ => List.mem_cons_self

theorem preceq_refl (B : CBlock) : Preceq B B := self_mem_chain B

end CBlock

/-- The authentication of an object. `vote ℓ i`: seat `i` of the committee of
label `ℓ` (every label has `n` seats; the run assigns them to validators by a
bijection). `proposer s`: the proposer key of slot `s`. `none`: unsigned. -/
inductive Auth (L : Type) (n : Nat) where
  | vote (ℓ : L) (i : Fin n)
  | proposer (s : Slot)
  | none
  deriving DecidableEq, Repr

/-- What an object says: a proposal of a contract block, or protocol data.
Only the engine builds proposals (`Contract.Run`), so a protocol cannot call
arbitrary data a proposal. -/
inductive Msg (Body : Type) where
  | prop (B : CBlock)
  | data (b : Body)
  deriving DecidableEq, Repr

/-- A wire object: its authentication, what it says, and the objects it
carries. -/
inductive Obj (L : Type) (n : Nat) (Body : Type) where
  | mk (auth : Auth L n) (msg : Msg Body) (carried : List (Obj L n Body))

section DecEq
variable {L : Type} {n : Nat} {Body : Type} [DecidableEq L] [DecidableEq Body]

mutual
/-- Decidable equality of objects (the deriving handler does not cover the
nesting through `List`). -/
def Obj.decEq : (a b : Obj L n Body) → Decidable (a = b)
  | .mk a m cs, .mk a' m' cs' =>
    if ha : a = a' then
      if hm : m = m' then
        match Obj.decEqList cs cs' with
        | isTrue h => isTrue (by subst ha hm h; rfl)
        | isFalse h => isFalse (by intro e; injection e with _ _ e; exact h e)
      else isFalse (by intro e; injection e with _ e _; exact hm e)
    else isFalse (by intro e; injection e with e _ _; exact ha e)
def Obj.decEqList : (l l' : List (Obj L n Body)) → Decidable (l = l')
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
  | a :: l, b :: l' =>
    match Obj.decEq a b with
    | isTrue h =>
      match Obj.decEqList l l' with
      | isTrue h' => isTrue (by rw [h, h'])
      | isFalse h' => isFalse (by intro e; injection e with _ e; exact h' e)
    | isFalse h => isFalse (by intro e; injection e with e _; exact h e)
end

instance : DecidableEq (Obj L n Body) := Obj.decEq

end DecEq

namespace Obj

variable {L : Type} {n : Nat} {Body : Type}

def auth : Obj L n Body → Auth L n
  | mk a _ _ => a

def msg : Obj L n Body → Msg Body
  | mk _ m _ => m

def carried : Obj L n Body → List (Obj L n Body)
  | mk _ _ cs => cs

/-- `Contains o o'`: `o'` is `o` or occurs, at any depth, in what `o` carries. -/
inductive Contains : Obj L n Body → Obj L n Body → Prop
  | refl (o : Obj L n Body) : Contains o o
  | step {o c d : Obj L n Body} : c ∈ o.carried → Contains c d → Contains o d

theorem Contains.trans {a b c : Obj L n Body} (h₁ : Contains a b) (h₂ : Contains b c) :
    Contains a c := by
  induction h₁ with
  | refl => exact h₂
  | step hm _ ih => exact .step hm (ih h₂)

/-- The objects that `o` contains, `o` first. -/
def parts : Obj L n Body → List (Obj L n Body)
  | mk a b cs => mk a b cs :: partsList cs
where
  partsList : List (Obj L n Body) → List (Obj L n Body)
    | [] => []
    | c :: cs => parts c ++ partsList cs

end Obj

end AvailableChain.Contract

end
