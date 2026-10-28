module
public import Mathlib.Data.List.Basic
public import AvailableChainModel.Objects.Identifiers
public import AvailableChainModel.Objects.Time

@[expose] public section

/-! # Contract objects

Blocks, authentications and wire objects of the generic contract. Nothing here
is supplied by a protocol.

* `Header`: a block header naming its parent by digest; a `Chain` (an output)
  is a list of headers. The hash is arbitrary run data (`Run.hash`) that honest
  code never sees; claims hold "or a hash collision was observed"
  (`Run.HashCollision`).
* `Auth`: who signed an object. Committee seats and slot proposers; the run
  maps them to validators. Honest code never chooses an `Auth`: the engine
  attaches it.
* `Msg`: a proposal of a header (honest ones are built by the engine) or protocol data.
* `Obj`: an authentication, a message, and the objects it carries. The
  carried objects are structural: the body type is fixed before `Obj`, so a
  body cannot hide a signed object. -/

namespace AvailableChain.Contract

/-- A block header. It names its parent by digest. `input` is the application
input of the proposal; `aux` is protocol data (for example an encoding of the
protocol's own block fields). The digest of a header is `hash h`, for the run's
hash function (`Run.hash`), which is arbitrary: it may have collisions.
Genesis is not a header; its digest is `0`. -/
structure Header where
  parent : Nat
  slot : Slot
  input : Nat
  aux : Nat
  deriving DecidableEq, Repr

/-- A chain: headers oldest first, genesis implicit before the first. An output
is a chain. Chains are compared structurally, never through digests. -/
abbrev Chain := List Header

namespace Chain

/-- `c ⪯ d`: `c` is a prefix of `d`. -/
def Preceq (c d : Chain) : Prop := c <+: d

/-- `c ≺ d`: a strict prefix. -/
def Prec (c d : Chain) : Prop := c <+: d ∧ c ≠ d

/-- Two chains are on one branch. -/
def Compatible (c d : Chain) : Prop := c <+: d ∨ d <+: c

/-- Each header names the previous one (genesis, digest `0`, for the first). -/
def LinkedFrom (hash : Header → Nat) : Nat → Chain → Prop
  | _, [] => True
  | prev, h :: t => h.parent = prev ∧ LinkedFrom hash (hash h) t

/-- The chain is linked by digests under `hash`. -/
def Linked (hash : Header → Nat) (c : Chain) : Prop := LinkedFrom hash 0 c

/-- Slots strictly increase along the chain, starting above 0 (genesis's
slot). -/
def SlotsFrom : Slot → Chain → Prop
  | _, [] => True
  | prev, h :: t => prev < h.slot ∧ SlotsFrom h.slot t

/-- The prefix of `c` up to and including `h`. -/
def upTo (h : Header) (c : Chain) : Chain := c.take (c.idxOf h + 1)

theorem preceq_refl (c : Chain) : Preceq c c := List.prefix_refl c

theorem nil_preceq (c : Chain) : Preceq [] c := List.nil_prefix

end Chain

/-- The authentication of an object. `vote ℓ i`: seat `i` of the committee of
label `ℓ` (every label has `n` seats; the run assigns them to validators by a
bijection). `proposer s`: the proposer key of slot `s`. `none`: unsigned. -/
inductive Auth (L : Type) (n : Nat) where
  | vote (ℓ : L) (i : Fin n)
  | proposer (s : Slot)
  | none
  deriving DecidableEq, Repr

/-- What an object says: a proposal of a header, or protocol data.
Only the engine builds proposals (`Contract.Run`), so a protocol cannot call
arbitrary data a proposal. -/
inductive Msg (Body : Type) where
  | prop (h : Header)
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
