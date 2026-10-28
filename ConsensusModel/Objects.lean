module
public import Mathlib.Data.List.Basic
public import AvailableChainModel.Objects.Time

@[expose] public section

/-! # Model objects (layer ½)

Authentications, messages and wire objects of the execution model. Nothing here
is supplied by a protocol beyond its types.

* `Auth`: who signed an object: seat `i` of label `ℓ` (the run assigns seats to
  validators), or nobody. Honest code never chooses an `Auth`: the engine
  attaches it.
* `Msg`: an item (hashed by the engine) or protocol data.
* `Obj`: an authentication, a message, and the objects it carries,
  structurally: the item and body types are fixed before `Obj`, so neither can
  hide a signed object. -/

namespace Consensus.Model

/-- The authentication of an object. -/
inductive Auth (L : Type) (seats : L → Nat) where
  | signed (ℓ : L) (i : Fin (seats ℓ))
  | none

instance {L : Type} [DecidableEq L] {seats : L → Nat} : DecidableEq (Auth L seats) := by
  intro a b
  cases a with
  | signed ℓ i =>
    cases b with
    | signed ℓ' i' =>
      if h : ℓ = ℓ' then
        subst h
        if hi : i = i' then exact isTrue (by rw [hi]) else
          exact isFalse (by intro e; cases e; exact hi rfl)
      else exact isFalse (by intro e; cases e; exact h rfl)
    | none => exact isFalse (by intro e; cases e)
  | none =>
    cases b with
    | signed _ _ => exact isFalse (by intro e; cases e)
    | none => exact isTrue rfl

/-- What an object says: an item, which the engine hashes, or protocol data. -/
inductive Msg (Item Body : Type) where
  | item (x : Item)
  | data (b : Body)
  deriving DecidableEq

/-- A wire object. -/
inductive Obj (L : Type) (seats : L → Nat) (Item Body : Type) where
  | mk (auth : Auth L seats) (msg : Msg Item Body) (carried : List (Obj L seats Item Body))

namespace Obj

variable {L : Type} {seats : L → Nat} {Item Body : Type}

def auth : Obj L seats Item Body → Auth L seats
  | mk a _ _ => a

def msg : Obj L seats Item Body → Msg Item Body
  | mk _ m _ => m

def carried : Obj L seats Item Body → List (Obj L seats Item Body)
  | mk _ _ cs => cs

/-- The item an object says, if any. -/
def item? : Obj L seats Item Body → Option Item
  | mk _ (.item x) _ => some x
  | _ => Option.none

/-- `Contains o o'`: `o'` is `o` or occurs, at any depth, in what `o` carries. -/
inductive Contains : Obj L seats Item Body → Obj L seats Item Body → Prop
  | refl (o : Obj L seats Item Body) : Contains o o
  | step {o c d : Obj L seats Item Body} : c ∈ o.carried → Contains c d → Contains o d

theorem Contains.trans {a b c : Obj L seats Item Body} (h₁ : Contains a b)
    (h₂ : Contains b c) : Contains a c := by
  induction h₁ with
  | refl => exact h₂
  | step hm _ ih => exact .step hm (ih h₂)

/-- The objects that `o` contains, `o` first. -/
def parts : Obj L seats Item Body → List (Obj L seats Item Body)
  | mk a m cs => mk a m cs :: partsList cs
where
  partsList : List (Obj L seats Item Body) → List (Obj L seats Item Body)
    | [] => []
    | c :: cs => parts c ++ partsList cs

section DecEq
variable [DecidableEq L] [DecidableEq Item] [DecidableEq Body]

mutual
/-- Decidable equality of objects. -/
def decEq : (a b : Obj L seats Item Body) → Decidable (a = b)
  | .mk a m cs, .mk a' m' cs' =>
    if ha : a = a' then
      if hm : m = m' then
        match decEqList cs cs' with
        | isTrue h => isTrue (by subst ha hm h; rfl)
        | isFalse h => isFalse (by intro e; injection e with _ _ e; exact h e)
      else isFalse (by intro e; injection e with _ e _; exact hm e)
    else isFalse (by intro e; injection e with e _ _; exact ha e)
def decEqList : (l l' : List (Obj L seats Item Body)) → Decidable (l = l')
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
  | a :: l, b :: l' =>
    match decEq a b with
    | isTrue h =>
      match decEqList l l' with
      | isTrue h' => isTrue (by rw [h, h'])
      | isFalse h' => isFalse (by intro e; injection e with _ e; exact h' e)
    | isFalse h => isFalse (by intro e; injection e with e _; exact h e)
end

instance : DecidableEq (Obj L seats Item Body) := decEq

end DecEq

end Obj

end Consensus.Model

end
