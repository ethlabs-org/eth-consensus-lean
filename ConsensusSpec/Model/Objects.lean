module
public import Mathlib.Data.List.Basic

@[expose] public section

/-! # Model objects (L1)

Authentications, messages and wire objects of the execution model. Nothing here
is supplied by a protocol beyond its types.

* `Auth`: who signed an object, and in which role: key `k : Fin n` (the run's
  PKI maps keys to validators) signing in role `r`, or nobody. Honest code never
  chooses an `Auth`: the engine attaches it.
* `Msg`: an item (hashed by the engine) or protocol data.
* `Obj`: an authentication, a message, and the objects it carries,
  structurally: the item and body types are fixed before `Obj`, so neither can
  hide a signed object. -/

namespace Consensus.Model

/-- The authentication of an object: key `k` signing in role `r`, or nobody.
The envelope binds the role, so a signature made for one duty cannot be
replayed for another. -/
inductive Auth (n : Nat) (Role : Type) where
  | signed (k : Fin n) (r : Role)
  | none
  deriving DecidableEq

/-- What an object says: an item, which the engine hashes, or protocol data. -/
inductive Msg (Item Body : Type) where
  | item (x : Item)
  | data (b : Body)
  deriving DecidableEq

/-- A wire object. -/
inductive Obj (n : Nat) (Role Item Body : Type) where
  | mk (auth : Auth n Role) (msg : Msg Item Body) (carried : List (Obj n Role Item Body))

namespace Obj

variable {n : Nat} {Role Item Body : Type}

def auth : Obj n Role Item Body → Auth n Role
  | mk a _ _ => a

def msg : Obj n Role Item Body → Msg Item Body
  | mk _ m _ => m

def carried : Obj n Role Item Body → List (Obj n Role Item Body)
  | mk _ _ cs => cs

/-- The key that signed an object, if any. -/
def signer? (o : Obj n Role Item Body) : Option (Fin n) :=
  match o.auth with
  | .signed k _ => some k
  | .none => Option.none

/-- The item an object says, if any. -/
def item? : Obj n Role Item Body → Option Item
  | mk _ (.item x) _ => some x
  | _ => Option.none

/-- `o`, then the parts of every object it carries, in order. -/
def parts : Obj n Role Item Body → List (Obj n Role Item Body)
  | mk a m cs => mk a m cs :: partsList cs
where
  partsList : List (Obj n Role Item Body) → List (Obj n Role Item Body)
    | [] => []
    | c :: cs => parts c ++ partsList cs

/-- `Contains o d`: `d` is `o` or occurs, at any depth, in what `o` carries. -/
def Contains (o d : Obj n Role Item Body) : Prop := d ∈ o.parts

section DecEq
variable [DecidableEq Role] [DecidableEq Item] [DecidableEq Body]

mutual
/-- Decidable equality of objects. -/
def decEq : (a b : Obj n Role Item Body) → Decidable (a = b)
  | .mk a m cs, .mk a' m' cs' =>
    if ha : a = a' then
      if hm : m = m' then
        match decEqList cs cs' with
        | isTrue h => isTrue (by subst ha hm h; rfl)
        | isFalse h => isFalse (by intro e; injection e with _ _ e; exact h e)
      else isFalse (by intro e; injection e with _ e _; exact hm e)
    else isFalse (by intro e; injection e with e _ _; exact ha e)
def decEqList : (l l' : List (Obj n Role Item Body)) → Decidable (l = l')
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

instance : DecidableEq (Obj n Role Item Body) := decEq

end DecEq

end Obj

end Consensus.Model

end
