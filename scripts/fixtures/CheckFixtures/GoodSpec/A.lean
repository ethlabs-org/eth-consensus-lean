module
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Basic.Countable.Defs

@[expose] public section

namespace CheckFixtures.GoodSpec

/-! A clean Spec-like group: every legitimate shape of definition the real Spec uses. -/

/-- A Prop structure (its fields are projections). -/
structure PS : Prop where
  h : 1 = 1

/-- An inductive with derived instances. -/
inductive Color where
  | red
  | green
  deriving DecidableEq, Repr

/-- A Prop-valued definition (a proposition, not a proof). -/
def P : Prop := ∀ n : Nat, n = n

/-- Data with embedded tactic proofs (as `ParentRef.equiv` in Chains.lean). -/
def colorEquiv : Color ≃ Color where
  toFun := id
  invFun := id
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

/-- A structure field with a default-value proof. -/
structure Bounded where
  n : Nat
  h : n ≤ n := Nat.le_refl n

/-- Structural recursion. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => n + 1 + sumTo n

/-- Well-founded recursion with `termination_by` / `decreasing_by`. -/
def halve (n : Nat) : Nat := if h : n < 2 then 0 else 1 + halve (n - 2)
termination_by n
decreasing_by omega

/-- A Prop-class instance (allowlisted with `class=Countable`). -/
instance instCountableColor : Countable Color :=
  ⟨⟨fun c => match c with | .red => 0 | .green => 1, by
    intro a b h; cases a <;> cases b <;> simp_all⟩⟩

/-- A nested inductive with mutual structural decidable equality (as `Obj` in Model/Objects.lean):
`_sizeOf_<n>_eq`, `brecOn_<n>.eq`, proof auxiliaries used only by `_sunfold`. -/
inductive Tree where
  | node (k : Nat) (cs : List Tree)

mutual
/-- Decidable equality of trees. -/
def Tree.decEq : (a b : Tree) → Decidable (a = b)
  | .node k cs, .node k' cs' =>
    if hk : k = k' then
      match Tree.decEqList cs cs' with
      | isTrue h => isTrue (by subst hk h; rfl)
      | isFalse h => isFalse (by intro e; injection e with _ e; exact h e)
    else isFalse (by intro e; injection e with e _; exact hk e)
def Tree.decEqList : (l l' : List Tree) → Decidable (l = l')
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
  | a :: l, b :: l' =>
    match Tree.decEq a b with
    | isTrue h =>
      match Tree.decEqList l l' with
      | isTrue h' => isTrue (by rw [h, h'])
      | isFalse h' => isFalse (by intro e; injection e with _ e; exact h' e)
    | isFalse h => isFalse (by intro e; injection e with e _; exact h e)
end

instance : DecidableEq Tree := Tree.decEq

/-- An abbreviation. -/
abbrev Small := Fin 3

end CheckFixtures.GoodSpec
