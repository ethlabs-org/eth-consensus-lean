module

@[expose] public section

namespace CheckFixtures.Proof

/-! Support module for the fixtures: proofs, an instance and a macro. Importing it into a
Spec-like group is a forbidden import. -/

def helper : Nat := 1

theorem helper_eq : helper = 1 := rfl

theorem le_helper (n : Nat) : n ≤ n + helper := Nat.le_add_right n helper

structure Foo where
  x : Nat

instance : Inhabited Foo := ⟨⟨0⟩⟩

/-- Expands to `1`: a term built through this macro contains no constant of this module. -/
macro "mkOne" : term => `(1)

end CheckFixtures.Proof
