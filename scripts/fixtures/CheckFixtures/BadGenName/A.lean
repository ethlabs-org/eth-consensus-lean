module

@[expose] public section

namespace CheckFixtures.BadGenName

/-! Proofs written by hand under names the compiler uses for its auxiliaries. Each has a declaration
range, so `content` rejects it whatever its name; the comments say which name rule each one forges. -/

def foo : Nat := 0
/-- structural suffix of a constructor, on a definition -/
def foo.inj : True := trivial

/-- equational suffix, declared before its parent exists -/
def earlier.eq_999 : True := trivial
def earlier : Nat := 0

/-- elaborator auxiliary, reachable from its parent's value -/
def bar._proof_99 : True := trivial
def bar : {n : Nat // True} := ⟨0, bar._proof_99⟩

def Foo : Nat := 0
def Foo.injEq : 2 + 2 = 4 := rfl
def Foo.sizeOf_spec : ∀ n : Nat, n + 0 = n := fun _ => rfl
def Foo._default : 1 = 1 := rfl
def Foo.splitter : True := trivial
def Foo._flat_ctor : True := trivial

inductive Col where
  | r
  | g

/-- structural suffix of a constructor, on an inductive type -/
def Col.injEq : 3 = 3 := rfl

/-- auxiliary under a nested namespace of a legitimate parent -/
def baz : Nat := 0
def baz.Inner._proof_1 : True := trivial

/-- a `where` function named like a termination proof, reachable from its parent -/
def wh : {n : Nat // True} := ⟨0, proof_1⟩
where proof_1 : True := trivial

end CheckFixtures.BadGenName
