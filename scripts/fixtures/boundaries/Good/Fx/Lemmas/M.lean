module

public import Fx.Lemmas.L

/-- Not the attribute: `@[expose]` in a docstring. -/
def notExposed : String := "@[expose]"
@[no_expose, exposeFoo, foo_expose, Foo.expose] def notExposed' : Char := ']'
def «@[expose]» : Nat := 0
theorem m : S := l
