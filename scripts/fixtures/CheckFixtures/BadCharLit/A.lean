module

@[expose] public section

namespace CheckFixtures.BadCharLit

/-! A character literal `'"'` must not open a string for the source scan (it would hide the next
lines), and a raw string literal is not supported in Spec sources (reported, fail-closed). -/

def c : Char := '"'
example : True := trivial
def d : String := "x"

def r : String := r"raw"

end CheckFixtures.BadCharLit
