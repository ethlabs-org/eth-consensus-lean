-- Source-only fixture (not compiled): words that look banned but are not commands or attributes.
/- example theorem run_cmd #eval inside a comment, /- nested -/ still a comment -/
structure S where
  init : Nat
  tactic : Nat
def s : S := { init := 0, tactic := 1 }
def str : String := "theorem example #eval -- not a comment /- nor this"
def ch : Char := 'x'
def esc : Char := '\''
def arr : Array Nat := #[1, 2]
def h' : Nat := s.init
attribute [simp] Nat.add_zero
