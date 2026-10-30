-- Fixture for step 7 (never built): an unfinished proof in a Lemmas file, counted (once), not flagged.
/-- A docstring that says sorry, /- nested: admit -/, is not counted. -/
theorem lemma_t : 1 = 1 := sorry -- nor is this sorry
def msg : String := "sorry, \"admit\" is not counted"
def nm : Lean.Name := `sorry
def q : Char := '"'
def raw : String := r#"sorry "admit""#
def h' (x' : Nat) : Nat := x'
