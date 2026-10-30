-- Fixture for step 7 (never built): the proof examples (lines 4, 6, 7, 11-15, 18; 11 follows a char literal that must not open a string) are flagged; bare references and comments are not.
/- example : 2 = 2 := rfl -/
example := @Nat.succ
example : 1 = 1 := rfl
theorem my_example : 3 = 3 := rfl
example := @id (0 = 0) rfl
example := @id
    (0 = 0) rfl
example := @Nat.zero
def q : Char := '"'
example : 5 = 5 := rfl
example := @id<|rfl
example := @Nat.succ "x"
example := @Nat.succ 'x'
example := @Nat.succ r"x"
example := @Nat.zero
example := ``Nat.zero
example := ``Nat.succ rfl
