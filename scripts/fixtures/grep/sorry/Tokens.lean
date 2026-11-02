-- Fixture for the sorry count of steps 7 and 10 (not built by check.sh): `admit` as a field, projection, longer
-- name, structure-instance field or named argument is not counted; the thirteen holes are, also a line-start
-- `admit : T` inside a bracket, after column-0 tactic lines or multi-line (raw) strings (`lake env lean` on this
-- file reports `declaration uses sorry` for exactly those thirteen theorems).
structure Closed (P : Nat → Prop) : Prop where
  admit : ∀ n, P n → P (n + 1)
  admit_foo : P 0
theorem use (h : Closed P) : P 2 := h.admit 1 (Closed.admit h 0 h.admit_foo)
theorem inst : Closed (fun _ => True) := { admit := fun _ _ => trivial, admit_foo := trivial }
theorem inst' : Closed (fun _ => True) := ⟨fun _ _ => trivial, trivial⟩
def named (f : (admit : Nat) → Nat) := f (admit := 0)
theorem hole_term : 1 = 2 := sorry
theorem hole_tactic : 1 = 2 := by admit
theorem hole_nested : 1 = 2 := Eq.trans (by sorry) rfl
theorem hole_ascribed : 1 = 2 := (sorry : 1 = 2)
theorem hole_ascribed_tactic : 1 = 2 := (by admit : 1 = 2)
theorem hole_block : 1 = 2 := by
  admit
theorem hole_cont : 1 = 2 := (by
  admit : 1 = 2)
theorem hole_cont_exact : 1 = 2 := by
  exact (by
    skip
    admit : 1 = 2)
theorem hole_cont_anon : 1 = 2 ∧ True := ⟨(by
  admit : 1 = 2), trivial⟩
theorem hole_cont_arg : 1 = 2 := Eq.trans (by
  admit : 1 = 2) rfl
theorem hole_col0 : 1 = 2 := (by
skip
admit : 1 = 2)
theorem hole_string : 1 = 2 := (by
  have : "a
b" = "a
b" := rfl
  admit : 1 = 2)
theorem hole_raw : 1 = 2 := (by
  have : r"x
y" = r"x
y" := rfl
  admit : 1 = 2)
