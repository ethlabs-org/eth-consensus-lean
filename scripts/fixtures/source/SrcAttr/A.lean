-- Source-only fixture (not compiled): attributes that register user code, also across lines.
def initFn : IO Unit := pure ()
@[init initFn] def foo : IO Unit := pure ()
attribute
  [local
    tactic Lean.Parser.Tactic.simp] foo
@[simp, app_unexpander Nat.succ] def bar : Nat := 0
