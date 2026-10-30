module

@[expose] public section

/-! Step 1 self-test: a warning (a deprecated name), so `lake build --wfail` fails, also when Lake replays the
warning of the already built module. -/

namespace CheckFixtures.Warn

@[deprecated "use `fresh`" (since := "2026-10-30")] def old : Nat := 1

def fresh : Nat := 1

def user : Nat := old

end CheckFixtures.Warn
