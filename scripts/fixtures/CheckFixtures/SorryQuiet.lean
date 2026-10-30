module

@[expose] public section

/-! Step 1 self-test: with `warn.sorry = false` (lakefile) a `sorry` logs nothing, so `lake build --wfail` passes;
where it may appear is checked by steps 3, 3b and 7. -/

theorem CheckFixtures.SorryQuiet.t : 1 = 1 := sorry
