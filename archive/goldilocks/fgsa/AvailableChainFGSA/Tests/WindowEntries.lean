module
public import AvailableChainFGSA.Statements.WindowEntries -- shake: keep (examples)

-- The fixtures and examples are local to this test module.
set_option linter.privateModule false

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.FGSA.Window.EntriesTests

open AvailableChain.SimplexFG

private abbrev params : Params :=
  { Δ := 1, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

/-- Genesis covers its own key `(0, genesis)`. -/
example : CoveredW params .genesis 0 .genesis := by
  rw [CoveredW_def, derive_def]
  exact ⟨Nat.zero_le _, rfl⟩

/-- Genesis retains no key: its window is empty. -/
example : ¬ RetainedW params .genesis 0 .genesis := by
  rw [RetainedW_def, derive_def]
  simp [initial]

end AvailableChain.FGSA.Window.EntriesTests
end
