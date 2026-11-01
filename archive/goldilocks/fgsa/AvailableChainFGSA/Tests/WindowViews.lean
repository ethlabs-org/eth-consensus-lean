module
public import AvailableChainFGSA.Model.WindowViews -- shake: keep (examples)

-- The fixtures and examples are local to this test module.
set_option linter.privateModule false

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.FGSA.Window.ViewTests

open AvailableChain.SimplexFG

private abbrev params : Params :=
  { Δ := 1, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

private def block : FGBlock (Fin 1) :=
  .node .genesis 1 ⟨100⟩ 0 [⟨0, .vote 1 genesisRoot false, none⟩]

example : Window.projectHeight (Window.derive params 2 block) =
    KitFG.heightOf (SimplexFG.derive params.E params.cfg block) := by rfl

example : headFields params 2 block = ⟨1, genesisRoot, 0⟩ := by decide +kernel

end AvailableChain.FGSA.Window.ViewTests
end
