module
public import AvailableChainSimplexFG.Window

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

/-- Equations that relate another fold to the generic window fold. -/
structure WindowFoldMap {V W : Type}
    [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (oldInitial : W)
    (oldStep : W → FGBlock V → List (Row V) → W)
    (oldFold : FGBlock V → W)
    (toWindow : W → SimplexFG.Window.State V) : Prop where
  initial : toWindow oldInitial = SimplexFG.Window.initial
  genesis : oldFold .genesis = oldInitial
  node : ∀ q s r x rs,
    oldFold (.node q s r x rs) =
      oldStep (oldFold q) (.node q s r x rs) rs
  step : ∀ σ B rows,
    toWindow (oldStep σ B rows) =
      SimplexFG.Window.transition E cfg K (toWindow σ) B rows

/-- Expand the contract into its four required equations. -/
theorem WindowFoldMap_def {V W : Type}
    [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (oldInitial : W) (oldStep : W → FGBlock V → List (Row V) → W)
    (oldFold : FGBlock V → W) (toWindow : W → SimplexFG.Window.State V) :
    WindowFoldMap E cfg K oldInitial oldStep oldFold toWindow =
      (toWindow oldInitial = SimplexFG.Window.initial ∧
        oldFold .genesis = oldInitial ∧
        (∀ q s r x rs, oldFold (.node q s r x rs) =
          oldStep (oldFold q) (.node q s r x rs) rs) ∧
        ∀ σ B rows, toWindow (oldStep σ B rows) =
          SimplexFG.Window.transition E cfg K (toWindow σ) B rows) := by
  apply propext
  exact ⟨fun m => ⟨m.initial, m.genesis, m.node, m.step⟩,
    fun ⟨hi, hg, hn, hs⟩ => ⟨hi, hg, hn, hs⟩⟩

end AvailableChain.KitFG
end
