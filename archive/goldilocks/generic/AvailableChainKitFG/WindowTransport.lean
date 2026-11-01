module
public import AvailableChainKitFG.WindowTransportDef
public import AvailableChainKitFG.WindowViewsDef

public section

namespace AvailableChain.KitFG.WindowFoldMap

open AvailableChain.SimplexFG

variable {V W : Type} [DecidableEq V] [Fintype V] [RowCodec V]
variable {E : Electorate V} {cfg : FGConfig} {K : Nat}
variable {oldInitial : W} {oldStep : W → FGBlock V → List (Row V) → W}
variable {oldFold : FGBlock V → W} {toWindow : W → SimplexFG.Window.State V}
variable (m : WindowFoldMap E cfg K oldInitial oldStep oldFold toWindow)

include m

/-- The four equations determine the complete window state at every block. -/
theorem fold_eq (B : FGBlock V) :
    toWindow (oldFold B) = SimplexFG.Window.derive E cfg K B := by
  induction B with
  | genesis => rw [m.genesis, m.initial]; rfl
  | node q s r x rs ih =>
      rw [m.node, m.step, ih]
      rfl

/-- Any read of the converted state agrees with the same generic read. -/
theorem view_eq {A : Sort*} (read : SimplexFG.Window.State V → A) (B : FGBlock V) :
    read (toWindow (oldFold B)) = read (SimplexFG.Window.derive E cfg K B) :=
  congrArg read (m.fold_eq B)

theorem foldMap_height_eq (B : FGBlock V) :
    Window.projectHeight (toWindow (oldFold B)) = Window.heightView E cfg K B :=
  m.view_eq Window.projectHeight B

theorem foldMap_finality_eq (B : FGBlock V) :
    Window.projectFinality (toWindow (oldFold B)) = Window.finalityView E cfg K B :=
  m.view_eq Window.projectFinality B

end AvailableChain.KitFG.WindowFoldMap
end
