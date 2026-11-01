module
public import AvailableChainFGSA.Model.Window
public import AvailableChainKitFG.FrameBridgeDef -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG AvailableChain.KitFG

namespace Window

/-- [bp.heightBridge.v1] The eight height fields, in `heightOf` order. -/
def projectHeight {V : Type} (σ : State V) : KitFG.FGHeight V :=
  ⟨σ.L, σ.s, σ.h, σ.T_h, σ.target_participation, σ.progress, σ.h_j, σ.J⟩

theorem projectHeight_def {V : Type} (σ : State V) :
    projectHeight σ =
      ⟨σ.L, σ.s, σ.h, σ.T_h, σ.target_participation, σ.progress, σ.h_j, σ.J⟩ := rfl

/-- [spec 1186–1200] The window parent state with the child slot. -/
def parentState (p : Params) (K : Nat) (P : FGBlock (Fin p.n)) (s : Slot) :
    State (Fin p.n) :=
  { derive p K P with s := s }

theorem parentState_def (p : Params) (K : Nat) (P : FGBlock (Fin p.n)) (s : Slot) :
    parentState p K P s = { derive p K P with s := s } := rfl

/-- The parent state keeps the parent's height and entry. -/
theorem parentState_height_entry (p : Params) (K : Nat) (P : FGBlock (Fin p.n))
    (s : Slot) : (parentState p K P s).h = (projectHeight (derive p K P)).h ∧
      (parentState p K P s).T_h = (projectHeight (derive p K P)).T_h := ⟨rfl, rfl⟩

/-- [spec 1603–1604] The head fields read directly from the window state. -/
def headFields (p : Params) (K : Nat) (Hd : FGBlock (Fin p.n)) : HeadFields :=
  ⟨(derive p K Hd).h_j, (derive p K Hd).J.root, (derive p K Hd).h_F⟩

theorem headFields_def (p : Params) (K : Nat) (Hd : FGBlock (Fin p.n)) :
    headFields p K Hd =
      ⟨(derive p K Hd).h_j, (derive p K Hd).J.root, (derive p K Hd).h_F⟩ := rfl

end Window

/-- The active height view reads the window fold. -/
def heightView (p : Params) (B : FGBlock (Fin p.n)) : FGHeight (Fin p.n) :=
  Window.projectHeight (Window.derive p p.K_W B)

theorem heightView_def (p : Params) (B : FGBlock (Fin p.n)) :
    heightView p B = Window.projectHeight (Window.derive p p.K_W B) := rfl

end AvailableChain.FGSA
end
