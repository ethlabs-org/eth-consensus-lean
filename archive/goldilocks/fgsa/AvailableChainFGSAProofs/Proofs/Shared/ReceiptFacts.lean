module
public import AvailableChainFGSA.Statements.FinalityView
public import AvailableChainKitFG.Certificates
public import AvailableChainFGSAClaims.Statements.Reads -- shake: keep (read API)

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

theorem receipt_finality (X : FGBlock (Fin p.n)) :
    (finalityView p X).F = (Window.derive p p.K_W X).F := by
  simp only [finalityView_def, Window.certificateFinality_def, Window.projectFinality_def]

theorem receipt_parent_path (X : FGBlock (Fin p.n)) : FGBlock.Preceq X.parent X := by
  cases X with
  | genesis => exact KitFG.preceq_refl _
  | node P s root body rows => exact KitFG.preceq_parent_node P s root body rows

omit [DecidableEq V] [Fintype V] in
theorem receipt_height_hj (X : FGBlock (Fin p.n)) :
    (heightView p X).h_j = (Window.derive p p.K_W X).h_j := by
  simp only [heightView_def, Window.projectHeight_def]

theorem receipt_height_genesis :
    (heightView p (.genesis : FGBlock (Fin p.n))).h = 1 := by
  rw [heightView_def, Window.derive_def, Window.projectHeight_def, Window.initial_def]

omit [DecidableEq V] [Fintype V] in
theorem receipt_actionTime_strictMono : StrictMono p.actionTime := by
  intro a b hab
  have hab' : (a : Int) < b := by exact_mod_cast hab
  have hR : (0 : Int) < p.R := by exact_mod_cast (show 0 < p.R by have := p.RLarge; omega)
  have hpos : (0 : Int) < 4 * p.Δ * (p.R : Int) :=
    mul_pos (mul_pos (by decide) p.deltaPos) hR
  change 4 * p.Δ * ((a * p.R : Nat) : Int) + 6 * p.Δ <
    4 * p.Δ * ((b * p.R : Nat) : Int) + 6 * p.Δ
  push_cast
  convert add_lt_add_right (mul_lt_mul_of_pos_left hab' hpos) (6 * p.Δ) using 1 <;> ring

end AvailableChain.FGSA.Run
end
