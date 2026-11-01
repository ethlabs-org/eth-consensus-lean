module
public import AvailableChainFGSA.Model.Window

@[expose] public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG

/-- [f07w plan §1.1; bp 01:421–424] The window key `(j, U)` is retained at `B`: some
entry of `σ(B) = derive p p.K_W B` has certificate height `j` and block `U`. The key is
`(j, U)`, not `U` alone and not the latest `(h_j, J)`. -/
def RetainedW (p : Params) (B : FGBlock (Fin p.n)) (j : Height) (U : FGBlock (Fin p.n)) :
    Prop :=
  ∃ e ∈ (derive p p.K_W B).W, e.j = j ∧ e.X = U

theorem RetainedW_def (p : Params) (B : FGBlock (Fin p.n)) (j : Height)
    (U : FGBlock (Fin p.n)) :
    RetainedW p B j U = ∃ e ∈ (derive p p.K_W B).W, e.j = j ∧ e.X = U := rfl

/-- [f07w plan §1.1; bp 01:405–409] The window key `(j, U)` is covered at `B`:
`j ≤ h_F` and `U ⪯ F` in `σ(B) = derive p p.K_W B`. -/
def CoveredW (p : Params) (B : FGBlock (Fin p.n)) (j : Height) (U : FGBlock (Fin p.n)) :
    Prop :=
  j ≤ (derive p p.K_W B).h_F ∧ FGBlock.Preceq U (derive p p.K_W B).F

theorem CoveredW_def (p : Params) (B : FGBlock (Fin p.n)) (j : Height)
    (U : FGBlock (Fin p.n)) :
    CoveredW p B j U =
      (j ≤ (derive p p.K_W B).h_F ∧ FGBlock.Preceq U (derive p p.K_W B).F) := rfl

/-- An identity bit in the retained entry with the exact key `(j, U)`. -/
def EntryBitW (p : Params) (B : FGBlock (Fin p.n)) (j : Height)
    (U : FGBlock (Fin p.n)) (i : Fin p.n) : Prop :=
  ∃ e ∈ (derive p p.K_W B).W, e.j = j ∧ e.X = U ∧ i ∈ e.Q

theorem EntryBitW_def (p : Params) (B : FGBlock (Fin p.n)) (j : Height)
    (U : FGBlock (Fin p.n)) (i : Fin p.n) :
    EntryBitW p B j U i =
      (∃ e ∈ (derive p p.K_W B).W, e.j = j ∧ e.X = U ∧ i ∈ e.Q) := rfl

end AvailableChain.FGSA.Window
end
