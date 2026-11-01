module
public import AvailableChainFGSA.Model.Window

@[expose] public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding derive acceptViable update_finality on_block

/-- [spec 1295–1301] `viable_tree`: acceptance uses the window height view and the live store
caches. -/
def acceptViable (p : Params) (K : Nat) (st : SimplexFG.Store (Fin p.n)) :
    Finset (FGBlock (Fin p.n)) :=
  st.TF.filter (fun B => FGBlock.preceq st.F B &&
    decide (∃ W ∈ st.TF, FGBlock.Preceq B W ∧ st.h_max - 1 ≤ (derive p K W).h))

theorem acceptViable_def (p : Params) (K : Nat) (st : SimplexFG.Store (Fin p.n)) :
    acceptViable p K st =
  st.TF.filter (fun B => FGBlock.preceq st.F B &&
    decide (∃ W ∈ st.TF, FGBlock.Preceq B W ∧ st.h_max - 1 ≤ (derive p K W).h)) := rfl

/-- [spec 1135–1148] `update_finality`: update height, then the justification pair, then accepted
window finality. -/
def update_finality (p : Params) (K : Nat)
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    SimplexFG.Store (Fin p.n) :=
  let σ := derive p K B
  let st := { st with h_max := max st.h_max σ.h }
  let st := if FGBlock.preceq st.F σ.J && decide (lexKey (st.h_j, st.J) < lexKey (σ.h_j, σ.J))
    then { st with J := σ.J, h_j := σ.h_j } else st
  if FGBlock.preceq st.F σ.F && decide (st.F ≠ σ.F) && FGBlock.preceq σ.F st.J &&
      decide (σ.F ∈ acceptViable p K st)
    then { st with F := σ.F } else st

theorem update_finality_def (p : Params) (K : Nat)
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    update_finality p K st B =
  let σ := derive p K B
  let st := { st with h_max := max st.h_max σ.h }
  let st := if FGBlock.preceq st.F σ.J && decide (lexKey (st.h_j, st.J) < lexKey (σ.h_j, σ.J))
    then { st with J := σ.J, h_j := σ.h_j } else st
  if FGBlock.preceq st.F σ.F && decide (st.F ≠ σ.F) && FGBlock.preceq σ.F st.J &&
      decide (σ.F ∈ acceptViable p K st)
    then { st with F := σ.F } else st := rfl

/-- [spec 1087–1113] `on_block`: apply the SimplexFG refusals before insertion and window finality
acceptance. Admission, not this function, applies three further spec refusals: the slot bound
`B.slot > Σ.s` (:1089), the slot-`B.slot` proposer signature (:1092–1095), and R6-window on the
parent post-state (:1098–1100). -/
def on_block (p : Params) (K : Nat)
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    SimplexFG.Store (Fin p.n) :=
  if B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot then st
  else update_finality p K { st with TF := insert B st.TF } B

theorem on_block_def (p : Params) (K : Nat)
    (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n)) :
    on_block p K st B =
  if B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot then st
  else update_finality p K { st with TF := insert B st.TF } B := rfl

end AvailableChain.FGSA.Window
end
