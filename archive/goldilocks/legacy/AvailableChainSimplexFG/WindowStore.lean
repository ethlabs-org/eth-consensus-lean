module
public import AvailableChainSimplexFG.Window
public import AvailableChainSimplexFG.Store

@[expose] public section

namespace AvailableChain.SimplexFG.Window

open AvailableChain.SimplexFG hiding derive acceptViable update_finality on_block

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- [spec 1295–1301] `viable_tree`: acceptance uses the window height view and the live store
caches. -/
def acceptViable (E : Electorate V) (cfg : FGConfig) (K : Nat) (st : SimplexFG.Store V) :
    Finset (FGBlock V) :=
  st.TF.filter (fun B => FGBlock.preceq st.F B &&
    decide (∃ W ∈ st.TF, FGBlock.Preceq B W ∧ st.h_max - 1 ≤ (derive E cfg K W).h))

theorem acceptViable_def (E : Electorate V) (cfg : FGConfig) (K : Nat) (st : SimplexFG.Store V) :
    acceptViable E cfg K st =
  st.TF.filter (fun B => FGBlock.preceq st.F B &&
    decide (∃ W ∈ st.TF, FGBlock.Preceq B W ∧ st.h_max - 1 ≤ (derive E cfg K W).h)) := rfl

/-- [spec 1135–1148] `update_finality`: update height, then the justification pair, then accepted
window finality. -/
def update_finality (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (st : SimplexFG.Store V) (B : FGBlock V) :
    SimplexFG.Store V :=
  let σ := derive E cfg K B
  let st := { st with h_max := max st.h_max σ.h }
  let st := if FGBlock.preceq st.F σ.J && decide (lexKey (st.h_j, st.J) < lexKey (σ.h_j, σ.J))
    then { st with J := σ.J, h_j := σ.h_j } else st
  if FGBlock.preceq st.F σ.F && decide (st.F ≠ σ.F) && FGBlock.preceq σ.F st.J &&
      decide (σ.F ∈ acceptViable E cfg K st)
    then { st with F := σ.F } else st

theorem update_finality_def (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (st : SimplexFG.Store V) (B : FGBlock V) :
    update_finality E cfg K st B =
  let σ := derive E cfg K B
  let st := { st with h_max := max st.h_max σ.h }
  let st := if FGBlock.preceq st.F σ.J && decide (lexKey (st.h_j, st.J) < lexKey (σ.h_j, σ.J))
    then { st with J := σ.J, h_j := σ.h_j } else st
  if FGBlock.preceq st.F σ.F && decide (st.F ≠ σ.F) && FGBlock.preceq σ.F st.J &&
      decide (σ.F ∈ acceptViable E cfg K st)
    then { st with F := σ.F } else st := rfl

/-- [spec 1087–1113] `on_block`: apply the SimplexFG refusals before insertion and window finality
acceptance. Admission, not this function, applies three further spec refusals: the slot bound
`B.slot > Σ.s` (:1089), the slot-`B.slot` proposer signature (:1092–1095), and R6-window on the
parent post-state (:1098–1100). -/
def on_block (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (st : SimplexFG.Store V) (B : FGBlock V) :
    SimplexFG.Store V :=
  if B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot then st
  else update_finality E cfg K { st with TF := insert B st.TF } B

theorem on_block_def (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (st : SimplexFG.Store V) (B : FGBlock V) :
    on_block E cfg K st B =
  if B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot then st
  else update_finality E cfg K { st with TF := insert B st.TF } B := rfl

end AvailableChain.SimplexFG.Window
end
