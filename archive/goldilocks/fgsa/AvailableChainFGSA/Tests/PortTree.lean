module
public import AvailableChainFGSA.Proofs.Port.Tree -- shake: keep (examples)

public section

namespace AvailableChain.FGSA.Next.TreeTests

open AvailableChain.SimplexFG

/-- Test fixture: the same small parameters as Window.StoreTests. -/
abbrev p : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }
private def first : FGBlock (Fin 4) := .node .genesis 1 ⟨100⟩ 0 []
private def second : FGBlock (Fin 4) := .node first 2 ⟨101⟩ 0 []
private def fork : FGBlock (Fin 4) := .node .genesis 3 ⟨102⟩ 0 []
private def unheld : FGBlock (Fin 4) := .node second 4 ⟨103⟩ 0 []
private def st : State 4 :=
  { base := { GridCO.initial 4 .root with
      blocks := [eraseFG second, .genesis, eraseFG first, eraseFG fork] }
    fg := { Store.init with TF := {.genesis, first, second, fork}, F := first } }

/-- [spec 305–326] The held ancestor below F remains stored but is excluded. -/
example : FGBlock.genesis ∈ st.fg.TF ∧ FGBlock.genesis ∉ tree p st := by decide

/-- [spec 305–326] F and a held block above F are included. -/
example : first ∈ tree p st ∧ second ∈ tree p st := by decide

/-- [spec 305–326] A conflicting held block and an unheld descendant are excluded. -/
example : fork ∈ st.fg.TF ∧ fork ∉ tree p st ∧
    FGBlock.Preceq st.fg.F unheld ∧ unheld ∉ tree p st := by decide

/-- [spec 305–326, 975–1015] The erased tree keeps the cumulative list order;
the base list and its resolution domain still hold the ancestor below F. -/
example : erasedList st (tree p st) = [eraseFG second, eraseFG first] ∧
    GridCO.resolutionTree st.base = st.base.blocks ∧
    Block.genesis ∈ GridCO.resolutionTree st.base := by decide

/-- [spec 305–326] Genesis is included in the initial tree. -/
example : FGBlock.genesis ∈ tree p (initial 4) := by decide

end AvailableChain.FGSA.Next.TreeTests
end
