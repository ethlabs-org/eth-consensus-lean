module
public import AvailableChainSimplexFG.Store
public import AvailableChainSimplexFG.Frame -- shake: keep (re-export)
public import AvailableChainSimplexFG.ChainState -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V] (E : Electorate V)
  (cfg : FGConfig)

/-- [helper] The store invariant. `pair` and `FJ` are what the F-acceptance
test needs; `Fcar` is the admitted block that finalized F (the accepting
carrier), which replaces the deleted F basis. There is one tree, so there is
no raw-tree field. -/
structure StoreInv (st : Store V) : Prop where
  closed : ∀ B ∈ st.TF, B.parent ∈ st.TF
  gen : FGBlock.genesis ∈ st.TF
  Fmem : st.F ∈ st.TF
  hmax : st.h_max = frontier E cfg st.TF
  pair : (st.h_j, st.J) = lexMax E cfg st.F st.TF
  FJ : FGBlock.Preceq st.F st.J
  Fcar : ∃ K ∈ st.TF, (derive E cfg K).F = st.F

end AvailableChain.KitFG
end
