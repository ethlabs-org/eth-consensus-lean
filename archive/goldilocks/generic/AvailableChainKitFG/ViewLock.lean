module
public import AvailableChainSimplexFG.Frame

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- Every block in the view whose state height is strictly above `θ`
extends `Fb`. The strict bound is the `hext` bound in
`Correspondence.lean:628` (GLY §C.2; step-2 ruling B08). -/
def ViewLock (E : Electorate V) (cfg : FGConfig) (θ : Nat)
    (Fb : FGBlock V) (vw : View V) : Prop :=
  ∀ W ∈ vw, θ < hOf E cfg W → FGBlock.Preceq Fb W

theorem ViewLock_def (E : Electorate V) (cfg : FGConfig) (θ : Nat)
    (Fb : FGBlock V) (vw : View V) :
    ViewLock E cfg θ Fb vw = (∀ W ∈ vw, θ < hOf E cfg W → FGBlock.Preceq Fb W) := by
  rw [ViewLock]

end AvailableChain.KitFG
end
