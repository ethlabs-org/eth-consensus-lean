module
public import AvailableChainSimplexFG.Objects

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V]

-- port: DC/DecoupledConsensusModel/Execution/Setup.lean:51-56 (RootInjectiveOnAncestors)
/-- [helper] Roots identify blocks on the two compared chains (port: DC
`RootInjectiveOnAncestors`, a collision-free hash idealization in DC). Here the
ROOT-DIGEST W1 uses this explicit premise for the two full ancestor chains. -/
def RootInjectiveOn [RowCodec V] (B₁ B₂ : FGBlock V) : Prop :=
  ∀ X Y : FGBlock V, (X.Preceq B₁ ∨ X.Preceq B₂) → (Y.Preceq B₁ ∨ Y.Preceq B₂) →
    X.root = Y.root → X = Y

/-- [ROOT-DIGEST W1; DC RootInjectiveOnAncestors] The two-chain root premise. -/
theorem RootInjectiveOn_def [RowCodec V] (B₁ B₂ : FGBlock V) :
    RootInjectiveOn B₁ B₂ =
      (∀ X Y : FGBlock V, (X.Preceq B₁ ∨ X.Preceq B₂) →
        (Y.Preceq B₁ ∨ Y.Preceq B₂) → X.root = Y.root → X = Y) := rfl

end AvailableChain.KitFG
end
