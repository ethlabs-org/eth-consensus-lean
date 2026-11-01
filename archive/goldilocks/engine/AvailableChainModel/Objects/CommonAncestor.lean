module
public import AvailableChainModel.Objects.Blocks

@[expose] public section

namespace AvailableChain.Block

/-- The deepest common ancestor. Walk towards genesis until an ancestor of
`B` is also a prefix of `C`. Equality is structural block equality. -/
def meet : Block → Block → Block
  | .genesis, _ => .genesis
  | B@(.node p _ _ _), C => if Preceq B C then B else meet p C

/-- The first-unfold equation for the common ancestor walk. -/
theorem meet_def (B C : Block) : meet B C =
    (match B with
    | .genesis => .genesis
    | B@(.node p _ _ _) => if Preceq B C then B else meet p C) := by
  cases B <;> rfl

end AvailableChain.Block
