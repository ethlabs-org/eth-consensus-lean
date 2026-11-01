module
public import AvailableChainGeneric.Proofs.Pure.Quorum

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.Gen.Pure.Tests.Dominance

def leftChild : Block := .node .genesis 1 (nodeRoot Block.genesis.root 1 0) 0
def rightChild : Block := .node .genesis 1 (nodeRoot Block.genesis.root 1 1) 1
def children : Finset Block := {leftChild, rightChild}
def support (C : Block) : Finset (Fin 3) :=
  if C = leftChild then {0, 1} else {2}
def denominator : Finset (Fin 3) := {0, 1, 2}

-- Two sibling blocks have disjoint support sets, and only the left child is eligible.
theorem only_left_eligible : ∀ C ∈ children,
    denominator.card < 2 * (support C).card ↔ C = leftChild := by decide

-- Use the public closed statement with concrete premises checked by the kernel.
theorem unique_eligible : ∀ C ∈ children, ∀ D ∈ children,
    denominator.card < 2 * (support C).card →
    denominator.card < 2 * (support D).card → C = D :=
  maj_unique_child children support denominator (by decide) (by decide)

end AvailableChain.Gen.Pure.Tests.Dominance
