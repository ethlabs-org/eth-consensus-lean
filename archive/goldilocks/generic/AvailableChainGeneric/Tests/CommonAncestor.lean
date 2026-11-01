module
public import AvailableChainGeneric.Proofs.Pure.CommonAncestor -- shake: keep (examples)

public section

namespace AvailableChain.Gen.Pure.Tests.CommonAncestor

def stem : Block := .node .genesis 1 ⟨1⟩ 10
def left : Block := .node stem 2 ⟨2⟩ 20
def right : Block := .node stem 2 ⟨3⟩ 30
def tip : Block := .node left 3 ⟨4⟩ 40
def forkTip : Block := .node right 3 ⟨5⟩ 50
def other : Block := .node .genesis 1 ⟨6⟩ 60

-- Equal blocks, prefixes in both orders, siblings, and unequal branch depths.
example : Block.meet left left = left := by decide
example : Block.Preceq stem tip ∧ Block.meet stem tip = stem := by decide
example : Block.meet tip stem = stem := by decide
example : Block.meet left right = stem := by decide
example : Block.meet tip right = stem := by decide
example : Block.meet tip forkTip = stem := by decide
example : Block.meet tip other = .genesis := by decide

-- Genesis in both orders, including two genesis inputs.
example : Block.meet .genesis tip = .genesis := by decide
example : Block.meet tip .genesis = .genesis := by decide
example : Block.meet .genesis .genesis = .genesis := by decide

-- Structural equality distinguishes blocks even when their stored roots agree.
example : Block.meet left (.node stem 2 ⟨2⟩ 99) = stem := by decide

-- Exercise the public lemmas with arbitrary inputs.
example (B C : Block) : Block.Preceq (Block.meet B C) B ∧
    Block.Preceq (Block.meet B C) C := meet_prefix_statement B C
example (X B C : Block) (hB : Block.Preceq X B) (hC : Block.Preceq X C) :
    Block.Preceq X (Block.meet B C) := meet_maximal hB hC
example (B C : Block) : Block.meet B C = Block.meet C B := meet_comm B C
example (X B C : Block) : Block.Preceq X (Block.meet B C) ↔
    Block.Preceq X B ∧ Block.Preceq X C := preceq_meet_iff X B C
example (B C : Block) (h : Block.Preceq B C) : Block.meet B C = B :=
  meet_of_preceq_left h
example (B C : Block) (h : Block.Preceq C B) : Block.meet B C = C :=
  meet_of_preceq_right h
example (K C H X : Block) (hK : K = Block.meet C H) (hX : Block.Preceq X K) :
    Block.Compatible X C ∧ Block.Compatible X H := compatible_of_preceq_meet hK hX

end AvailableChain.Gen.Pure.Tests.CommonAncestor
