module
public import AvailableChainGeneric -- shake: keep (examples)

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.Gen.Pure.Tests.Batch

-- The largest denominator passes when the anchor score equals the honest count.
example : 5 < 2 * 3 ∧ decide (5 < 2 * 3) = true :=
  anchor_passes 3 2 5 3 ⟨by decide⟩ (by decide) (by decide)

-- The unsupported score and the honest count must fit in the same denominator.
example : 2 * 2 ≤ 5 ∧ decide (5 < 2 * 2) = false :=
  unsupported_fails 3 2 5 2 ⟨by decide⟩ (by decide) (by decide)

-- A score cap and a denominator cap alone permit an eligible unsupported score.
example : Batch 3 2 ∧ 2 ≤ 2 ∧ 3 ≤ 3 + 2 ∧ decide (3 < 2 * 2) = true := by
  exact ⟨⟨by decide⟩, by decide, by decide, by decide⟩

end AvailableChain.Gen.Pure.Tests.Batch

namespace AvailableChain.Gen.AC.Tests.Batch

open AvailableChain AvailableChain.GridCO AvailableChain.Gen.Pure

def child : Block := .node .genesis 1 (nodeRoot Block.genesis.root 1 0) 0
def head : Wire 1 := ⟨.seat 1 ⟨0, by decide⟩, .head child⟩

-- A stored child with one honest vote is covered from the eligible genesis anchor.
example :
    BatchBounds [child] [head] [head] [head] Finset.univ 1 0 child ∧
    Block.Preceq child (ghost .genesis [child] (goldfishScore [child] [head] [head])
      (fun B => decide (voterCount [head] < 2 * goldfishScore [child] [head] [head] B))) ∧
    decide (voterCount [head] < 2 * goldfishScore [child] [head] [head]
      (ghost .genesis [child] (goldfishScore [child] [head] [head])
        (fun B => decide
          (voterCount [head] < 2 * goldfishScore [child] [head] [head] B)))) = true := by
  apply batch_anchored [child] [head] [head] [head] Finset.univ 1 0 .genesis child
    (by simp) (by simp) (by decide) (by decide) (by decide) (by decide) ⟨by decide⟩
    (by change Block.compatible .genesis child = true; decide) ?_ (by decide)
  intro C hAC hCX
  have hne : C ≠ .genesis := by
    intro he
    subst C
    exact (by decide : ¬ Block.Prec .genesis .genesis) hAC
  have hCC : C = child := by
    cases C with
    | genesis => exact (hne rfl).elim
    | node P s r id =>
        change (decide (Block.node P s r id = child) ||
          Block.preceq (.node P s r id) .genesis) = true at hCX
        simpa [Block.preceq] using hCX
  simp [hCC]

-- A descendant anchor is permitted; its eligibility remains an explicit premise.
example :
    BatchBounds [child] [head] [head] [head] Finset.univ 1 0 .genesis ∧
    Block.Preceq .genesis (ghost child [child] (goldfishScore [child] [head] [head])
      (fun B => decide (voterCount [head] < 2 * goldfishScore [child] [head] [head] B))) ∧
    decide (voterCount [head] < 2 * goldfishScore [child] [head] [head]
      (ghost child [child] (goldfishScore [child] [head] [head])
        (fun B => decide
          (voterCount [head] < 2 * goldfishScore [child] [head] [head] B)))) = true := by
  apply batch_anchored [child] [head] [head] [head] Finset.univ 1 0 child .genesis
    (by simp) (by simp) (by decide) (by decide) (by decide) (by decide) ⟨by decide⟩
    (by change Block.compatible child .genesis = true; decide) ?_ (by decide)
  intro C hAC hCX
  have he : C = .genesis := of_decide_eq_true hCX
  subst C
  exact ((by decide : ¬ Block.Prec child .genesis) hAC).elim

end AvailableChain.Gen.AC.Tests.Batch
