module
public import AvailableChainGeneric.Statements.Pure.Stages
public import Mathlib.Data.List.Perm.Subperm

public section

namespace AvailableChain.Gen.Pure

/-- foldl_le_of_sublist proves the stated contract.
DC: DecoupledConsensusProofs/Bridge/FinalizedLive.lean:298–306 (nearest fold).
INTENTIONAL: Extract a pure preorder theorem; no DC sorted-stage contract.
S1:587–609; 21-healing.md:2233–2263. Consumers: HG.8a, F4.FF7, F5.H.11-Q. -/
theorem foldl_le_of_sublist : SublistStageFoldStatement := by
  rw [SublistStageFoldStatement_def]
  intro ι α _ f hmono hid xs ys hsub
  induction hsub with
  | slnil => intro u v huv; exact huv
  | cons i hsub ih =>
    intro u v huv
    exact ih u (f i v) (huv.trans (hid i v))
  | cons_cons i hsub ih =>
    intro u v huv
    exact ih (f i u) (f i v) (hmono i huv)

/-- foldl_le_finRange proves the stated contract.
DC: DecoupledConsensusProofs/Bridge/FinalizedLive.lean:298–306 (nearest fold).
INTENTIONAL: Extract a pure preorder theorem; no DC sorted-stage contract.
S1:587–609; 21-healing.md:2233–2263. Consumers: HG.8a, F4.FF7, F5.H.11-Q. -/
theorem foldl_le_finRange : OrderedStageFoldStatement := by
  rw [OrderedStageFoldStatement_def]
  intro α _ n f hmono hid vis hvis u₀
  have hsorted : vis.SortedLT := hvis.sortedLT
  have hsubset : vis ⊆ List.finRange n := by intro i _; simp
  have hsubperm : vis.Subperm (List.finRange n) := hsorted.nodup.subperm hsubset
  have hsub : vis.Sublist (List.finRange n) :=
    List.sublist_of_subperm_of_sortedLE hsubperm hsorted.sortedLE
      (List.sortedLT_finRange n).sortedLE
  exact foldl_le_of_sublist f hmono hid vis (List.finRange n) hsub u₀ u₀ (le_refl u₀)

/-- nat_foldl_le_finRange proves the stated contract.
DC: DecoupledConsensusProofs/Bridge/FinalizedLive.lean:298–306 (nearest fold).
INTENTIONAL: Extract a pure preorder theorem; no DC sorted-stage contract.
S1:587–609; 21-healing.md:2233–2263. Consumers: HG.8a, F4.FF7, F5.H.11-Q. -/
theorem nat_foldl_le_finRange : NatOrderedStageFoldStatement :=
  foldl_le_finRange (α := Nat)

/-- product_foldl_le_finRange proves the stated contract.
DC: DecoupledConsensusProofs/Bridge/FinalizedLive.lean:298–306 (nearest fold).
INTENTIONAL: Extract a pure preorder theorem; no DC sorted-stage contract.
S1:587–609; 21-healing.md:2233–2263. Consumers: HG.8a, F4.FF7, F5.H.11-Q. -/
theorem product_foldl_le_finRange : ProductOrderedStageFoldStatement :=
  foldl_le_finRange (α := Int × Int)

end AvailableChain.Gen.Pure
