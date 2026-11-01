module
public import AvailableChainPCSAProofs.Proofs.Shared.Walk
public import AvailableChainPCSAProofs.Proofs.Foundations.Rank

public section

/-! The S-case root (pcsa34-r4.3 §5.5 step 3): a live lock on `A` in the
tree, with every lock and the view compatible with `A`, keeps the live root
and the HEAD `⪰ A`. -/

namespace AvailableChain.PCSA

open AvailableChain.SimplexFG Gen.Pure

/-- A compatible block at least as deep as `A` extends `A`. -/
theorem pcsa_preceq_of_compatible_depth {A R : Block} (hc : Block.Compatible A R)
    (hd : A.depth ≤ R.depth) : Block.Preceq A R := by
  rcases Bool.or_eq_true_iff.mp hc with h | h
  · exact h
  · rw [prefix_eq_of_depth R A h hd]
    exact block_preceq_refl _

/-- [pcsa34-r4.3 §5.5 step 3] The live root is `⪰ A` when every lock is
compatible with `A`, the view target is compatible with `A`, `Z` is genesis,
and a live lock on `A` is in the tree (or `A` is genesis). -/
theorem pcsa_liveRoot_above_lock (p : Params) (st : State p.n) (c : Option (PC p.n))
    (A : Block) (hZ : eraseFG (controls p st).Z = .genesis)
    (hlocks : ∀ row ∈ st.base.obligations, Block.Compatible row.1 A)
    (hview : ∀ v, c = some v → Block.Compatible v.target A)
    (hlock : A = .genesis ∨ ∃ row ∈ st.base.obligations, row.1 = A ∧ st.base.now < row.2.2)
    (htree : ∃ B ∈ fullTree p st, eraseFG B = A) :
    Block.Preceq A (liveRoot p st c) := by
  have hwc : Block.Compatible (walkBase p st c) A := by
    cases c with
    | none =>
      change Block.Compatible (eraseFG (controls p st).Z) A
      rw [hZ]
      exact block_compatible_of_common (block_genesis_preceq A) (block_preceq_refl A)
    | some v =>
      change Block.Compatible (if frameActive p st v then v.target else
        eraseFG (controls p st).Z) A
      split
      · exact hview v rfl
      · rw [hZ]
        exact block_compatible_of_common (block_genesis_preceq A) (block_preceq_refl A)
  by_cases hA : Block.Preceq A (walkBase p st c)
  · exact block_preceq_trans hA (pcsa_liveRoot_extends_base p st c)
  rcases hlock with rfl | ⟨row, hrow, hrA, hlive⟩
  · exact block_genesis_preceq _
  have hwA : Block.Preceq (walkBase p st c) A := by
    rcases Bool.or_eq_true_iff.mp hwc with h | h
    · exact h
    · exact absurd h hA
  have hdepth : (walkBase p st c).depth < A.depth := by
    rcases Nat.lt_or_eq_of_le (prefix_depth _ _ hwA) with h | h
    · exact h
    · exact absurd (prefix_eq_of_depth _ _ hwA (le_of_eq h.symm) ▸ block_preceq_refl A) hA
  have hmem : A ∈ walkLocks p st c := by
    refine (pcsa_walkLocks_mem p st c A).mpr ⟨row, hrow, hrA, hlive, htree, ?_, hdepth, ?_⟩
    · exact block_compatible_of_common (block_preceq_refl A) hwA
    · cases c with
      | none => rfl
      | some v =>
        change Block.compatible A v.target = true
        rw [block_compatible_comm]
        exact hview v rfl
  have hd := (pcsa_liveRoot_depth p st c).2 A hmem
  have hrc : Block.Compatible A (liveRoot p st c) := by
    rcases pcsa_liveRoot_origin p st c with he | hm
    · rw [he, Block.Compatible, block_compatible_comm]
      exact hwc
    · obtain ⟨row', hrow', hr', _⟩ := (pcsa_walkLocks_mem p st c _).mp hm
      rw [Block.Compatible, block_compatible_comm, ← hr']
      exact hlocks row' hrow'
  exact pcsa_preceq_of_compatible_depth hrc hd

/-- [pcsa34-r4.3 §5.5 step 3] The HEAD of a positive label extends the live
root of its view, so it is `⪰ A` under the lock facts. -/
theorem pcsa_headVote_above_lock (p : Params) (st : State p.n) (j : Slot) (hj : j ≠ 0)
    (A : Block) (hZ : eraseFG (controls p st).Z = .genesis)
    (hlocks : ∀ row ∈ st.base.obligations, Block.Compatible row.1 A)
    (hview : ∀ v ∈ pcSnapshotAt st (j - 1) ++ carriedPCs st j, Block.Compatible v.target A)
    (hlock : A = .genesis ∨ ∃ row ∈ st.base.obligations, row.1 = A ∧ st.base.now < row.2.2)
    (htree : ∃ B ∈ fullTree p st, eraseFG B = A) :
    Block.Preceq A (headVote p st j) := by
  delta headVote
  rw [ite_eq_right hj]
  refine block_preceq_trans (pcsa_liveRoot_above_lock p st _ A hZ hlocks ?_ hlock htree)
    (pcsa_headInTree_extends_root p st _ _ _ _)
  intro v hv
  exact hview v (List.mem_filter.mp (bestPC_mem _ v hv)).1

end AvailableChain.PCSA
end
