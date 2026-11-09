module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Entries

public section

/-! # Goldilocks FG store: the excluded entries of C1.1's scope, and held ancestry

The vocabulary of `FGStore/Cut` that its steps (`FGStore/CutSteps`) and their growing-fault
sibling read: the excluded entries of C1.1's scope (`excludedEntries`), and, at an honest node,
the state height of a held block (`one_le_h`), its held parent (`parent_held`) and ancestry
inside the run's blocks below a held block (`anc_of_U`). -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type}

/-- The excluded entries of C1.1's scope: conflicting with `B`, strictly above an honest `Σ.F`
at `Ts` (the state before the first cut of the run at a time `≥ Ts`). -/
def excludedEntries (H : Set (Fin P.n)) (U : Set (NodeBlock P ACP)) (tr : FGTrace P ACP)
    (Ts : Time) (B : NodeBlock P ACP) : Set (NodeBlock P ACP) :=
  {E | ¬ Compatible U E B ∧ ∃ z ∈ H, ∃ j, Ts ≤ tr.time j ∧ (∀ k < j, tr.time k < Ts) ∧
    Goldilocks.Anc U (tr.store z j).F E ∧ E ≠ (tr.store z j).F}

/-- Membership in `excludedEntries`. -/
theorem mem_excludedEntries {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}
    {Ts : Time} {B E : NodeBlock P ACP} : E ∈ excludedEntries H U tr Ts B ↔
      ¬ Compatible U E B ∧ ∃ z ∈ H, ∃ j, Ts ≤ tr.time j ∧ (∀ k < j, tr.time k < Ts) ∧
        Goldilocks.Anc U (tr.store z j).F E ∧ E ≠ (tr.store z j).F := Iff.rfl

/-! ## One block of the state transition -/

variable {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}

/-- The state of a held block has height at least `1`, above its justification. -/
theorem one_le_h (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {B : NodeBlock P ACP} (hB : B ∈ (tr.store y i).tree) :
    1 ≤ ((tr.store y i).σ B.root).h ∧
      ((tr.store y i).σ B.root).hj < ((tr.store y i).σ B.root).h := by
  obtain ⟨c, -, -, -, hc⟩ := chain_state_of_chain P ACP acp₀ _ (store_reachable hr hy i) B hB
  obtain ⟨h1, -, h2, -⟩ := FG.chain_invariants P.fg _ _ hc
  exact ⟨h1, h2⟩

/-- A held block that names a parent has its parent held. -/
theorem parent_held (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {B : NodeBlock P ACP} (hB : B ∈ (tr.store y i).tree) {r : Nat} (hp : B.parent = some r) :
    ∃ Y, ParentIn (tr.store y i).tree Y B := by
  rcases ((accepted_tree P ACP acp₀ _ (store_reachable hr hy i)).2.2.2 B hB).cases_tail with
    rfl | ⟨Y, -, hY⟩
  · exact absurd hp (by simp [Params.genesisBlock])
  · exact ⟨Y, hY⟩

/-- `U`-ancestry below a held block is ancestry in the tree. -/
theorem anc_of_U (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {A C : NodeBlock P ACP} (h : Goldilocks.Anc U A C) (hC : C ∈ (tr.store y i).tree) :
    (tr.store y i).Anc A C := by
  induction h with
  | refl => exact .refl
  | tail _ hYC ih =>
    obtain ⟨Z, hZ⟩ := parent_held hr hy hC hYC.2.2
    obtain rfl : Z = _ := hr.coherent.1 (hr.tree_subset y hy i hZ.1) hYC.1
      (Option.some.inj (hZ.2.2.symm.trans hYC.2.2))
    exact (ih hZ.1).tail hZ

end Consensus.Goldilocks.Store

end
