module
public import AvailableChainModel.Objects.Blocks
public import Mathlib.Tactic

@[expose] public section

namespace AvailableChain.FGSA

/-! Public ancestry lemmas on `Block`. The GridCO copies are `private`
(`GridCO/Proofs/Map.lean:25`, `Goldfish.lean:81`), so this file proves them
again. The proofs follow the FG versions in `AvailableChainKitFG/Ancestry.lean`. -/

/-- [helper] `B ⪯ B`. -/
theorem block_preceq_refl (B : Block) : Block.Preceq B B := by
  cases B <;> simp [Block.Preceq, Block.preceq]
/-- [helper] `⪯` is transitive. -/
theorem block_preceq_trans {A B C : Block} (h₁ : Block.Preceq A B) (h₂ : Block.Preceq B C) :
    Block.Preceq A C := by
  induction C with
  | genesis =>
      simp only [Block.Preceq, Block.preceq, decide_eq_true_eq] at h₂
      subst h₂
      exact h₁
  | node p s r_s r ih =>
      simp only [Block.Preceq, Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at h₂
      change Block.preceq A (Block.node p s r_s r) = true
      rcases h₂ with h | h
      · subst h
        exact h₁
      · have hAp : Block.preceq A p = true := ih h
        simp only [Block.preceq, hAp, Bool.or_true]
/-- [helper] `⪯` is antisymmetric. -/
theorem block_preceq_antisymm {A B : Block} (h₁ : Block.Preceq A B) (h₂ : Block.Preceq B A) :
    A = B := by
  have hle : ∀ {X Y : Block}, Block.Preceq X Y → X.depth ≤ Y.depth := by
    intro X Y h
    induction Y with
    | genesis =>
        simp only [Block.Preceq, Block.preceq, decide_eq_true_eq] at h
        subst h
        exact Nat.le_refl _
    | node p s r_s r ih =>
        simp only [Block.Preceq, Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at h
        rcases h with h | h
        · subst h
          exact Nat.le_refl _
        · have := ih h
          simp only [Block.depth]
          omega
  have heq : ∀ {X Y : Block}, Block.Preceq X Y → Y.depth ≤ X.depth → X = Y := by
    intro X Y h hd
    induction Y with
    | genesis =>
        simp only [Block.Preceq, Block.preceq, decide_eq_true_eq] at h
        exact h
    | node p s r_s r _ =>
        simp only [Block.Preceq, Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at h
        rcases h with h | h
        · exact h
        · exfalso
          have h1 := hle h
          simp only [Block.depth] at hd
          omega
  exact heq h₁ (hle h₂)
/-- [helper] Genesis precedes every block. -/
theorem block_genesis_preceq (B : Block) : Block.Preceq .genesis B := by
  induction B with
  | genesis => exact block_preceq_refl _
  | node p s r_s r ih =>
      simp only [Block.Preceq, Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at ih ⊢
      exact Or.inr ih
/-- [helper] Two ancestors of one block are comparable. -/
theorem block_preceq_total_of_common {A B W : Block} (hA : Block.Preceq A W)
    (hB : Block.Preceq B W) : Block.Preceq A B ∨ Block.Preceq B A := by
  induction W with
  | genesis =>
      simp only [Block.Preceq, Block.preceq, decide_eq_true_eq] at hA hB
      subst hA
      subst hB
      exact Or.inl (block_preceq_refl _)
  | node p s r_s r ih =>
      simp only [Block.Preceq, Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at hA hB
      rcases hA with hA | hA
      · rcases hB with hB | hB
        · subst hA; subst hB; exact Or.inl (block_preceq_refl _)
        · subst hA
          refine Or.inr ?_
          change Block.preceq B (Block.node p s r_s r) = true
          simp only [Block.preceq, hB, Bool.or_true]
      · rcases hB with hB | hB
        · subst hB
          refine Or.inl ?_
          change Block.preceq A (Block.node p s r_s r) = true
          simp only [Block.preceq, hA, Bool.or_true]
        · exact ih hA hB
/-- [helper] `compatible` is commutative. -/
theorem block_compatible_comm (A B : Block) : Block.compatible A B = Block.compatible B A := by
  unfold Block.compatible
  exact Bool.or_comm _ _
/-- [helper] Two blocks below one block are compatible. -/
theorem block_compatible_of_common {A B W : Block} (hA : Block.Preceq A W)
    (hB : Block.Preceq B W) : Block.Compatible A B := by
  unfold Block.Compatible Block.compatible
  simp only [Bool.or_eq_true]
  exact block_preceq_total_of_common hA hB
/-- [helper] bp01 §5 item 5: a block that conflicts with `X` conflicts with every
descendant of `X`. -/
theorem block_incompatible_of_preceq {b X Y : Block} (hbX : ¬ Block.Compatible b X)
    (hXY : Block.Preceq X Y) : ¬ Block.Compatible b Y := by
  intro hbY
  apply hbX
  unfold Block.Compatible Block.compatible at hbY
  simp only [Bool.or_eq_true] at hbY
  rcases hbY with hbY | hYb
  · exact block_compatible_of_common hbY hXY
  · have hXb := block_preceq_trans hXY hYb
    unfold Block.Compatible Block.compatible
    simp only [Bool.or_eq_true]
    exact Or.inr hXb
/-- [helper] If `A ⪯ C` and `C` is compatible with `F`, then `A` is compatible
with `F`. -/
theorem block_compatible_of_preceq_compatible {A C F : Block} (hAC : Block.Preceq A C)
    (hCF : Block.Compatible C F) : Block.Compatible A F := by
  unfold Block.Compatible Block.compatible at hCF
  simp only [Bool.or_eq_true] at hCF
  rcases hCF with hCF | hFC
  · have hAF := block_preceq_trans hAC hCF
    unfold Block.Compatible Block.compatible
    simp only [Bool.or_eq_true]
    exact Or.inl hAF
  · exact block_compatible_of_common hAC hFC

end AvailableChain.FGSA
end
