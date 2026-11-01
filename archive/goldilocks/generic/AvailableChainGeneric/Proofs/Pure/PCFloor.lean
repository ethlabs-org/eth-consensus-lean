module
public import AvailableChainGeneric.Statements.Pure.PCFloor
public import AvailableChainGeneric.Proofs.Pure.BlockOrder

public section

/-! Proofs for the PC output floor: the cases of `pcFloor`, the output extends
the PC target, the output extends `S` exactly when the target is compatible
with `S`, nesting below the output, and monotonicity. The block order lemmas
come from `Proofs/Pure/BlockOrder.lean`. -/

namespace AvailableChain.Gen.Pure

/-- `Block.Compatible` is comparability in `Block.Preceq`. -/
theorem block_compatible_iff_preceq_or (A B : Block) :
    Block.Compatible A B ↔ Block.Preceq A B ∨ Block.Preceq B A := by
  unfold Block.Compatible Block.compatible
  simp only [Bool.or_eq_true]
  rfl

theorem pcFloor_none (S : Block) : pcFloor S none = S := by
  rw [pcFloor_def]
  rfl

theorem pcFloor_some_of_preceq {S T : Block} (h : Block.Preceq T S) :
    pcFloor S (some T) = S := by
  rw [pcFloor_def]
  exact ite_eq_left h

theorem pcFloor_some_of_not_preceq {S T : Block} (h : ¬ Block.Preceq T S) :
    pcFloor S (some T) = T := by
  rw [pcFloor_def]
  exact ite_eq_right h

/-- With a held PC, the output is `S` or the PC target. -/
theorem pcFloor_some_eq_or (S T : Block) : pcFloor S (some T) = S ∨ pcFloor S (some T) = T := by
  by_cases h : Block.Preceq T S
  · exact Or.inl (pcFloor_some_of_preceq h)
  · exact Or.inr (pcFloor_some_of_not_preceq h)

/-- On a conflict between `S` and the PC target, the output is the PC target. -/
theorem pcFloor_some_of_not_compatible {S T : Block} (h : ¬ Block.Compatible T S) :
    pcFloor S (some T) = T := by
  apply pcFloor_some_of_not_preceq
  intro hTS
  exact h ((block_compatible_iff_preceq_or T S).mpr (Or.inl hTS))

theorem pcFloor_target_statement : PCFloorTargetStatement := by
  rw [PCFloorTargetStatement_def]
  intro S T
  by_cases h : Block.Preceq T S
  · rw [pcFloor_some_of_preceq h]
    exact h
  · rw [pcFloor_some_of_not_preceq h]
    exact block_preceq_refl T

/-- The output extends the held PC target. -/
theorem target_preceq_pcFloor (S T : Block) : Block.Preceq T (pcFloor S (some T)) :=
  pcFloor_target_statement S T

/-- A block below the PC target is below the output. -/
theorem preceq_pcFloor_of_preceq_target {X S T : Block} (h : Block.Preceq X T) :
    Block.Preceq X (pcFloor S (some T)) :=
  block_preceq_trans h (target_preceq_pcFloor S T)

/-- The output extends `S` exactly when the PC target is compatible with `S`. -/
theorem self_preceq_pcFloor_some_iff (S T : Block) :
    Block.Preceq S (pcFloor S (some T)) ↔ Block.Compatible T S := by
  rw [block_compatible_iff_preceq_or]
  by_cases h : Block.Preceq T S
  · rw [pcFloor_some_of_preceq h]
    exact ⟨fun _ => Or.inl h, fun _ => block_preceq_refl S⟩
  · rw [pcFloor_some_of_not_preceq h]
    constructor
    · exact Or.inr
    · rintro (hTS | hST)
      · exact absurd hTS h
      · exact hST

/-- The output extends `S` when every held PC target is compatible with `S`. -/
theorem self_preceq_pcFloor {S : Block} {target : Option Block}
    (h : ∀ T, target = some T → Block.Compatible T S) :
    Block.Preceq S (pcFloor S target) := by
  cases target with
  | none =>
      rw [pcFloor_none]
      exact block_preceq_refl S
  | some T => exact (self_preceq_pcFloor_some_iff S T).mpr (h T rfl)

theorem pcFloor_nest_statement : PCFloorNestStatement := by
  rw [PCFloorNestStatement_def]
  intro X S target hXS hX
  cases target with
  | none =>
      rw [pcFloor_none]
      exact hXS
  | some T =>
      by_cases h : Block.Preceq T S
      · rw [pcFloor_some_of_preceq h]
        exact hXS
      · rw [pcFloor_some_of_not_preceq h]
        rcases (block_compatible_iff_preceq_or X T).mp (hX T rfl) with hXT | hTX
        · exact hXT
        · exact absurd (block_preceq_trans hTX hXS) h

/-- A block below `S` and compatible with the held PC target is below the
output. -/
theorem preceq_pcFloor {X S : Block} {target : Option Block} (hXS : Block.Preceq X S)
    (hX : ∀ T, target = some T → Block.Compatible X T) :
    Block.Preceq X (pcFloor S target) :=
  pcFloor_nest_statement X S target hXS hX

theorem pcFloor_mono_statement : PCFloorMonoStatement := by
  rw [PCFloorMonoStatement_def]
  intro S S' target target' hS htarget hcompat
  have hS' : Block.Preceq S (pcFloor S' target') :=
    block_preceq_trans hS (self_preceq_pcFloor hcompat)
  cases target with
  | none =>
      rw [pcFloor_none]
      exact hS'
  | some T =>
      obtain ⟨T', hT', hTT'⟩ := htarget T rfl
      by_cases h : Block.Preceq T S
      · rw [pcFloor_some_of_preceq h]
        exact hS'
      · rw [pcFloor_some_of_not_preceq h, hT']
        exact preceq_pcFloor_of_preceq_target hTT'

/-- The output moves forward when `S` and the held PC target move forward and
the later target is compatible with the later `S`. -/
theorem pcFloor_mono {S S' : Block} {target target' : Option Block}
    (hS : Block.Preceq S S')
    (htarget : ∀ T, target = some T → ∃ T', target' = some T' ∧ Block.Preceq T T')
    (hcompat : ∀ T', target' = some T' → Block.Compatible T' S') :
    Block.Preceq (pcFloor S target) (pcFloor S' target') :=
  pcFloor_mono_statement S S' target target' hS htarget hcompat

/-- The two-PC form: `S ⪯ S'`, `T ⪯ T'` and `T'` compatible with `S'`. -/
theorem pcFloor_mono_some {S S' T T' : Block} (hS : Block.Preceq S S')
    (hT : Block.Preceq T T') (hcompat : Block.Compatible T' S') :
    Block.Preceq (pcFloor S (some T)) (pcFloor S' (some T')) :=
  pcFloor_mono hS (fun _ h => ⟨T', rfl, Option.some.inj h ▸ hT⟩)
    (fun _ h => Option.some.inj h ▸ hcompat)

end AvailableChain.Gen.Pure
