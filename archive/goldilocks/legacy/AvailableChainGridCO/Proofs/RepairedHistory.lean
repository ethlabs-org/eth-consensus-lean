module
public import AvailableChainGridCO.Proofs.RecoveryPersistence

@[expose] public section
namespace AvailableChain.GridCO

/-- A repaired record stays sourced in the repaired raw history when
each step retains its value or takes the current raw result. -/
theorem repaired_record_source (result : Slot → Option Block) (record : Slot → Block)
    (valid : Slot → Prop) (down : ∀ s t, s ≤ t → valid t → valid s)
    (repair : Slot) (initial : result repair = some (record repair))
    (step : ∀ t, repair < t → valid t → record t = record (t - 1) ∨ result t = some (record t))
    (t : Slot) (start : repair ≤ t) (horizon : valid t) :
    ∃ s, repair ≤ s ∧ s ≤ t ∧ result s = some (record t) := by
  induction t with
  | zero =>
    have eq := Nat.le_zero.mp start
    subst repair
    exact ⟨0, le_refl _, le_refl _, initial⟩
  | succ t ih =>
    rcases Nat.eq_or_lt_of_le start with eq | lt
    · subst repair
      exact ⟨t + 1, le_refl _, le_refl _, initial⟩
    · rcases step (t + 1) lt horizon with old | raw
      · simp only [Nat.add_sub_cancel] at old
        rw [old]
        obtain ⟨s, lo, hi, source⟩ := ih (Nat.le_of_lt_succ lt)
          (down t (t + 1) (Nat.le_succ t) horizon)
        exact ⟨s, lo, hi.trans (Nat.le_succ t), source⟩
      · exact ⟨t + 1, start, le_refl _, raw⟩

/-- Ordered raw history makes all later repaired records monotone. -/
theorem repaired_record_prefix (result : Slot → Option Block) (record : Slot → Block)
    (valid : Slot → Prop) (down : ∀ s t, s ≤ t → valid t → valid s)
    (repair : Slot) (initial : result repair = some (record repair))
    (step : ∀ t, repair < t → valid t → record t = record (t - 1) ∨ result t = some (record t))
    (ordered : ∀ s t, repair ≤ s → s < t → valid t → ∀ B C,
      result s = some B → result t = some C → Block.Preceq B C)
    (r t : Slot) (start : repair ≤ r) (le : r ≤ t) (horizon : valid t) :
    Block.Preceq (record r) (record t) := by
  induction t with
  | zero => rw [Nat.le_zero.mp le]; exact block_preceq_self _
  | succ t ih =>
    rcases Nat.eq_or_lt_of_le le with eq | lt
    · subst r; exact block_preceq_self _
    · rcases step (t + 1) (start.trans_lt lt) horizon with old | raw
      · simp only [Nat.add_sub_cancel] at old
        rw [old]
        exact ih (Nat.le_of_lt_succ lt) (down t (t + 1) (Nat.le_succ t) horizon)
      · obtain ⟨s, lo, hi, source⟩ := repaired_record_source result record valid down repair
          initial step r start (down r (t + 1) le horizon)
        exact ordered s (t + 1) lo (hi.trans_lt lt) horizon _ _ source raw

end AvailableChain.GridCO
end
