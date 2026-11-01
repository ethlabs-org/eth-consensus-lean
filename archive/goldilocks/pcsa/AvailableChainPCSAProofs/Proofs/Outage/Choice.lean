module
public import AvailableChainPCSAProofs.Proofs.Foundations.Rank

public section

/-! The slot bound of the max-rank PC choice (pcsa34-r4.3 §5.4.1 step 1: the
view has rank at least that of every source). -/

namespace AvailableChain.PCSA

variable {n : Nat}

/-- One preference step keeps a PC whose slot bounds the old choice and the candidate. -/
theorem pcsa_preferPC_slot (old : Option (PC n)) (d : PC n) :
    ∃ c, preferPC old d = some c ∧ d.slot ≤ c.slot ∧
      ∀ c₀, old = some c₀ → c₀.slot ≤ c.slot := by
  cases old with
  | none => exact ⟨d, rfl, le_rfl, fun c₀ h => absurd h (by simp)⟩
  | some prev =>
    by_cases hb : pcBelow prev d = true
    · refine ⟨d, ?_, le_rfl, ?_⟩
      · change (if pcBelow prev d then some d else some prev) = some d
        rw [ite_eq_left hb]
      · intro c₀ h
        cases Option.some.inj h
        change (decide (prev.slot < d.slot) || _) = true at hb
        rcases Bool.or_eq_true_iff.mp hb with h1 | h1
        · exact le_of_lt (of_decide_eq_true h1)
        · exact le_of_eq (beq_iff_eq.mp (Bool.and_eq_true_iff.mp h1).1)
    · refine ⟨prev, ?_, ?_, fun c₀ h => le_of_eq (by cases Option.some.inj h; rfl)⟩
      · change (if pcBelow prev d then some d else some prev) = some prev
        rw [ite_eq_right hb]
      · by_contra hlt
        apply hb
        change (decide (prev.slot < d.slot) || _) = true
        rw [decide_eq_true (Nat.lt_of_not_le hlt), Bool.true_or]

/-- The max-rank choice of a list has a slot at least that of every member. -/
theorem pcsa_bestPC_slot_ge (cs : List (PC n)) (d : PC n) (hd : d ∈ cs) :
    ∃ c, bestPC cs = some c ∧ d.slot ≤ c.slot := by
  have key : ∀ (cs : List (PC n)) (old : Option (PC n)),
      (∀ c₀, old = some c₀ → ∃ c, cs.foldl preferPC old = some c ∧ c₀.slot ≤ c.slot) ∧
      ∀ d ∈ cs, ∃ c, cs.foldl preferPC old = some c ∧ d.slot ≤ c.slot := by
    intro cs
    induction cs with
    | nil =>
      intro old
      exact ⟨fun c₀ h => ⟨c₀, h, le_rfl⟩, fun d hd => absurd hd (by simp)⟩
    | cons a as ih =>
      intro old
      obtain ⟨c', hc', ha, hold⟩ := pcsa_preferPC_slot old a
      obtain ⟨ih1, ih2⟩ := ih (preferPC old a)
      rw [List.foldl_cons]
      refine ⟨fun c₀ h => ?_, fun d hd => ?_⟩
      · obtain ⟨c, hc, hle⟩ := ih1 c' hc'
        exact ⟨c, hc, le_trans (hold c₀ h) hle⟩
      · rcases List.mem_cons.mp hd with rfl | hd
        · obtain ⟨c, hc, hle⟩ := ih1 c' hc'
          exact ⟨c, hc, le_trans ha hle⟩
        · exact ih2 d hd
  exact (key cs none).2 d hd

end AvailableChain.PCSA
end
