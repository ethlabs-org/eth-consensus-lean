module
public import AvailableChainPCSAProofs.Proofs.Foundations.Rank

public section

/-! C6 ViewRank: concrete receipt and count support. -/
namespace AvailableChain.PCSA
variable {n : Nat}
private theorem view_below_slot (A B : PC n) (h : pcBelow A B = true) : A.slot ≤ B.slot := by
  delta pcBelow at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact Nat.le_of_lt (of_decide_eq_true h)
  · exact Nat.le_of_eq (beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).1)
private theorem view_not_below_slot (A B : PC n) (h : ¬ pcBelow A B = true) : B.slot ≤ A.slot := by
  apply Nat.le_of_not_gt
  intro hh
  apply h
  exact Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true hh))
private theorem view_offer_slot (old : Option (PC n)) (C D : PC n)
    (hd : preferPC old C = some D) : C.slot ≤ D.slot := by
  cases old with
  | none => have he := Option.some.inj hd; subst D; exact le_refl _
  | some A =>
    change (if pcBelow A C then some C else some A) = some D at hd
    split at hd
    · have he := Option.some.inj hd; subst D; exact le_refl _
    · rename_i hn
      have he := Option.some.inj hd
      subst D
      exact view_not_below_slot A C hn
private theorem view_offer_keeps_slot (A C D : PC n)
    (hd : preferPC (some A) C = some D) : A.slot ≤ D.slot := by
  change (if pcBelow A C then some C else some A) = some D at hd
  split at hd
  · rename_i hh
    have he := Option.some.inj hd
    subst D
    exact view_below_slot A C hh
  · have he := Option.some.inj hd; subst D; exact le_refl _
private theorem view_fold_keeps_slot (cs : List (PC n)) (A : PC n) :
    ∃ D, cs.foldl preferPC (some A) = some D ∧ A.slot ≤ D.slot := by
  induction cs generalizing A with
  | nil => exact ⟨A, rfl, le_refl _⟩
  | cons C cs ih =>
    obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp (pcsa_preferPC_isSome (some A) C)
    obtain ⟨B, hB, hDB⟩ := ih D
    refine ⟨B, ?_, (view_offer_keeps_slot A C D hD).trans hDB⟩
    rw [List.foldl_cons, hD]
    exact hB
private theorem view_fold_member_slot (cs : List (PC n)) (C : PC n) (hc : C ∈ cs)
    (old : Option (PC n)) : ∃ D, cs.foldl preferPC old = some D ∧ C.slot ≤ D.slot := by
  induction cs generalizing old with
  | nil => exact (List.not_mem_nil hc).elim
  | cons A cs ih =>
    rcases List.mem_cons.mp hc with he | hm
    · subst A
      obtain ⟨B, hB⟩ := Option.isSome_iff_exists.mp (pcsa_preferPC_isSome old C)
      obtain ⟨D, hD, hBD⟩ := view_fold_keeps_slot cs B
      refine ⟨D, ?_, (view_offer_slot old C B hB).trans hBD⟩
      rw [List.foldl_cons, hB]
      exact hD
    · exact ih hm (preferPC old A)
/-- The selected PC has at least the slot of every source PC. -/
theorem pcsa_clean_bestPC_slot_ge (cs : List (PC n)) (C D : PC n)
    (hc : C ∈ cs) (hd : bestPC cs = some D) : C.slot ≤ D.slot := by
  obtain ⟨B, hb, hCB⟩ := view_fold_member_slot cs C hc none
  have he : B = D := Option.some.inj (hb.symm.trans hd)
  exact he ▸ hCB
/-- A source list containing a slot maximum selects its target when that slot has one target. -/
theorem pcsa_bestPC_target_of_max_slot (cs : List (PC n)) (C : PC n)
    (hc : C ∈ cs) (hmax : ∀ D ∈ cs, D.slot ≤ C.slot)
    (hunique : ∀ D ∈ cs, D.slot = C.slot → D.target = C.target) :
    ∃ D, bestPC cs = some D ∧ D.slot = C.slot ∧ D.target = C.target := by
  obtain ⟨D, hd, hlo⟩ := view_fold_member_slot cs C hc none
  have hm := bestPC_mem cs D hd
  have hs := Nat.le_antisymm (hmax D hm) hlo
  exact ⟨D, hd, hs, hunique D hm hs⟩
end AvailableChain.PCSA

namespace AvailableChain.PCSA
/-- A source member makes the selected PC nonempty. -/
theorem pcsa_bestPC_isSome_of_mem (cs : List (PC n)) (C : PC n) (hc : C ∈ cs) :
    (bestPC cs).isSome = true := by
  obtain ⟨D, hd, _⟩ := view_fold_member_slot cs C hc none
  have hb : bestPC cs = some D := hd
  rw [hb]
  rfl
end AvailableChain.PCSA

end
