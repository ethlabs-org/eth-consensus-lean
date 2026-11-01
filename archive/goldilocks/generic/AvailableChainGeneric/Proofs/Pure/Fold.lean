module

public section

namespace AvailableChain.Gen.Pure

-- Source: AvailableChainSAPC/Proofs/ReceiptState.lean:10–15 (E-16).
/-- A fold preserves each field that its step preserves. -/
theorem fold_field {α β γ : Type} (f : α → γ) (step : α → β → α)
    (h : ∀ st x, f (step st x) = f st) (xs : List β) (st : α) :
    f (xs.foldl step st) = f st := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => exact (ih _).trans (h st x)

-- Source: AvailableChainFGSA/Proofs/StoreInv.lean:739–752 (E-16).
/-- A selector fold returns the initial value or a list member. -/
theorem foldl_select_mem {α : Type} (f : α → α → Bool) (l : List α) (init : α) :
    l.foldl (fun best b => if f best b then b else best) init = init ∨
      l.foldl (fun best b => if f best b then b else best) init ∈ l := by
  induction l generalizing init with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      split
      · rcases ih x with he | hm
        · exact Or.inr (by rw [he]; exact List.mem_cons_self)
        · exact Or.inr (List.mem_cons_of_mem _ hm)
      · rcases ih init with he | hm
        · exact Or.inl he
        · exact Or.inr (List.mem_cons_of_mem _ hm)

-- Source: AvailableChainFGSA/Proofs/StoreInv.lean:798–804 (E-16).
/-- Tests that agree on the list members give the same search result. -/
theorem find?_congr_mem {α : Type} {f g : α → Bool} (l : List α)
    (h : ∀ a ∈ l, f a = g a) : l.find? f = l.find? g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [List.find?_cons, List.find?_cons, h x List.mem_cons_self,
        ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]

end AvailableChain.Gen.Pure
