module
public import AvailableChainGridCO.Proofs.ProposalDelivery

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Counts depend on the set of raw HEADs, not on list order or duplicates. -/
theorem voterCount_congr {n : Nat} (xs ys : List (Wire n))
    (h : ∀ o, o ∈ xs ↔ o ∈ ys) : voterCount xs = voterCount ys := by
  have hs : (seats n xs).toFinset = (seats n ys).toFinset := by
    ext i
    simp only [List.mem_toFinset, seats, List.mem_dedup, List.mem_filterMap]
    exact exists_congr (fun o => and_congr (h o) Iff.rfl)
  unfold voterCount
  have hx : (seats n xs).Nodup := List.nodup_dedup _
  have hy : (seats n ys).Nodup := List.nodup_dedup _
  rw [← List.toFinset_card_of_nodup hx, ← List.toFinset_card_of_nodup hy, hs]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Equivocation is also a set property; the two-copy test ignores repeats. -/
theorem equivocates_congr {n : Nat} (xs ys : List (Wire n))
    (h : ∀ o, o ∈ xs ↔ o ∈ ys) (i : Fin n) : equivocates xs i = equivocates ys i := by
  apply Bool.eq_iff_iff.mpr
  exact ⟨fun he => equivocates_mono xs ys i (fun o ho => (h o).mp ho) he,
    fun he => equivocates_mono ys xs i (fun o ho => (h o).mpr ho) he⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Ordinary scores agree when raw and support sets agree and all support
targets have the same membership in the two stores. Unrelated blocks can
differ; they do not contribute a support vote. -/
theorem goldfishScore_congr {n : Nat} (tree₁ tree₂ : List Block)
    (raw₁ raw₂ support₁ support₂ : List (Wire n))
    (hraw : ∀ o, o ∈ raw₁ ↔ o ∈ raw₂)
    (hsupport : ∀ o, o ∈ support₁ ↔ o ∈ support₂)
    (htree : ∀ o ∈ support₁, ∀ target, headTarget? o = some target →
      (target ∈ tree₁ ↔ target ∈ tree₂)) (B : Block) :
    goldfishScore tree₁ raw₁ support₁ B = goldfishScore tree₂ raw₂ support₂ B := by
  have hseats : (seats n raw₁).toFinset = (seats n raw₂).toFinset := by
    ext i
    simp only [List.mem_toFinset, seats, List.mem_dedup, List.mem_filterMap]
    exact exists_congr (fun o => and_congr (hraw o) Iff.rfl)
  have hany : ∀ i,
      (seatVotes support₁ i).any (fun o => match headTarget? o with
        | some target => target ∈ tree₁ && target.slot ≤ (headLabel? o).getD 0 &&
            Block.preceq B target
        | none => false) =
      (seatVotes support₂ i).any (fun o => match headTarget? o with
        | some target => target ∈ tree₂ && target.slot ≤ (headLabel? o).getD 0 &&
            Block.preceq B target
        | none => false) := by
    intro i
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, seatVotes, List.mem_filter]
    constructor
    · rintro ⟨o, ⟨ho, hi⟩, he⟩
      refine ⟨o, ⟨(hsupport o).mp ho, hi⟩, ?_⟩
      cases ht : headTarget? o with
      | none => simp [ht] at he
      | some target => simpa only [ht, htree o ho target ht] using he
    · rintro ⟨o, ⟨ho, hi⟩, he⟩
      have ho' := (hsupport o).mpr ho
      refine ⟨o, ⟨ho', hi⟩, ?_⟩
      cases ht : headTarget? o with
      | none => simp [ht] at he
      | some target => simpa only [ht, htree o ho' target ht] using he
  rw [goldfishScore_eq_card, goldfishScore_eq_card]
  congr 1
  ext i
  simp only [scoreSeats, Finset.mem_filter, hseats,
    equivocates_congr raw₁ raw₂ hraw i]
  apply and_congr Iff.rfl
  exact Iff.of_eq (congrArg (fun b : Bool => (equivocates raw₂ i || b) = true) (hany i))

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Set equality of the proposal merge discharges the arithmetic transport
premises. Complete support paths suffice for the score-store comparison. -/
theorem ProposalViewTransport.of_sets (p : Params) {n : Nat}
    (source reader : State n) (s : Slot) (B : Block)
    (htree : ∀ C ∈ voterTree p reader s, C = B ∨ C ∈ source.blocks)
    (hraw : ∀ o, o ∈ proposerView source s ↔ o ∈ voterView p reader s)
    (hsupport : ∀ o, o ∈ proposerSupportView source s ↔ o ∈ voterSupportView p reader s)
    (hknown : ∀ o ∈ proposerSupportView source s, ∀ target,
      headTarget? o = some target → target ∈ reader.blocks) :
    ProposalViewTransport p source reader s B := by
  refine ⟨htree, (voterCount_congr _ _ hraw).symm, ?_⟩
  intro C _ _
  symm
  apply goldfishScore_congr source.blocks reader.blocks _ _ _ _ hraw hsupport ?_ C
  intro o ho target ht
  have hm := (List.mem_filter.mp ho).2
  have hb : target ∈ source.blocks := by
    by_contra hn
    simp [resolvedHead?, ht, resolveTarget, resolutionTree, hn] at hm
  exact iff_of_true hb (hknown o ho target ht)

end AvailableChain.GridCO
end
