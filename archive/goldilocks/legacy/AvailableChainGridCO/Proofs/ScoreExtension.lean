module
public import AvailableChainGridCO.Proofs.Handling
public import AvailableChainGridCO.Proofs.Support

@[expose] public section
namespace AvailableChain.GridCO

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Seats counted by the ordinary walk, including equivocators. -/
def scoreSeats {n : Nat} (tree : List Block) (raw support : List (Wire n))
    (B : Block) : Finset (Fin n) :=
  (seats n raw).toFinset.filter (fun i =>
    equivocates raw i || (seatVotes support i).any (fun o =>
      match headTarget? o with
      | some target => target ∈ tree && target.slot ≤ (headLabel? o).getD 0 &&
          Block.preceq B target
      | none => false))

theorem goldfishScore_eq_card {n : Nat} (tree : List Block)
    (raw support : List (Wire n)) (B : Block) :
    goldfishScore tree raw support B = (scoreSeats tree raw support B).card := by
  rw [goldfishScore_block_eq]
  unfold scoreSeats
  rw [← List.toFinset_filter]
  exact (List.toFinset_card_of_nodup
    (List.Nodup.filter _ (List.nodup_dedup _))).symm


/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Relay can replace a raw key by two-target evidence for its seat.
Such replacement preserves the participant set. -/
theorem seats_eq_of_mem_or_equivocates {n : Nat} (xs ys : List (Wire n))
    (hsub : xs ⊆ ys)
    (hback : ∀ o ∈ ys, ∀ i, headSeat? o = some i →
      o ∈ xs ∨ equivocates xs i = true) :
    (seats n xs).toFinset = (seats n ys).toFinset := by
  ext i
  simp only [seats, List.mem_toFinset, List.mem_dedup, List.mem_filterMap]
  constructor
  · rintro ⟨o, ho, hi⟩
    exact ⟨o, hsub ho, hi⟩
  · rintro ⟨o, ho, hi⟩
    rcases hback o ho i hi with hm | he
    · exact ⟨o, hm, hi⟩
    · have hp : 0 < (seatVotes xs i).eraseDups.length := by
        have := of_decide_eq_true he
        omega
      obtain ⟨key, hk⟩ := List.length_pos_iff_exists_mem.mp hp
      obtain ⟨hm, hs⟩ := List.mem_filter.mp (List.mem_eraseDups.mp hk)
      exact ⟨key, hm, by simpa using hs⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Extra raw copies from a seat already known to equivocate cannot
change the equivocation test. -/
theorem equivocates_eq_of_mem_or_equivocates {n : Nat}
    (xs ys : List (Wire n)) (hsub : xs ⊆ ys)
    (hback : ∀ o ∈ ys, ∀ i, headSeat? o = some i →
      o ∈ xs ∨ equivocates xs i = true) (i : Fin n) :
    equivocates xs i = equivocates ys i := by
  cases he : equivocates xs i with
  | true => exact (equivocates_mono xs ys i hsub he).symm
  | false =>
    symm
    apply equivocates_false_of_unique
    intro a ha b hb
    have back (o : Wire n) (ho : o ∈ seatVotes ys i) :
        o ∈ seatVotes xs i := by
      obtain ⟨hm, hi⟩ := List.mem_filter.mp ho
      exact List.mem_filter.mpr ⟨(hback o hm i (by simpa using hi)).resolve_right
        (by simp [he]), hi⟩
    exact non_equivocating_unique xs i he a b (back a ha) (back b hb)

theorem voterCount_eq_of_mem_or_equivocates {n : Nat}
    (xs ys : List (Wire n)) (hsub : xs ⊆ ys)
    (hback : ∀ o ∈ ys, ∀ i, headSeat? o = some i →
      o ∈ xs ∨ equivocates xs i = true) :
    voterCount xs = voterCount ys := by
  unfold voterCount
  rw [← List.toFinset_card_of_nodup (show (seats n xs).Nodup from List.nodup_dedup _),
    ← List.toFinset_card_of_nodup (show (seats n ys).Nodup from List.nodup_dedup _),
    seats_eq_of_mem_or_equivocates xs ys hsub hback]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Common resolved support is needed only for non-equivocating seats.
This covers the different two-copy caches allowed by SA-PC relay. -/
theorem goldfishScore_eq_of_mem_or_equivocates {n : Nat}
    (tree₁ tree₂ : List Block) (raw₁ raw₂ support₁ support₂ : List (Wire n))
    (hraw : raw₁ ⊆ raw₂)
    (hback : ∀ o ∈ raw₂, ∀ i, headSeat? o = some i →
      o ∈ raw₁ ∨ equivocates raw₁ i = true)
    (hsupport : support₁ ⊆ support₂)
    (hsback : ∀ o ∈ support₂, ∀ i, headSeat? o = some i →
      o ∈ support₁ ∨ equivocates raw₁ i = true)
    (htree : ∀ o ∈ support₁, ∀ target, headTarget? o = some target →
      (target ∈ tree₁ ↔ target ∈ tree₂)) (b : Block) :
    goldfishScore tree₁ raw₁ support₁ b =
      goldfishScore tree₂ raw₂ support₂ b := by
  rw [goldfishScore_eq_card, goldfishScore_eq_card]
  congr 1
  ext i
  have he := equivocates_eq_of_mem_or_equivocates raw₁ raw₂ hraw hback i
  simp only [scoreSeats, Finset.mem_filter,
    seats_eq_of_mem_or_equivocates raw₁ raw₂ hraw hback, ← he]
  apply and_congr Iff.rfl
  cases hi : equivocates raw₁ i with
  | true => simp
  | false =>
    simp only [Bool.false_or, List.any_eq_true]
    constructor
    · rintro ⟨o, ho, ht⟩
      obtain ⟨hm, hs⟩ := List.mem_filter.mp ho
      refine ⟨o, List.mem_filter.mpr ⟨hsupport hm, hs⟩, ?_⟩
      cases hh : headTarget? o with
      | none => simp [hh] at ht
      | some target => simpa only [hh, htree o hm target hh] using ht
    · rintro ⟨o, ho, ht⟩
      obtain ⟨hm, hs⟩ := List.mem_filter.mp ho
      have hm' := (hsback o hm i (by simpa using hs)).resolve_right (by simp [hi])
      refine ⟨o, List.mem_filter.mpr ⟨hm', hs⟩, ?_⟩
      cases hh : headTarget? o with
      | none => simp [hh] at ht
      | some target => simpa only [hh, htree o hm' target hh] using ht

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A view extension can add copies only at seats that already equivocate.
This is the list-based form of DC's score-preserving proposal snapshot. -/
structure ScorePreservingViewExtension {n : Nat}
    (sourceRaw sourceSupport targetRaw targetSupport : List (Wire n)) : Prop where
  raw_subset : sourceRaw ⊆ targetRaw
  support_subset : sourceSupport ⊆ targetSupport
  raw_back : ∀ o ∈ targetRaw, ∀ i, headSeat? o = some i →
    o ∈ sourceRaw ∨ equivocates sourceRaw i = true
  support_back : ∀ o ∈ targetSupport, ∀ i, headSeat? o = some i →
    o ∈ sourceSupport ∨ equivocates sourceRaw i = true

namespace ScorePreservingViewExtension
variable {n : Nat} {A S A' S' : List (Wire n)}

theorem seats_eq (h : ScorePreservingViewExtension A S A' S') :
    (seats n A).toFinset = (seats n A').toFinset :=
  seats_eq_of_mem_or_equivocates A A' h.raw_subset h.raw_back

theorem equivocates_eq (h : ScorePreservingViewExtension A S A' S') (i : Fin n) :
    equivocates A i = equivocates A' i :=
  equivocates_eq_of_mem_or_equivocates A A' h.raw_subset h.raw_back i

theorem count_eq (h : ScorePreservingViewExtension A S A' S') :
    voterCount A = voterCount A' :=
  voterCount_eq_of_mem_or_equivocates A A' h.raw_subset h.raw_back

theorem score_eq (h : ScorePreservingViewExtension A S A' S')
    (tree tree' : List Block)
    (ht : ∀ o ∈ S, ∀ target, headTarget? o = some target →
      (target ∈ tree ↔ target ∈ tree')) (B : Block) :
    goldfishScore tree A S B = goldfishScore tree' A' S' B :=
  goldfishScore_eq_of_mem_or_equivocates tree tree' A A' S S'
    h.raw_subset h.raw_back h.support_subset h.support_back ht B

theorem eligible_eq (h : ScorePreservingViewExtension A S A' S')
    (tree tree' : List Block)
    (ht : ∀ o ∈ S, ∀ target, headTarget? o = some target →
      (target ∈ tree ↔ target ∈ tree')) (s : Slot) (B : Block) :
    goldfishEligible tree A S s B = goldfishEligible tree' A' S' s B := by
  simp only [goldfishEligible, h.score_eq tree tree' ht B, h.count_eq]

end ScorePreservingViewExtension

end AvailableChain.GridCO
end
