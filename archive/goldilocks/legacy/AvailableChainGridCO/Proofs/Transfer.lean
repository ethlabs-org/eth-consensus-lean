module
public import AvailableChainGridCO.Proofs.ScoreExtension
public import AvailableChainGridCO.Proofs.Release

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Receipt conditions for one source result and one next ordinary view.
The source's clean supporters occur in the resolved view. A raw vote
relays back to the source's late pool, or that pool already contains
equivocation evidence. The support view is a raw subset. This follows
the two-copy cap in reference Goldfish `AdoptionTransport`. -/
structure TransferReceipts (p : Params) {n : Nat} (source : State n) (r : Slot)
    (tree : List Block) (raw support : List (Wire n)) (B : Block) : Prop where
  forward : ∀ o ∈ cleanSupport p source r,
    (∃ target, headTarget? o = some target ∧ Block.Preceq B target) →
      o ∈ support ∧ ∃ target, headTarget? o = some target ∧ target ∈ tree
  backward : ∀ o ∈ raw, ∀ i, headSeat? o = some i →
    o ∈ lateVotes p source r ∨ equivocates (lateVotes p source r) i = true
  support_raw : ∀ o ∈ support, o ∈ raw

private theorem no_equivocation_of_unique {n : Nat} (raw : List (Wire n))
    (i : Fin n) (o : Wire n)
    (h : ∀ q ∈ raw, headSeat? q = some i → q = o) : equivocates raw i = false := by
  have hc : (seatVotes raw i).toFinset.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha, hai⟩ := List.mem_filter.mp (List.mem_toFinset.mp ha)
    obtain ⟨hb, hbi⟩ := List.mem_filter.mp (List.mem_toFinset.mp hb)
    exact (h a ha (by simpa using hai)).trans (h b hb (by simpa using hbi)).symm
  have he : (seatVotes raw i).eraseDups.toFinset = (seatVotes raw i).toFinset := by
    ext q; simp
  have hl : (seatVotes raw i).eraseDups.length ≤ 1 := by
    rw [← List.toFinset_card_of_nodup (eraseDups_nodup _), he]
    exact hc
  exact decide_eq_false (by omega)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A source supporter is the only raw vote for its seat in the next view.
This also excludes an equivocation that could score on all branches. -/
theorem TransferReceipts.seat_unique {p : Params} {n : Nat} {source : State n}
    {r : Slot} {tree : List Block} {raw support : List (Wire n)} {B : Block}
    (h : TransferReceipts p source r tree raw support B)
    (i : Fin n) (o : Wire n) (ho : o ∈ cleanSupport p source r)
    (hi : headSeat? o = some i) :
    ∀ q ∈ raw, headSeat? q = some i → q = o := by
  intro q hq hqi
  rcases h.backward q hq i hqi with hl | he
  · exact (cleanSupport_eq_of_late_same_seat p source r i o q ho hl hi hqi).symm
  · have hno := no_equivocation_of_unique (lateVotes p source r) i o (by
      intro u hu hui
      exact (cleanSupport_eq_of_late_same_seat p source r i o u ho hu hi hui).symm)
    simp [hno] at he

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every genuine prefix supporter scores for that prefix in the next view. -/
theorem TransferReceipts.supporters_subset {p : Params} {n : Nat} {source : State n}
    {r : Slot} {tree : List Block} {raw support : List (Wire n)} {B : Block}
    (h : TransferReceipts p source r tree raw support B) :
    prefixSupportSeats p source r B ⊆ scoreSeats tree raw support B := by
  intro i hi
  obtain ⟨o, ho, hseat, target, ht, hp⟩ := prefixSupportSeats_witness p source r B i hi
  obtain ⟨hm, target', ht', htree⟩ := h.forward o ho ⟨target, ht, hp⟩
  have he : target' = target := Option.some.inj (ht'.symm.trans ht)
  subst target'
  have hres := (List.mem_filter.mp (List.mem_filter.mp ho).1).2
  simp only [resolvedBefore_block, ht, Bool.and_eq_true, decide_eq_true_eq] at hres
  apply Finset.mem_filter.mpr
  refine ⟨List.mem_toFinset.mpr (List.mem_dedup.mpr
    (List.mem_filterMap.mpr ⟨o, h.support_raw o hm, hseat⟩)), ?_⟩
  apply Bool.or_eq_true_iff.mpr
  apply Or.inr
  apply List.any_eq_true.mpr
  exact ⟨o, List.mem_filter.mpr ⟨hm, by simp [hseat]⟩,
    by simpa [ht, htree, hres.1.1.2] using! hp⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A source supporter cannot score on a conflicting branch, including
through another proposal's declared support subset. -/
theorem TransferReceipts.conflict_disjoint {p : Params} {n : Nat} {source : State n}
    {r : Slot} {tree : List Block} {raw support : List (Wire n)} {B : Block}
    (h : TransferReceipts p source r tree raw support B) (C : Block)
    (hc : Block.compatible B C = false) :
    Disjoint (prefixSupportSeats p source r B) (scoreSeats tree raw support C) := by
  apply Finset.disjoint_left.mpr
  intro i hi hci
  obtain ⟨o, ho, hseat, target, ht, hp⟩ := prefixSupportSeats_witness p source r B i hi
  have hno := no_equivocation_of_unique raw i o (h.seat_unique i o ho hseat)
  have hh := (Finset.mem_filter.mp hci).2
  simp only [hno, Bool.false_or] at hh
  obtain ⟨q, hq, hqt⟩ := List.any_eq_true.mp hh
  obtain ⟨hq, hqi⟩ := List.mem_filter.mp hq
  have he := h.seat_unique i o ho hseat q (h.support_raw q hq) (by simpa using hqi)
  subst q
  simp only [ht, Bool.and_eq_true, decide_eq_true_eq] at hqt
  have hcomp := ancestors_compatible B C target hp hqt.2
  change Block.compatible B C = true at hcomp
  rw [hc] at hcomp
  contradiction

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Reverse relay bounds the next view's participant denominator. -/
theorem TransferReceipts.participants_subset {p : Params} {n : Nat} {source : State n}
    {r : Slot} {tree : List Block} {raw support : List (Wire n)} {B : Block}
    (h : TransferReceipts p source r tree raw support B) :
    (seats n raw).toFinset ⊆ lateSeats p source r := by
  intro i hi
  obtain ⟨o, ho, hi⟩ := List.mem_filterMap.mp (List.mem_dedup.mp (List.mem_toFinset.mp hi))
  rcases h.backward o ho i hi with hm | he
  · exact List.mem_toFinset.mpr (List.mem_dedup.mpr
      (List.mem_filterMap.mpr ⟨o, hm, hi⟩))
  · have hpos : 0 < (seatVotes (lateVotes p source r) i).eraseDups.length := by
      have : 2 ≤ (seatVotes (lateVotes p source r) i).eraseDups.length :=
        of_decide_eq_true he
      omega
    obtain ⟨q, hq⟩ := List.length_pos_iff_exists_mem.mp hpos
    obtain ⟨hq, hqi⟩ := List.mem_filter.mp (List.mem_eraseDups.mp hq)
    exact List.mem_toFinset.mpr (List.mem_dedup.mpr
      (List.mem_filterMap.mpr ⟨q, hq, by simpa using hqi⟩))

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The ordinary score of a conflicting branch and the genuine source
support fit together in the source's late denominator. -/
theorem TransferReceipts.conflicting_score_bound {p : Params} {n : Nat} {source : State n}
    {r : Slot} {tree : List Block} {raw support : List (Wire n)} {B : Block}
    (h : TransferReceipts p source r tree raw support B) (C : Block)
    (hc : Block.compatible B C = false) :
    prefixSupport p source r B + goldfishScore tree raw support C ≤
      voterCount (lateVotes p source r) := by
  rw [prefixSupport_eq_card, goldfishScore_eq_card, ← lateSeats_card,
    ← Finset.card_union_of_disjoint (h.conflict_disjoint C hc)]
  apply Finset.card_le_card
  exact Finset.union_subset (prefixSupportSeats_subset_late p source r B)
    (Finset.Subset.trans (Finset.filter_subset _ _) h.participants_subset)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A genuine source majority is eligible in the next ordinary view and
strictly beats every conflicting branch. This includes current-slot rivals. -/
theorem TransferReceipts.majority {p : Params} {n : Nat} {source : State n}
    {r : Slot} {tree : List Block} {raw support : List (Wire n)} {B : Block}
    (h : TransferReceipts p source r tree raw support B)
    (hm : voterCount (lateVotes p source r) < 2 * prefixSupport p source r B) :
    voterCount raw < 2 * goldfishScore tree raw support B ∧
      ∀ C, Block.compatible B C = false →
        goldfishScore tree raw support C < goldfishScore tree raw support B := by
  have hsupport : prefixSupport p source r B ≤ goldfishScore tree raw support B := by
    rw [prefixSupport_eq_card, goldfishScore_eq_card]
    exact Finset.card_le_card h.supporters_subset
  have hcount : voterCount raw ≤ voterCount (lateVotes p source r) := by
    rw [← lateSeats_card]
    change (seats n raw).length ≤ _
    rw [← List.toFinset_card_of_nodup (show (seats n raw).Nodup from List.nodup_dedup _)]
    exact Finset.card_le_card h.participants_subset
  refine ⟨by omega, ?_⟩
  intro C hc
  have := h.conflicting_score_bound C hc
  omega

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Ordinary scores increase towards ancestors, also for equivocators. -/
theorem goldfishScore_prefix_mono {n : Nat} (tree : List Block)
    (raw support : List (Wire n)) (B C : Block) (hp : Block.Preceq B C) :
    goldfishScore tree raw support C ≤ goldfishScore tree raw support B := by
  rw [goldfishScore_eq_card, goldfishScore_eq_card]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi, hs⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨hi, ?_⟩
  rcases Bool.or_eq_true_iff.mp hs with he | hs
  · exact Bool.or_eq_true_iff.mpr (Or.inl he)
  · apply Bool.or_eq_true_iff.mpr
    apply Or.inr
    obtain ⟨o, ho, ht⟩ := List.any_eq_true.mp hs
    refine List.any_eq_true.mpr ⟨o, ho, ?_⟩
    cases htarg : headTarget? o with
    | none => simp [htarg] at ht
    | some target =>
        simp only [htarg, Bool.and_eq_true, decide_eq_true_eq] at ht ⊢
        exact ⟨ht.1, prefix_trans B C target hp ht.2⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The transferred majority drives the executable walk through the
source prefix from every compatible root. Only receipts and a stored
voter path remain to be supplied by the run. -/
theorem forkChoice_covers_of_transfer {n : Nat} (p : Params) (source st : State n)
    (r current : Slot) (tree : List Block) (raw support : List (Wire n))
    (B C : Block) (hc : confirmation p source r = some C) (hp : Block.Preceq B C)
    (h : TransferReceipts p source r st.blocks raw support B)
    (hroot : Block.Compatible (liveRoot st) B)
    (hpath : ∀ A, A ≠ .genesis → Block.Preceq A B → A ∈ tree) :
    Block.Preceq B (forkChoice st tree raw support current) := by
  have hm : voterCount (lateVotes p source r) < 2 * prefixSupport p source r B := by
    have hc := confirmation_majority p source r C hc
    have hp := prefixSupport_mono p source r B C hp
    omega
  obtain ⟨helig, hdom⟩ := h.majority hm
  apply forkChoice_covers_of_path_dominance st tree raw support current B hroot hpath
  · intro A _ hA
    have hle := goldfishScore_prefix_mono st.blocks raw support A B hA
    apply Bool.or_eq_true_iff.mpr
    exact Or.inr (decide_eq_true (by omega))
  · intro A _ hA D _ hparent _ hne
    have hd := conflict_mono_descendant A B D hA (siblings_incompatible D A hparent hne)
    have hd' : Block.compatible B D = false := by
      simpa [Block.compatible, Bool.or_comm] using hd
    have hlt := hdom D hd'
    have hle := goldfishScore_prefix_mono st.blocks raw support A B hA
    omega

end AvailableChain.GridCO
end
