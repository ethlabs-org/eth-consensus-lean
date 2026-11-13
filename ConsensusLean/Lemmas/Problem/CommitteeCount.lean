module
public import ConsensusLean.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.Card

public section

/-! # Committee counting

Population-free count arithmetic over a committee `K : Finset V`, for the committee forms of the
AC fault counts. Each lemma has a `Finset` form (`card`) and, where the counted sets are sets of
validators as in the existing `ncard` counts, a `Set` form (`ncard` of `↑K ∩ S`); the committee
size is always `K.card`.

* A strict majority of one of two disjoint sets inside `K` bounds the other below half of `K`
  (`two_mul_card_inter_lt`, `two_mul_ncard_inter_lt`); with a joined set inside the honest set
  and the faulty set its complement this is the partition count (`two_mul_ncard_inter_compl_lt`).
* The half bound passes to smaller fault sets (`two_mul_card_inter_lt_of_subset`,
  `two_mul_ncard_inter_lt_of_subset`) and to every subset of the faulty committee members, so
  such a subset is no half and no three-quarter quorum of `K`
  (`two_mul_card_lt_of_subset_inter`, `not_card_le_two_mul_of_subset_inter`,
  `not_three_mul_card_le_of_subset_inter` and their `ncard` forms).
* A strict majority passes to a smaller opposing set and a larger supporting set
  (`card_inter_lt_card_inter_of_subset`, `ncard_inter_lt_ncard_inter_of_subset`).
* A three-quarter quorum of `K` among the faulty members plus one, with fewer than half faulty,
  makes `K` a singleton whose member is not faulty (`card_eq_one_of_subset_union_singleton`,
  `ncard_eq_one_of_subset_union_singleton`, `not_mem_of_card_eq_one`, `eq_of_mem_of_card_eq_one`).
* Committee forms of the counts that read the validator universe `Fin n`: a set of committee
  members has at most `K.card` elements (`ncard_le_card_of_subset_coe`); two three-quarter
  quorums of `K` overlap in more than its faulty members, so in a non-faulty member
  (`ncard_inter_lt_ncard_inter_of_quorums`, `exists_mem_inter_not_mem_of_quorums`); the
  equivocators and the voters outside a three-quarter quorum are fewer than the quorum
  (`ncard_add_ncard_sdiff_lt`); the singleton committee of a quorum inside the faulty members and
  one more validator, with a non-faulty member in the quorum equal to every member
  (`singleton_of_quorum_subset_union_singleton` and its `ncard` form).
* At the full committee `K = univ` the committee counts are the population counts
  (`ncard_coe_univ_inter`, `two_mul_ncard_inter_univ_lt_iff`), and the two committee fault
  premises that replace one population fault premise both reduce to it
  (`two_mul_ncard_inter_lt_pair_of_univ`).
-/

namespace Consensus

/-! ## Arithmetic -/

/-- `3c ≤ 4(f + 1)` and `2f < c` leave `c = 1`. -/
theorem eq_one_of_three_mul_le {c f : Nat} (h3 : 3 * c ≤ 4 * (f + 1)) (h2 : 2 * f < c) :
    c = 1 := by
  omega

/-! ## `Finset` counts -/

section Finset

variable {V : Type*} [DecidableEq V]

/-- Two disjoint sets meet the committee in at most its size together. -/
theorem card_inter_add_card_inter_le (K : Finset V) {A B : Finset V} (hd : Disjoint A B) :
    (K ∩ A).card + (K ∩ B).card ≤ K.card := by
  have hd' : Disjoint (K ∩ A) (K ∩ B) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hd)
  have h1 : (K ∩ A ∪ K ∩ B).card = (K ∩ A).card + (K ∩ B).card :=
    Finset.card_union_of_disjoint hd'
  have h2 : (K ∩ A ∪ K ∩ B).card ≤ K.card :=
    Finset.card_le_card (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
  omega

/-- **CO ⇒ CO2, CS ⇒ CS2.** Fewer committee members in `B` than in a disjoint `A` are fewer
than half of the committee. -/
theorem two_mul_card_inter_lt (K : Finset V) {A B : Finset V} (hd : Disjoint A B)
    (h : (K ∩ B).card < (K ∩ A).card) : 2 * (K ∩ B).card < K.card := by
  have := card_inter_add_card_inter_le K hd
  omega

/-- The half bound passes to a smaller set (faults only grow). -/
theorem two_mul_card_inter_lt_of_subset (K : Finset V) {F F' : Finset V} (hF : F' ⊆ F)
    (h : 2 * (K ∩ F).card < K.card) : 2 * (K ∩ F').card < K.card := by
  have hs : K ∩ F' ⊆ K ∩ F := fun x hx =>
    Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hx).1, hF (Finset.mem_inter.1 hx).2⟩
  have := Finset.card_le_card hs
  omega

/-- A strict committee majority passes to a smaller opposing set and a larger supporting set. -/
theorem card_inter_lt_card_inter_of_subset (K : Finset V) {A B Q T : Finset V} (hQ : Q ⊆ B)
    (hT : A ⊆ T) (h : (K ∩ B).card < (K ∩ A).card) : (K ∩ Q).card < (K ∩ T).card := by
  have hq : K ∩ Q ⊆ K ∩ B := fun x hx =>
    Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hx).1, hQ (Finset.mem_inter.1 hx).2⟩
  have ht : K ∩ A ⊆ K ∩ T := fun x hx =>
    Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hx).1, hT (Finset.mem_inter.1 hx).2⟩
  have := Finset.card_le_card hq
  have := Finset.card_le_card ht
  omega

/-- A set of committee members in `B` is below half of the committee when `K ∩ B` is. -/
theorem two_mul_card_lt_of_subset_inter (K : Finset V) {B S : Finset V} (hS : S ⊆ K ∩ B)
    (h : 2 * (K ∩ B).card < K.card) : 2 * S.card < K.card := by
  have := Finset.card_le_card hS
  omega

/-- A set of committee members in `B` is no half of the committee when `K ∩ B` is below half. -/
theorem not_card_le_two_mul_of_subset_inter (K : Finset V) {B S : Finset V} (hS : S ⊆ K ∩ B)
    (h : 2 * (K ∩ B).card < K.card) : ¬ K.card ≤ 2 * S.card := by
  have := two_mul_card_lt_of_subset_inter K hS h
  omega

/-- A set of committee members in `B` is no three-quarter quorum of the committee when `K ∩ B`
is below half. -/
theorem not_three_mul_card_le_of_subset_inter (K : Finset V) {B S : Finset V}
    (hS : S ⊆ K ∩ B) (h : 2 * (K ∩ B).card < K.card) : ¬ 3 * K.card ≤ 4 * S.card := by
  have := two_mul_card_lt_of_subset_inter K hS h
  omega

/-- **R21.** A three-quarter quorum of the committee inside its faulty members and one more
validator, with fewer than half of the committee faulty, makes the committee a singleton. -/
theorem card_eq_one_of_subset_union_singleton (K : Finset V) {F O : Finset V} {p : V}
    (hO : O ⊆ (K ∩ F) ∪ {p}) (h3 : 3 * K.card ≤ 4 * O.card)
    (h2 : 2 * (K ∩ F).card < K.card) : K.card = 1 := by
  have h4 := Finset.card_le_card hO
  have h5 := Finset.card_union_le (K ∩ F) {p}
  have h6 := Finset.card_singleton p
  exact eq_one_of_three_mul_le (f := (K ∩ F).card) (by omega) h2

/-- In a singleton committee with fewer than half faulty, every member is not faulty. -/
theorem not_mem_of_card_eq_one {K F : Finset V} (h1 : K.card = 1)
    (h2 : 2 * (K ∩ F).card < K.card) {u : V} (hu : u ∈ K) : u ∉ F := fun hF => by
  have := Finset.card_pos.mpr ⟨u, Finset.mem_inter.2 ⟨hu, hF⟩⟩
  omega

end Finset

/-! ## `Set` counts -/

section Set

variable {V : Type*}

/-- Any two members of a singleton committee are equal. -/
theorem eq_of_mem_of_card_eq_one {K : Finset V} (h : K.card = 1) {u y : V} (hu : u ∈ K)
    (hy : y ∈ K) : u = y :=
  Finset.card_le_one.mp h.le u hu y hy

/-- Two disjoint sets meet the committee in at most its size together. -/
theorem ncard_inter_add_ncard_inter_le (K : Finset V) {A B : Set V} (hd : Disjoint A B) :
    ((K : Set V) ∩ A).ncard + ((K : Set V) ∩ B).ncard ≤ K.card := by
  have hd' : Disjoint ((K : Set V) ∩ A) ((K : Set V) ∩ B) :=
    Set.disjoint_of_subset Set.inter_subset_right Set.inter_subset_right hd
  have h1 : ((K : Set V) ∩ A ∪ (K : Set V) ∩ B).ncard =
      ((K : Set V) ∩ A).ncard + ((K : Set V) ∩ B).ncard :=
    Set.ncard_union_eq hd' (K.finite_toSet.inter_of_left A) (K.finite_toSet.inter_of_left B)
  have h2 : ((K : Set V) ∩ A ∪ (K : Set V) ∩ B).ncard ≤ (K : Set V).ncard :=
    Set.ncard_le_ncard (Set.union_subset Set.inter_subset_left Set.inter_subset_left)
      K.finite_toSet
  have h3 := Set.ncard_coe_finset K
  omega

/-- **CO ⇒ CO2, CS ⇒ CS2** (`ncard` form). -/
theorem two_mul_ncard_inter_lt (K : Finset V) {A B : Set V} (hd : Disjoint A B)
    (h : ((K : Set V) ∩ B).ncard < ((K : Set V) ∩ A).ncard) :
    2 * ((K : Set V) ∩ B).ncard < K.card := by
  have := ncard_inter_add_ncard_inter_le K hd
  omega

/-- **CS ⇒ CS2**, the partition count restricted to the committee: fewer faulty committee members
than honest joined ones are fewer than half of the committee. -/
theorem two_mul_ncard_inter_compl_lt (K : Finset V) {H J : Set V} (hJ : J ⊆ H)
    (h : ((K : Set V) ∩ Hᶜ).ncard < ((K : Set V) ∩ J).ncard) :
    2 * ((K : Set V) ∩ Hᶜ).ncard < K.card :=
  two_mul_ncard_inter_lt K (Set.disjoint_of_subset_left hJ disjoint_compl_right) h

/-- The half bound passes to a smaller set (`ncard` form). -/
theorem two_mul_ncard_inter_lt_of_subset (K : Finset V) {F F' : Set V} (hF : F' ⊆ F)
    (h : 2 * ((K : Set V) ∩ F).ncard < K.card) : 2 * ((K : Set V) ∩ F').ncard < K.card := by
  have hs : (K : Set V) ∩ F' ⊆ (K : Set V) ∩ F := fun _ hx => ⟨hx.1, hF hx.2⟩
  have := Set.ncard_le_ncard hs (K.finite_toSet.inter_of_left F)
  omega

/-- A strict committee majority passes to a smaller opposing set and a larger supporting set
(`ncard` form). -/
theorem ncard_inter_lt_ncard_inter_of_subset (K : Finset V) {A B Q T : Set V} (hQ : Q ⊆ B)
    (hT : A ⊆ T) (h : ((K : Set V) ∩ B).ncard < ((K : Set V) ∩ A).ncard) :
    ((K : Set V) ∩ Q).ncard < ((K : Set V) ∩ T).ncard := by
  have hq : (K : Set V) ∩ Q ⊆ (K : Set V) ∩ B := fun _ hx => ⟨hx.1, hQ hx.2⟩
  have ht : (K : Set V) ∩ A ⊆ (K : Set V) ∩ T := fun _ hx => ⟨hx.1, hT hx.2⟩
  have := Set.ncard_le_ncard hq (K.finite_toSet.inter_of_left B)
  have := Set.ncard_le_ncard ht (K.finite_toSet.inter_of_left T)
  omega

/-- A set of committee members in `B` is below half of the committee (`ncard` form). -/
theorem two_mul_ncard_lt_of_subset_inter (K : Finset V) {B S : Set V}
    (hS : S ⊆ (K : Set V) ∩ B) (h : 2 * ((K : Set V) ∩ B).ncard < K.card) :
    2 * S.ncard < K.card := by
  have := Set.ncard_le_ncard hS (K.finite_toSet.inter_of_left B)
  omega

/-- A set of committee members in `B` is no half of the committee (`ncard` form). -/
theorem not_card_le_two_mul_ncard_of_subset_inter (K : Finset V) {B S : Set V}
    (hS : S ⊆ (K : Set V) ∩ B) (h : 2 * ((K : Set V) ∩ B).ncard < K.card) :
    ¬ K.card ≤ 2 * S.ncard := by
  have := two_mul_ncard_lt_of_subset_inter K hS h
  omega

/-- A set of committee members in `B` is no three-quarter quorum of the committee
(`ncard` form). -/
theorem not_three_mul_card_le_ncard_of_subset_inter (K : Finset V) {B S : Set V}
    (hS : S ⊆ (K : Set V) ∩ B) (h : 2 * ((K : Set V) ∩ B).ncard < K.card) :
    ¬ 3 * K.card ≤ 4 * S.ncard := by
  have := two_mul_ncard_lt_of_subset_inter K hS h
  omega

/-- **R21** (`ncard` form). -/
theorem ncard_eq_one_of_subset_union_singleton (K : Finset V) {F O : Set V} {p : V}
    (hO : O ⊆ ((K : Set V) ∩ F) ∪ {p}) (h3 : 3 * K.card ≤ 4 * O.ncard)
    (h2 : 2 * ((K : Set V) ∩ F).ncard < K.card) : K.card = 1 := by
  have h4 := Set.ncard_le_ncard hO
    ((K.finite_toSet.inter_of_left F).union (Set.finite_singleton p))
  have h5 := Set.ncard_union_le ((K : Set V) ∩ F) {p}
  have h6 := Set.ncard_singleton p
  exact eq_one_of_three_mul_le (f := ((K : Set V) ∩ F).ncard) (by omega) h2

/-- In a singleton committee with fewer than half faulty, every member is not faulty
(`ncard` form). -/
theorem not_mem_of_ncard_eq_one {K : Finset V} {F : Set V} (h1 : K.card = 1)
    (h2 : 2 * ((K : Set V) ∩ F).ncard < K.card) {u : V} (hu : u ∈ K) : u ∉ F := fun hF => by
  have := (Set.ncard_pos (K.finite_toSet.inter_of_left F)).2
    ⟨u, (⟨Finset.mem_coe.2 hu, hF⟩ : u ∈ (K : Set V) ∩ F)⟩
  omega

end Set

/-! ## Committee forms of universe counts -/

section FinsetUniverse

variable {V : Type*} [DecidableEq V]

/-- **S13, R21.** A three-quarter quorum `O` of committee members inside the faulty members and
one more validator, with fewer than half of the committee faulty, makes the committee a singleton
with a non-faulty member of `O` that every member equals. At `K = univ` over `Fin n` this is the
stock `n = 1`, the honest optimistic voter and `Fin.ext`. -/
theorem singleton_of_quorum_subset_union_singleton (K : Finset V) {F O : Finset V} {p : V}
    (hOK : O ⊆ K) (hO : O ⊆ (K ∩ F) ∪ {p}) (h3 : 3 * K.card ≤ 4 * O.card)
    (h2 : 2 * (K ∩ F).card < K.card) :
    K.card = 1 ∧ ∃ u ∈ O, u ∉ F ∧ ∀ y ∈ K, y = u := by
  have h1 := card_eq_one_of_subset_union_singleton K hO h3 h2
  obtain ⟨u, hu⟩ : O.Nonempty := Finset.card_pos.mp (by omega)
  exact ⟨h1, u, hu, not_mem_of_card_eq_one h1 h2 (hOK hu),
    fun y hy => eq_of_mem_of_card_eq_one h1 hy (hOK hu)⟩

end FinsetUniverse

section SetUniverse

variable {V : Type*}

/-- **S5, S6.** A set of committee members has at most the committee's size. At `K = univ` over
`Fin n` this is the stock `ncard_le_n`. -/
theorem ncard_le_card_of_subset_coe {K : Finset V} {T : Set V} (hT : T ⊆ (K : Set V)) :
    T.ncard ≤ K.card := by
  have h := Set.ncard_le_ncard hT K.finite_toSet
  have hK := Set.ncard_coe_finset K
  omega

/-- **S6, S11 (`hint`).** Two three-quarter quorums of committee members overlap in more than the
faulty committee members when fewer than half of the committee is faulty. At `K = univ` over
`Fin n` this is the stock overlap count against `2 f < n`. -/
theorem ncard_inter_lt_ncard_inter_of_quorums (K : Finset V) {F O₁ O₂ : Set V}
    (h₁ : O₁ ⊆ (K : Set V)) (h₂ : O₂ ⊆ (K : Set V)) (h3₁ : 3 * K.card ≤ 4 * O₁.ncard)
    (h3₂ : 3 * K.card ≤ 4 * O₂.ncard) (h2 : 2 * ((K : Set V) ∩ F).ncard < K.card) :
    ((K : Set V) ∩ F).ncard < (O₁ ∩ O₂).ncard := by
  have hI := Set.ncard_inter_add_ncard_union O₁ O₂ (K.finite_toSet.subset h₁)
    (K.finite_toSet.subset h₂)
  have hU := ncard_le_card_of_subset_coe (Set.union_subset h₁ h₂)
  omega

/-- **S6, S11.** Two three-quarter quorums of committee members share a non-faulty member when
fewer than half of the committee is faulty. -/
theorem exists_mem_inter_not_mem_of_quorums (K : Finset V) {F O₁ O₂ : Set V}
    (h₁ : O₁ ⊆ (K : Set V)) (h₂ : O₂ ⊆ (K : Set V)) (h3₁ : 3 * K.card ≤ 4 * O₁.ncard)
    (h3₂ : 3 * K.card ≤ 4 * O₂.ncard) (h2 : 2 * ((K : Set V) ∩ F).ncard < K.card) :
    ∃ u, u ∈ O₁ ∩ O₂ ∧ u ∉ F := by
  obtain ⟨u, hu, hnot⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (ncard_inter_lt_ncard_inter_of_quorums K h₁ h₂ h3₁ h3₂ h2) (K.finite_toSet.inter_of_left F)
  exact ⟨u, hu, fun hF => hnot ⟨h₁ hu.1, hF⟩⟩

/-- **S11 (`h3`).** With the voters `W` and a three-quarter quorum `SX` inside the committee and the
equivocators `E` faulty committee members, the equivocators and the voters outside `SX` are fewer
than `SX`. The committee replaces the universe complement `SXᶜ` of the stock count: at
`K = univ` over `Fin n` the voters outside `SX` lie in `SXᶜ` and `|SX| + |SXᶜ| = n`. -/
theorem ncard_add_ncard_sdiff_lt (K : Finset V) {F E W SX : Set V} (hSX : SX ⊆ (K : Set V))
    (hW : W ⊆ (K : Set V)) (hE : E ⊆ (K : Set V) ∩ F) (h34 : 3 * K.card ≤ 4 * SX.ncard)
    (h2 : 2 * ((K : Set V) ∩ F).ncard < K.card) : E.ncard + (W \ SX).ncard < SX.ncard := by
  have hEf := Set.ncard_le_ncard hE (K.finite_toSet.inter_of_left F)
  have hWK : W \ SX ⊆ (K : Set V) := fun _ hx => hW hx.1
  have hdisj : Disjoint (W \ SX) SX := Set.disjoint_left.2 fun _ hx hx' => hx.2 hx'
  have hu := Set.ncard_union_eq hdisj (K.finite_toSet.subset hWK) (K.finite_toSet.subset hSX)
  have hle := ncard_le_card_of_subset_coe (Set.union_subset hWK hSX)
  omega

/-- **S13, R21** (`ncard` form). -/
theorem singleton_of_quorum_subset_union_singleton_ncard (K : Finset V) {F O : Set V} {p : V}
    (hOK : O ⊆ (K : Set V)) (hO : O ⊆ ((K : Set V) ∩ F) ∪ {p}) (h3 : 3 * K.card ≤ 4 * O.ncard)
    (h2 : 2 * ((K : Set V) ∩ F).ncard < K.card) :
    K.card = 1 ∧ ∃ u ∈ O, u ∉ F ∧ ∀ y ∈ K, y = u := by
  have h1 := ncard_eq_one_of_subset_union_singleton K hO h3 h2
  obtain ⟨u, hu⟩ : O.Nonempty := (Set.ncard_pos (K.finite_toSet.subset hOK)).mp (by omega)
  exact ⟨h1, u, hu, not_mem_of_ncard_eq_one h1 h2 (hOK hu),
    fun y hy => eq_of_mem_of_card_eq_one h1 hy (hOK hu)⟩

end SetUniverse

section Fintype

variable {V : Type*} [Fintype V]

/-- At the full committee a committee count is the population count. -/
theorem ncard_coe_univ_inter (F : Set V) :
    (((Finset.univ : Finset V) : Set V) ∩ F).ncard = F.ncard := by
  rw [Finset.coe_univ, Set.univ_inter]

/-- At the full committee the committee fault bound is the population fault bound. -/
theorem two_mul_ncard_inter_univ_lt_iff (F : Set V) :
    2 * (((Finset.univ : Finset V) : Set V) ∩ F).ncard < (Finset.univ : Finset V).card ↔
      2 * F.ncard < Fintype.card V := by
  rw [ncard_coe_univ_inter, Finset.card_univ]

/-- **S11, the split fault premise.** The stock first transfer's one population premise
`2 |F| < n` becomes two committee premises: at the label-`s` committee (the optimistic quorums,
the overlap and the cover count) and at the label-`(s + 1)` committee (the slot-`(s + 1)` locks).
With every committee the full set, both are the population premise. -/
theorem two_mul_ncard_inter_lt_pair_of_univ {K : Nat → Finset V}
    (hK : ∀ m, K m = Finset.univ) {F : Set V} (hf : 2 * F.ncard < Fintype.card V) (s : Nat) :
    2 * ((K s : Set V) ∩ F).ncard < (K s).card ∧
      2 * ((K (s + 1) : Set V) ∩ F).ncard < (K (s + 1)).card := by
  rw [hK s, hK (s + 1)]
  exact ⟨(two_mul_ncard_inter_univ_lt_iff F).2 hf, (two_mul_ncard_inter_univ_lt_iff F).2 hf⟩

end Fintype

end Consensus
