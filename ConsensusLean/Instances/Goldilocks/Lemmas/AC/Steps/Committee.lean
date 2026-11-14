module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.CommitteeRun

public section

/-! # Goldilocks SA: committee count steps and the full committee

The count steps of the committee-native AC step lemmas and their reductions at the full committee.

The committee is `K : CommitteeDict sp.n`, bound by (i) `K.BindsSel rho voteRole` at the engine
and (ii) `∀ s, (K.committee s).ncard = sp.committeeSize`. Thresholds are in
`N = sp.committeeSize`; fault premises are over `ncard` of `K.committee s`.

* Count steps over `C = K.committee s` with `hN : C.ncard = N` (binding (ii)), each by a count
  over a `Finset` committee after lifting `C` to a `Finset`: `cs2_of_cs`, `not_update_update`,
  `not_update_optimistic`, `quorums_meet`, `cover_count`, `next_transfer_counts`,
  `inter_nonempty_of_half_quorum`, `third_cover_count`.
* Reductions at `K = CommitteeDict.full n` with `committeeSize = n`: `committee_full`,
  `mem_full`, `ncard_full`, `size_binding_full`, `ncard_inter_full`,
  `mul_ncard_inter_full_lt_iff`, `ncard_inter_full_lt_iff`; P, T and CS at the full committee
  (`CommitteeP.full`, `CommitteeT.full`, `CommitteePAt.full`, `CommitteeTAt.full`,
  `faultBoundK_full_iff`); the half, third and
  three-quarter fault bounds at the full committee from the population ones (`cs2_full`,
  `third_full`, `four_thirds_full`). -/

namespace Consensus.Goldilocks.SA

section Counts

variable {V : Type*}

/-! ## Counts over a `Finset` committee -/

/-- Two disjoint sets meet the committee in at most its size together. -/
private theorem ncard_inter_add_ncard_inter_le (K : Finset V) {A B : Set V}
    (hd : Disjoint A B) : ((K : Set V) ∩ A).ncard + ((K : Set V) ∩ B).ncard ≤ K.card := by
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

/-- Fewer faulty committee members than members of a set `J` of honest validators are fewer than
half of the committee. -/
private theorem two_mul_ncard_inter_compl_lt (K : Finset V) {H J : Set V} (hJ : J ⊆ H)
    (h : ((K : Set V) ∩ Hᶜ).ncard < ((K : Set V) ∩ J).ncard) :
    2 * ((K : Set V) ∩ Hᶜ).ncard < K.card := by
  have := ncard_inter_add_ncard_inter_le K (Set.disjoint_of_subset_left hJ disjoint_compl_right)
  omega

/-- A set of committee members has at most the committee's size. -/
private theorem ncard_le_card_of_subset_coe {K : Finset V} {T : Set V}
    (hT : T ⊆ (K : Set V)) : T.ncard ≤ K.card := by
  have h := Set.ncard_le_ncard hT K.finite_toSet
  have hK := Set.ncard_coe_finset K
  omega

/-- Two three-quarter quorums of committee members share a member outside `F` when fewer than half
of the committee is in `F`. -/
private theorem exists_mem_inter_not_mem_of_quorums (K : Finset V) {F O₁ O₂ : Set V}
    (h₁ : O₁ ⊆ (K : Set V)) (h₂ : O₂ ⊆ (K : Set V)) (h3₁ : 3 * K.card ≤ 4 * O₁.ncard)
    (h3₂ : 3 * K.card ≤ 4 * O₂.ncard) (h2 : 2 * ((K : Set V) ∩ F).ncard < K.card) :
    ∃ u, u ∈ O₁ ∩ O₂ ∧ u ∉ F := by
  have hI := Set.ncard_inter_add_ncard_union O₁ O₂ (K.finite_toSet.subset h₁)
    (K.finite_toSet.subset h₂)
  have hU := ncard_le_card_of_subset_coe (Set.union_subset h₁ h₂)
  obtain ⟨u, hu, hnot⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (show ((K : Set V) ∩ F).ncard < (O₁ ∩ O₂).ncard by omega) (K.finite_toSet.inter_of_left F)
  exact ⟨u, hu, fun hF => hnot ⟨h₁ hu.1, hF⟩⟩

/-- With the voters `W` and a three-quarter quorum `SX` inside the committee and `E` a set of
committee members in `F`, fewer than half of the committee, `E` and the voters outside `SX` are
fewer than `SX`. -/
private theorem ncard_add_ncard_sdiff_lt (K : Finset V) {F E W SX : Set V}
    (hSX : SX ⊆ (K : Set V)) (hW : W ⊆ (K : Set V)) (hE : E ⊆ (K : Set V) ∩ F)
    (h34 : 3 * K.card ≤ 4 * SX.ncard) (h2 : 2 * ((K : Set V) ∩ F).ncard < K.card) :
    E.ncard + (W \ SX).ncard < SX.ncard := by
  have hEf := Set.ncard_le_ncard hE (K.finite_toSet.inter_of_left F)
  have hWK : W \ SX ⊆ (K : Set V) := fun _ hx => hW hx.1
  have hdisj : Disjoint (W \ SX) SX := Set.disjoint_left.2 fun _ hx hx' => hx.2 hx'
  have hu := Set.ncard_union_eq hdisj (K.finite_toSet.subset hWK) (K.finite_toSet.subset hSX)
  have hle := ncard_le_card_of_subset_coe (Set.union_subset hWK hSX)
  omega

/-! ## The committee half bound -/

/-- The committee sleepy count CS gives the committee half bound CS2. -/
theorem cs2_of_cs [Finite V] (C : Set V) {H J : Set V} (hJ : J ⊆ H)
    (hCS : (C ∩ Hᶜ).ncard < (C ∩ J).ncard) : 2 * (C ∩ Hᶜ).ncard < C.ncard := by
  obtain ⟨K, rfl⟩ := (Set.toFinite C).exists_finset_coe
  have := two_mul_ncard_inter_compl_lt K hJ hCS
  have := Set.ncard_coe_finset K
  omega

/-! ## `fastLock_same_slotU` -/

/-- **Two updates.** The voters `W` of the slot-`s` pool are committee members. -/
theorem not_update_update [Finite V] (C : Set V) {N : Nat} {S S' W : Set V}
    (hN : C.ncard = N) (hW : W ⊆ C) (hn' : N ≤ 2 * S'.ncard) (hmaj : W.ncard < 2 * S.ncard)
    (hsum : S'.ncard + S.ncard ≤ W.ncard) : False := by
  obtain ⟨K, rfl⟩ := (Set.toFinite C).exists_finset_coe
  have := ncard_le_card_of_subset_coe hW
  have := Set.ncard_coe_finset K
  omega

/-- **An update and an optimistic confirmation.** Half and three quarters of the committee do not
fit disjointly among committee voters; CS2 excludes the empty committee. -/
theorem not_update_optimistic [Finite V] (C : Set V) {N : Nat} {F S T W : Set V}
    (hN : C.ncard = N) (hW : W ⊆ C) (h2 : 2 * (C ∩ F).ncard < C.ncard)
    (hn : N ≤ 2 * S.ncard) (h34 : 3 * N ≤ 4 * T.ncard) (hsum : T.ncard + S.ncard ≤ W.ncard) :
    False := by
  obtain ⟨K, rfl⟩ := (Set.toFinite C).exists_finset_coe
  have := ncard_le_card_of_subset_coe hW
  have := Set.ncard_coe_finset K
  omega

/-- **Two optimistic quorums** of committee members share a non-faulty member. -/
theorem quorums_meet [Finite V] (C : Set V) {N : Nat} {F O₁ O₂ : Set V} (hN : C.ncard = N)
    (h₁ : O₁ ⊆ C) (h₂ : O₂ ⊆ C) (h3₁ : 3 * N ≤ 4 * O₁.ncard) (h3₂ : 3 * N ≤ 4 * O₂.ncard)
    (h2 : 2 * (C ∩ F).ncard < C.ncard) : ∃ u, u ∈ O₁ ∩ O₂ ∧ u ∉ F := by
  obtain ⟨K, rfl⟩ := (Set.toFinite C).exists_finset_coe
  have hK := Set.ncard_coe_finset K
  exact exists_mem_inter_not_mem_of_quorums K h₁ h₂ (by omega) (by omega) (by omega)

/-! ## `Nodes`, `CarryPrefix` -/

/-- **The optimistic cover count** (`optimistic_transfer_storedU`):
the equivocators and the voters outside a three-quarter quorum `SX` are fewer than `SX`. -/
theorem cover_count [Finite V] (C : Set V) {N : Nat} {F E W SX : Set V} (hN : C.ncard = N)
    (hSX : SX ⊆ C) (hW : W ⊆ C) (hE : E ⊆ C ∩ F) (h34 : 3 * N ≤ 4 * SX.ncard)
    (h2 : 2 * (C ∩ F).ncard < C.ncard) : E.ncard + (W \ SX).ncard < SX.ncard := by
  obtain ⟨K, rfl⟩ := (Set.toFinite C).exists_finset_coe
  have hK := Set.ncard_coe_finset K
  exact ncard_add_ncard_sdiff_lt K hSX hW hE (by omega) (by omega)

/-- **`next_transfer_of_carryU`.** CS gives CS2, and with half of the committee size voting
honestly the honest voters `SX` and the faulty members are fewer than twice `SX`. -/
theorem next_transfer_counts [Finite V] (C : Set V) {N : Nat} {H J SX : Set V}
    (hN : C.ncard = N) (hJ : J ⊆ H) (hCS : (C ∩ Hᶜ).ncard < (C ∩ J).ncard)
    (hhalf : N ≤ 2 * SX.ncard) :
    2 * (C ∩ Hᶜ).ncard < C.ncard ∧ (SX ∪ (C ∩ Hᶜ)).ncard < 2 * SX.ncard := by
  have hf2 := cs2_of_cs C hJ hCS
  have := Set.ncard_union_le SX (C ∩ Hᶜ)
  exact ⟨hf2, by omega⟩

/-- **`first_transfer_stored_of_poolU` (`hint`).** Half and three quarters of the committee size,
both of committee members, overlap; CS2 excludes the empty committee. -/
theorem inter_nonempty_of_half_quorum [Finite V] (C : Set V) {N : Nat} {F S O : Set V}
    (hN : C.ncard = N) (hS : S ⊆ C) (hO : O ⊆ C) (h2 : 2 * (C ∩ F).ncard < C.ncard)
    (hhalf : N ≤ 2 * S.ncard) (h34 : 3 * N ≤ 4 * O.ncard) : (S ∩ O).Nonempty := by
  obtain ⟨K, rfl⟩ := (Set.toFinite C).exists_finset_coe
  have hI := Set.ncard_inter_add_ncard_union S O (K.finite_toSet.subset hS)
    (K.finite_toSet.subset hO)
  have hU := ncard_le_card_of_subset_coe (Set.union_subset hS hO)
  have hK := Set.ncard_coe_finset K
  exact Set.nonempty_of_ncard_ne_zero (by omega)

/-- **`honest_isBest_of_carry` (`h3`).** With fewer than a third of the committee faulty, the
equivocators (faulty members) and the voters outside the honest members are fewer than the honest
members. The committee split `|C ∩ H| + |C ∩ Hᶜ| = |C|` replaces `|H| + |Hᶜ| = n`. -/
theorem third_cover_count [Finite V] (C : Set V) {H E W : Set V} (hW : W ⊆ C)
    (hE : E ⊆ C ∩ Hᶜ) (h3 : 3 * (C ∩ Hᶜ).ncard < C.ncard) :
    E.ncard + (W \ (C ∩ H)).ncard < (C ∩ H).ncard := by
  have hfin := (Set.toFinite C).inter_of_left Hᶜ
  have hEf := Set.ncard_le_ncard hE hfin
  have hout : W \ (C ∩ H) ⊆ C ∩ Hᶜ := fun x hx =>
    ⟨hW hx.1, (fun hH => hx.2 ⟨hW hx.1, hH⟩ : x ∉ H)⟩
  have hWf := Set.ncard_le_ncard hout hfin
  have hsplit : (C ∩ H).ncard + (C ∩ Hᶜ).ncard = C.ncard :=
    Set.ncard_inter_add_ncard_sdiff_eq_ncard C H (Set.toFinite C)
  omega

end Counts

/-! ## Reductions at the full committee, `committeeSize = n` -/

section Full

/-- Every slot of the full dictionary is the whole validator set. -/
theorem committee_full (n s : Nat) : (CommitteeDict.full n).committee s = Set.univ := rfl

/-- P and T membership at `K = full` holds for every signer. -/
theorem mem_full {n : Nat} (s : Nat) (u : Fin n) : u ∈ (CommitteeDict.full n).committee s :=
  Set.mem_univ u

/-- The full committee has `n` members. -/
theorem ncard_full (n s : Nat) : ((CommitteeDict.full n).committee s).ncard = n := by
  rw [committee_full, Set.ncard_univ, Nat.card_fin]

/-- **Binding (ii) at `K = full`** with `committeeSize = n`. -/
theorem size_binding_full {n N : Nat} (hN : N = n) (s : Nat) :
    ((CommitteeDict.full n).committee s).ncard = N := by
  rw [ncard_full]
  exact hN.symm

/-- A count restricted to the full committee is the population count. -/
theorem ncard_inter_full {n : Nat} (s : Nat) (F : Set (Fin n)) :
    ((CommitteeDict.full n).committee s ∩ F).ncard = F.ncard := by
  rw [committee_full, Set.univ_inter]

/-- **CS2 (`k = 2`) and the third bound (`k = 3`) at `K = full`** are the stock `k f < n`. -/
theorem mul_ncard_inter_full_lt_iff {n : Nat} (k s : Nat) (F : Set (Fin n)) :
    k * ((CommitteeDict.full n).committee s ∩ F).ncard <
      ((CommitteeDict.full n).committee s).ncard ↔ k * F.ncard < n := by
  rw [ncard_inter_full, ncard_full]

/-- **CS at `K = full`** is the stock comparison; with `J` the honest awake joined validators
at `t` it is `FaultBound tr H t`. -/
theorem ncard_inter_full_lt_iff {n : Nat} (s : Nat) (F J : Set (Fin n)) :
    ((CommitteeDict.full n).committee s ∩ F).ncard <
      ((CommitteeDict.full n).committee s ∩ J).ncard ↔ F.ncard < J.ncard := by
  rw [ncard_inter_full, ncard_inter_full]

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}

/-- **P at `K = full`.** -/
theorem CommitteeP.full {tr : SATrace sp FGP ro} {H : Set (Fin sp.n)} :
    CommitteeP (CommitteeDict.full sp.n) tr H :=
  ⟨fun _ _ _ s _ _ => mem_full s _, fun _ _ _ _ _ _ s _ _ => mem_full s _⟩

/-- **T at `K = full`.** -/
theorem CommitteeT.full {tr : SATrace sp FGP ro} {H : Set (Fin sp.n)} :
    CommitteeT (CommitteeDict.full sp.n) tr H :=
  fun _ _ _ _ _ _ _ v _ => mem_full v.slot _

/-- P under growing faults holds at `K = full`. -/
theorem CommitteePAt.full {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)} :
    CommitteePAt (CommitteeDict.full sp.n) tr H :=
  ⟨fun _ _ _ _ _ s _ _ => mem_full s _, fun _ _ _ _ _ _ s _ _ => mem_full s _⟩

/-- T under growing faults holds at `K = full`. -/
theorem CommitteeTAt.full {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)} :
    CommitteeTAt (CommitteeDict.full sp.n) tr H :=
  fun _ _ _ _ _ _ _ v _ => mem_full v.slot _

/-- **CS at `K = full`** is `FaultBound`. -/
theorem faultBoundK_full_iff {tr : SATrace sp FGP ro} {H : Set (Fin sp.n)} (s : Nat) (t : Time) :
    FaultBoundK (CommitteeDict.full sp.n) s tr H t ↔ FaultBound tr H t :=
  ncard_inter_full_lt_iff s _ _

/-- **CS2 at `K = full`** from the population half bound, with `committeeSize = n`. -/
theorem cs2_full (hc : sp.committeeSize = sp.n) {F : Set (Fin sp.n)} (hf : 2 * F.ncard < sp.n)
    {s : Nat} : 2 * ((CommitteeDict.full sp.n).committee s ∩ F).ncard < sp.committeeSize := by
  rw [ncard_inter_full, hc]
  exact hf

/-- **The third bound at `K = full`** from the population one, with `committeeSize = n`. -/
theorem third_full (hc : sp.committeeSize = sp.n) {F : Set (Fin sp.n)} (hf : 3 * F.ncard < sp.n)
    {s : Nat} : 3 * ((CommitteeDict.full sp.n).committee s ∩ F).ncard < sp.committeeSize := by
  rw [ncard_inter_full, hc]
  exact hf

/-- **The four-thirds bound at `K = full`** from the population one, with
`committeeSize = n`. -/
theorem four_thirds_full (hc : sp.committeeSize = sp.n) {F : Set (Fin sp.n)}
    (hf : 4 * F.ncard < 3 * sp.n) {s : Nat} :
    4 * ((CommitteeDict.full sp.n).committee s ∩ F).ncard < 3 * sp.committeeSize := by
  rw [ncard_inter_full, hc]
  exact hf

end Full

end Consensus.Goldilocks.SA

end
