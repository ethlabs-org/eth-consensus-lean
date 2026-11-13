module
public import ConsensusLean.Lemmas.Problem.CommitteeCount
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.CommitteeRun

public section

/-! # Goldilocks SA: committee count steps and the full committee

The count steps of the committee-native AC step lemmas and their reductions at the full committee.

The committee is `K : CommitteeDict sp.n`, bound by (i) `K.BindsSel rho voteRole` at the engine
and (ii) `∀ s, (K.committee s).ncard = sp.committeeSize`. Thresholds are in
`N = sp.committeeSize`; fault premises are over `ncard` of `K.committee s`.

* Count steps over `C = K.committee s` with `hN : C.ncard = N` (binding (ii)), each by
  `CommitteeCount` after lifting `C` to a `Finset`: `size_pos_of_cs2`, `nonempty_of_half`,
  `cs2_of_cs`, `not_update_update`, `not_update_optimistic`, `quorums_meet`, `cover_count`,
  `next_transfer_counts`, `inter_nonempty_of_half_quorum`, `third_cover_count`.
* Reductions at `K = CommitteeDict.full n` with `committeeSize = n`: `committee_full`,
  `full_eq_coe_univ`, `mem_full`, `ncard_full`, `size_binding_full`, `ncard_inter_full`,
  `mul_ncard_inter_full_lt_iff`, `ncard_inter_full_lt_iff`; P, T and CS at the full committee
  (`CommitteeP.full`, `CommitteeT.full`, `faultBoundK_full_iff`); the half, third and
  three-quarter fault bounds at the full committee from the population ones (`cs2_full`,
  `third_full`, `four_thirds_full`). -/

namespace Consensus.Goldilocks.SA

section Counts

variable {V : Type*}

/-! ## `c = 0` -/

/-- **`c = 0`.** The strict committee fault premise (CS2) and binding (ii) give
`0 < committeeSize`. -/
theorem size_pos_of_cs2 (C : Set V) {F : Set V} {N : Nat} (hN : C.ncard = N)
    (h2 : 2 * (C ∩ F).ncard < C.ncard) : 0 < N := by
  omega

/-- **`locks_after_unlock`.** Half of a positive committee size is nonempty. -/
theorem nonempty_of_half {S : Set V} {N : Nat} (hpos : 0 < N) (hn : N ≤ 2 * S.ncard) :
    S.Nonempty :=
  Set.nonempty_of_ncard_ne_zero (by omega)

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

/-- **The optimistic cover count** (`optimistic_transfer_storedU`, `optimistic_isBest_of_carry`):
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

/-- The full dictionary's slot is the `univ` committee of `CommitteeCount`. -/
theorem full_eq_coe_univ (n s : Nat) :
    (CommitteeDict.full n).committee s = ((Finset.univ : Finset (Fin n)) : Set (Fin n)) := by
  rw [committee_full, Finset.coe_univ]

/-- **P, T and G at `K = full`** hold for every signer. -/
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
  rw [full_eq_coe_univ]
  exact ncard_coe_univ_inter F

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
