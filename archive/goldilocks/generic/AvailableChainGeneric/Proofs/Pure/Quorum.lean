module
public import AvailableChainGeneric.Statements.Pure.Quorum -- shake: keep (re-export)
public import AvailableChainGeneric.Statements.Pure.QuorumInter
public import AvailableChainGeneric.Statements.Pure.Dominance
public import AvailableChainGeneric.Proofs.Pure.SupportCounts
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Push -- shake: keep (re-export)

public section

/-! G01 count facts, adopted by DC in GLY r3.15 and r3.16:
`claude-files/a0/archive/generic-layer-r3.16-4e3cf44c.md:9–32`. -/

namespace AvailableChain.Gen.Pure

variable {V : Type} [DecidableEq V] [Fintype V]

-- Source: AvailableChainKitFG/Ancestry.lean:18–53 (GLY E-5, S4b-06).
omit [DecidableEq V] in
/-- A quorum has a member outside a set of weight below `q`. -/
theorem quorum_honest (E : Weights V) (faulty : Finset V) {Q : Finset V}
    (hQ : E.IsQuorum Q) (hcap : E.weightOf faulty < E.q) : ∃ i ∈ Q, i ∉ faulty := by
  by_contra hn
  push Not at hn
  have hle : E.weightOf Q ≤ E.weightOf faulty := by
    simp only [Weights.weightOf_def]
    exact Finset.sum_le_sum_of_subset hn
  rw [Weights.IsQuorum_def] at hQ
  omega

/-- The weights of two quorums give a lower bound for their intersection. -/
theorem quorum_intersection (E : Weights V) {Q Q' : Finset V}
    (hQ : E.IsQuorum Q) (hQ' : E.IsQuorum Q') :
    2 * E.q ≤ E.totalWeight + E.weightOf (Q ∩ Q') := by
  have hie : E.weightOf (Q ∪ Q') + E.weightOf (Q ∩ Q') = E.weightOf Q + E.weightOf Q' := by
    simp only [Weights.weightOf_def]
    exact Finset.sum_union_inter
  have hu : E.weightOf (Q ∪ Q') ≤ E.totalWeight := by
    simp only [Weights.weightOf_def, Weights.totalWeight_def]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Weights.IsQuorum_def] at hQ hQ'
  omega

/-- Two quorums meet outside a set of weight below `2q − W`. -/
theorem quorum_inter_honest (E : Weights V) {Q Q' F : Finset V}
    (hQ : E.IsQuorum Q) (hQ' : E.IsQuorum Q')
    (hF : E.weightOf F + E.totalWeight < 2 * E.q) : ∃ i ∈ Q ∩ Q', i ∉ F := by
  have hint := quorum_intersection E hQ hQ'
  by_contra hn
  push Not at hn
  have hle : E.weightOf (Q ∩ Q') ≤ E.weightOf F := by
    simp only [Weights.weightOf_def]
    exact Finset.sum_le_sum_of_subset hn
  omega

/-- The recovery count bound gives an honest quorum intersection. -/
theorem count_rec {n a : Nat} (hn : 0 < n) (hf : a ≤ (n - 1) / 3) : FaultX n a := by
  constructor
  rw [qF_def]
  let q := (2 * n + 2) / 3
  have ha : a * 3 < n :=
    Nat.lt_of_le_of_lt ((Nat.le_div_iff_mul_le (by decide)).mp hf)
      (Nat.sub_lt hn (by decide))
  have hq : 2 * n ≤ 3 * q := by
    apply Nat.le_of_add_le_add_right (b := 2)
    calc
      2 * n + 2 = 3 * q + (2 * n + 2) % 3 := (Nat.div_add_mod _ _).symm
      _ ≤ 3 * q + 2 :=
        Nat.add_le_add_left (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))) _
  have hmul : (a + n) * 3 < (2 * q) * 3 := by
    calc
      (a + n) * 3 = a * 3 + n * 3 := Nat.add_mul _ _ _
      _ < n + n * 3 := Nat.add_lt_add_right ha _
      _ = (2 * n) * 2 := by
        simp [Nat.mul_succ, Nat.succ_mul, Nat.add_left_comm, Nat.add_comm]
      _ ≤ (3 * q) * 2 := Nat.mul_le_mul_right _ hq
      _ = (2 * q) * 3 := by
        simp only [Nat.mul_left_comm, Nat.mul_comm]
  exact Nat.lt_of_not_le fun hle =>
    Nat.not_le_of_gt hmul (Nat.mul_le_mul_right 3 hle)

/-- An honest count above the faulty count gives an honest quorum member. -/
theorem count_clean {n a h : Nat} (hah : a < h) (hhn : h ≤ n - a) : FaultQ n a := by
  constructor
  rw [qF_def]
  have han : a < n :=
    Nat.sub_pos_iff_lt.mp (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.zero_le a) hah) hhn)
  have hsum : a + a < n :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_right hah a)
      ((Nat.le_sub_iff_add_le (Nat.le_of_lt han)).mp hhn)
  apply Nat.lt_of_succ_le
  apply (Nat.le_div_iff_mul_le (by decide)).mpr
  calc
    (a + 1) * 3 ≤ (a + 1) * 4 := Nat.mul_le_mul_left _ (by decide)
    _ = 2 * (a + a + 1) + 2 := by
      simp [Nat.mul_succ, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ ≤ 2 * n + 2 := Nat.add_le_add_right (Nat.mul_le_mul_left _ hsum) _

end AvailableChain.Gen.Pure

namespace AvailableChain.Gen.Pure

/-- The closed unit-seat statement follows from the weighted intersection result.
DC: Generic/Conditions.lean:180 BelowOneThird; INTENTIONAL: unit-seat two-quorum bound;
record gly319/generic-layer.md:1297 (GLY r3.19 S044). -/
theorem faultX_inter_honest_statement : FaultXInterHonestStatement := by
  rw [FaultXInterHonestStatement_def]
  intro n a Q Q' F hX hF hQ hQ'
  let E : Weights (Fin n) := ⟨fun _ => 1, by intro i; decide⟩
  have hweight (S : Finset (Fin n)) : E.weightOf S = S.card := by
    simp [Weights.weightOf_def, E]
  have htotal : E.totalWeight = n := by
    simp [Weights.totalWeight_def, E]
  have hq : E.q = qF n := by
    rw [Weights.q_def, htotal, qF_def]
  apply quorum_inter_honest E
  · rwa [Weights.IsQuorum_def, hq, hweight]
  · rwa [Weights.IsQuorum_def, hq, hweight]
  · rw [hweight, htotal, hq]
    have := hX.lt
    omega

/-- Two unit-seat quorums have an honest member in their intersection.
DC: Generic/Conditions.lean:180 BelowOneThird; INTENTIONAL: unit-seat two-quorum bound;
record gly319/generic-layer.md:1297 (GLY r3.19 S044). -/
theorem FaultX.inter_honest {n a : Nat} {Q Q' F : Finset (Fin n)}
    (hX : FaultX n a) (hF : F.card ≤ a)
    (hQ : qF n ≤ Q.card) (hQ' : qF n ≤ Q'.card) :
    ∃ v ∈ Q ∩ Q', v ∉ F :=
  faultX_inter_honest_statement hX hF hQ hQ'

end AvailableChain.Gen.Pure

namespace AvailableChain.Gen.Pure

/-- Two eligible children have a common supporter, so disjoint support forces equality.
DC: Goldfish/Confirmation.lean:405, 419–423; INTENTIONAL (lead ruling 2026-10-01): the count step of
eligible_compatible. -/
theorem maj_unique_child_statement : MajUniqueChildStatement := by
  rw [MajUniqueChildStatement_def]
  intro n children support denominator hsub hdis C hC D hD hmajC hmajD
  by_contra hne
  have hunion : support C ∪ support D ⊆ denominator :=
    Finset.union_subset (hsub C hC) (hsub D hD)
  obtain ⟨i, hi⟩ := two_majorities_intersect hunion hunion hmajC hmajD
  exact Finset.disjoint_left.mp (hdis C hC D hD hne)
    (Finset.mem_inter.mp hi).1 (Finset.mem_inter.mp hi).2

/-- At most one child has a strict majority of disjoint counted support sets.
DC: Goldfish/Confirmation.lean:405, 419–423; INTENTIONAL (lead ruling 2026-10-01): the count step of
eligible_compatible. -/
theorem maj_unique_child : MajUniqueChildStatement :=
  maj_unique_child_statement

end AvailableChain.Gen.Pure
