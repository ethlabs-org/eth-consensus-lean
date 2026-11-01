module
public import AvailableChainGeneric.Statements.Pure.PCQuorum
public import Mathlib.Data.Fintype.Card

public section

/-! Proofs of the PC threshold contracts. The count step follows
`AvailableChainSAPC/Proofs/Quorum.lean:21–47` with the `q_N`, `q_A` bounds. -/

namespace AvailableChain.Gen.Pure

/-- `q_A n + n ≤ 2 q_N n`: two `q_N` sets overlap in `q_A` seats. -/
theorem qA_add_le_two_mul_qN (n : Nat) : qA n + n ≤ 2 * qN n := by
  rw [qA_def, qN_def]
  omega

/-- `a < q_A n` exactly when `2a < n`, that is `a < n/2`. -/
theorem lt_qA_iff_two_mul_lt (n a : Nat) : a < qA n ↔ 2 * a < n := by
  rw [qA_def]
  omega

/-- Two `q_N` seat sets of `n` seats share at least `2 q_N n − n` seats. -/
theorem two_mul_qN_le_add_inter_card {n : Nat} {Q Q' : Finset (Fin n)}
    (hQ : qN n ≤ Q.card) (hQ' : qN n ≤ Q'.card) :
    2 * qN n ≤ n + (Q ∩ Q').card := by
  have hu : (Q ∪ Q').card ≤ n := by
    simpa using Finset.card_le_univ (Q ∪ Q')
  have he := Finset.card_union_add_card_inter Q Q'
  omega

theorem qN_inter_card_statement : QNInterCardStatement := by
  rw [QNInterCardStatement_def]
  intro n Q Q' hQ hQ'
  have h := two_mul_qN_le_add_inter_card hQ hQ'
  have hq := qA_add_le_two_mul_qN n
  omega

/-- Two `q_N` seat sets share at least `q_A` seats. -/
theorem qN_inter_card {n : Nat} {Q Q' : Finset (Fin n)}
    (hQ : qN n ≤ Q.card) (hQ' : qN n ≤ Q'.card) : qA n ≤ (Q ∩ Q').card :=
  qN_inter_card_statement hQ hQ'

theorem qA_honest_statement : QAHonestStatement := by
  rw [QAHonestStatement_def]
  intro n A F hF hA
  by_contra hn
  have hAF : A ⊆ F := by
    intro v hv
    by_contra hvF
    exact hn ⟨v, hv, hvF⟩
  have := Finset.card_le_card hAF
  omega

/-- A set of `q_A` seats has a seat outside a set of fewer than `q_A` seats. -/
theorem qA_honest {n : Nat} {A F : Finset (Fin n)}
    (hF : F.card < qA n) (hA : qA n ≤ A.card) : ∃ v ∈ A, v ∉ F :=
  qA_honest_statement hF hA

theorem qN_inter_honest_statement : QNInterHonestStatement := by
  rw [QNInterHonestStatement_def]
  intro n Q Q' F hF hQ hQ'
  exact qA_honest hF (qN_inter_card hQ hQ')

/-- Two `q_N` seat sets share a seat outside a set of fewer than `q_A` seats. -/
theorem qN_inter_honest {n : Nat} {Q Q' F : Finset (Fin n)}
    (hF : F.card < qA n) (hQ : qN n ≤ Q.card) (hQ' : qN n ≤ Q'.card) :
    ∃ v ∈ Q ∩ Q', v ∉ F :=
  qN_inter_honest_statement hF hQ hQ'

theorem qN_head_unique_statement : QNHeadUniqueStatement := by
  rw [QNHeadUniqueStatement_def]
  intro n B sent F S S' b b' hone hF hS hS' hcS hcS'
  obtain ⟨v, hv, hvF⟩ := qN_inter_honest hF hcS hcS'
  exact hone v hvF b b' (hS v (Finset.mem_inter.mp hv).1) (hS' v (Finset.mem_inter.mp hv).2)

/-- At one slot, `q_N` exact-HEAD sets on two blocks name the same block. -/
theorem qN_head_unique {n : Nat} {B : Type} (sent : Fin n → B → Prop)
    (F S S' : Finset (Fin n)) (b b' : B)
    (hone : ∀ v, v ∉ F → ∀ x y, sent v x → sent v y → x = y) (hF : F.card < qA n)
    (hS : ∀ v ∈ S, sent v b) (hS' : ∀ v ∈ S', sent v b')
    (hcS : qN n ≤ S.card) (hcS' : qN n ≤ S'.card) : b = b' :=
  qN_head_unique_statement sent F S S' b b' hone hF hS hS' hcS hcS'

end AvailableChain.Gen.Pure
