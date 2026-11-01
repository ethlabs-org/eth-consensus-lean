module
public import AvailableChainPCSAProofs.Proofs.Shared.Count

public section

/-! CL4 count boundaries (pcsa34-r4.3 §5.2.1–2). The run must supply
relay membership and common resolution on the intersecting seats. -/

namespace AvailableChain.PCSA

open Gen.Pure

/-- The Generic quorum bound gives the strict score gap used after an
honest N observation, even when each equivocator scores on both sides. -/
theorem pcsa_n_score_gap {n e on off : Nat} (he : e < pcQuorum n)
    (hon : nQuorum n ≤ on) (hoff : off + nQuorum n ≤ n + e) : off < on := by
  have h := qA_add_le_two_mul_qN n
  change e < qA n at he
  change qN n ≤ on at hon
  change off + qN n ≤ n + e at hoff
  omega

/-- CL4 at the N label: a majority result and a relayed N set share a
seat. A non-equivocating common resolution makes their blocks compatible. -/
theorem pcsa_cl4_same_label {n a : Nat} (X D : Block)
    (N S L : Finset (Fin n)) (ha : a < pcQuorum n)
    (hN : nQuorum n ≤ N.card) (hNL : N ⊆ L) (hSL : S ⊆ L)
    (hS : L.card < 2 * S.card)
    (hresolve : ∀ i ∈ N ∩ S, ∃ H, Block.Preceq X H ∧ Block.Preceq D H) :
    Block.Compatible X D := by
  have hcard : L.card ≤ n := by simpa using Finset.card_le_univ L
  have hq := qA_add_le_two_mul_qN n
  change a < qA n at ha
  change qN n ≤ N.card at hN
  have hmaj : L.card < 2 * N.card := by omega
  have hsub : N ∪ S ⊆ L := Finset.union_subset hNL hSL
  obtain ⟨i, hi⟩ := two_majorities_intersect hsub hsub hmaj hS
  obtain ⟨H, hx, hd⟩ := hresolve i hi
  exact block_compatible_of_common hx hd

/-- CL4 at a later label: with more honest than faulty participants, a
majority support set contains an honest seat whose HEAD covers the target. -/
theorem pcsa_cl4_later_label {n : Nat} (X D : Block)
    (H F S L : Finset (Fin n)) (heads : Fin n → Block)
    (hHF : Disjoint H F) (hHL : H ⊆ L) (hSL : S ⊆ L)
    (hbatch : F.card < H.card) (hS : L.card < 2 * S.card)
    (hheads : ∀ i ∈ S, i ∉ F → Block.Preceq X (heads i))
    (hsupport : ∀ i ∈ S, Block.Preceq D (heads i)) : Block.Compatible X D := by
  by_cases hex : ∃ i ∈ S, i ∉ F
  · obtain ⟨i, hi, hf⟩ := hex
    exact block_compatible_of_common (hheads i hi hf) (hsupport i hi)
  · have hSF : S ⊆ F := by
      intro i hi
      by_contra hf
      exact hex ⟨i, hi, hf⟩
    have hdis : Disjoint H S := hHF.mono_right hSF
    have hcount := Finset.card_le_card (Finset.union_subset hHL hSL)
    rw [Finset.card_union_of_disjoint hdis] at hcount
    have hbound := Finset.card_le_card hSF
    omega

end AvailableChain.PCSA
end
