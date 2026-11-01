module
public import AvailableChainGeneric.Statements.AC.Support
public import AvailableChainGeneric.Proofs.AC.Votes

public section

namespace AvailableChain.Gen.AC

open AvailableChain AvailableChain.GridCO

/-- DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Confirmation.lean:210;
INTENTIONAL: Use resolved blocks and retain the fixed equivocation contribution;
record blueprint/02-clean.md:354. -/
theorem goldfishScore_antitone_statement : GoldfishScoreAntitoneStatement := by
  rw [GoldfishScoreAntitoneStatement_def]
  intro n tree raw support X B hXB
  -- port: GridCO/Proofs/Map.lean:120; only the pool incidence core.
  rw [vote_pool_score_card, vote_pool_score_card]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hm, hs⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨hm, ?_⟩
  rcases Bool.or_eq_true_iff.mp hs with he | hb
  · exact Bool.or_eq_true_iff.mpr (Or.inl he)
  · obtain ⟨o, ho, hi, hv⟩ := (vote_pool_support_witness tree support i B).mp hb
    exact Bool.or_eq_true_iff.mpr (Or.inr
      ((vote_pool_support_witness tree support i X).mpr
        ⟨o, ho, hi, vote_pool_support_ancestor tree o hXB hv⟩))

/-- DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Confirmation.lean:210;
INTENTIONAL: Use the A2 ancestry proposition for resolved blocks;
record blueprint/02-clean.md:354. -/
theorem goldfishScore_antitone {n : Nat} (tree : List Block)
    (raw support : List (Wire n)) (X B : Block) (hXB : Block.Preceq X B) :
    goldfishScore tree raw support B ≤ goldfishScore tree raw support X :=
  goldfishScore_antitone_statement tree raw support X B hXB

/-- DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Confirmation.lean:210;
INTENTIONAL: Give a Boolean ancestry bridge for the resolved-block pool contract;
record blueprint/02-clean.md:354. -/
theorem goldfishScore_antitone_of_preceq {n : Nat} (tree : List Block)
    (raw support : List (Wire n)) (X B : Block) (hXB : Block.preceq X B = true) :
    goldfishScore tree raw support B ≤ goldfishScore tree raw support X :=
  goldfishScore_antitone tree raw support X B hXB

-- The local notation expands to the scoreVoters set used by A2's score-card lemma.
local notation "scoreVoters" =>
  (fun {n : Nat} (tree : List Block) (raw support : List (Wire n)) (B : Block) =>
    Finset.filter (fun i => (equivocates raw i || poolSupports tree support i B) = true)
      (List.toFinset (seats n raw)))

/-- DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Adoption.lean:257;
INTENTIONAL: Use one pool without equivocators, so both scores count plain supporters;
record blueprint/02-clean.md:116. -/
theorem conflicting_score_sum_le_statement : ConflictingScoreSumLeStatement := by
  rw [ConflictingScoreSumLeStatement_def]
  intro n tree pool B D hclean hconf
  -- port: GridCO/Proofs/Support.lean:60,75; only disjoint pool support and its count.
  have hdis : Disjoint (scoreVoters tree pool pool B) (scoreVoters tree pool pool D) := by
    apply Finset.disjoint_left.mpr
    intro i hb hd
    have hB := (Finset.mem_filter.mp hb).2
    have hD := (Finset.mem_filter.mp hd).2
    simp only [hclean i, Bool.false_or] at hB hD
    have hnot := vote_pool_support_conflict tree pool pool i
      (fun _ ho => ho) (hclean i) hB hconf
    simp only [hnot, Bool.false_eq_true] at hD
  rw [vote_pool_score_card, vote_pool_score_card,
    ← Finset.card_union_of_disjoint hdis, vote_pool_voterCount_card]
  exact Finset.card_le_card (Finset.union_subset
    (Finset.filter_subset _ _) (Finset.filter_subset _ _))

/-- DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Adoption.lean:257;
INTENTIONAL: Expose the equivocation-free self-pool count bound;
record blueprint/02-clean.md:116. -/
theorem conflicting_score_sum_le {n : Nat} (tree : List Block)
    (pool : List (Wire n)) (B D : Block) (hclean : ∀ i, equivocates pool i = false)
    (hconf : Block.compatible B D = false) :
    goldfishScore tree pool pool B + goldfishScore tree pool pool D ≤ voterCount pool :=
  conflicting_score_sum_le_statement tree pool B D hclean hconf

/-- DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Adoption.lean:128;
INTENTIONAL: Require seat inclusion directly, without a transport or run premise;
record blueprint/02-clean.md:340. -/
theorem voterCount_le_of_seats_subset_statement : VoterCountLeOfSeatsSubsetStatement := by
  rw [VoterCountLeOfSeatsSubsetStatement_def]
  intro n pool late hsub
  rw [vote_pool_voterCount_card, vote_pool_voterCount_card]
  exact Finset.card_le_card hsub

/-- DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Adoption.lean:128;
INTENTIONAL: Expose the finite-seat count bound;
record blueprint/02-clean.md:340. -/
theorem voterCount_le_of_seats_subset {n : Nat} (pool late : List (Wire n))
    (hsub : (seats n pool).toFinset ⊆ (seats n late).toFinset) :
    voterCount pool ≤ voterCount late :=
  voterCount_le_of_seats_subset_statement pool late hsub

end AvailableChain.Gen.AC
