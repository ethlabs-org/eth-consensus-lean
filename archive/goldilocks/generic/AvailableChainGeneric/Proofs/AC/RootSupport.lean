module
public import AvailableChainGeneric.Statements.AC.Support
public import AvailableChainGeneric.Proofs.AC.RootVotes

-- Find matcher bodies in the two definitions; do not depend on generated names.
local elab "hygieneEq% " lhs:term:max rhs:term:max : term => do
  let left ← Lean.Elab.Term.elabTerm lhs none
  let right ← Lean.Elab.Term.elabTerm rhs none
  let a ← Lean.getConstInfo left.getAppFn.constName!
  let b ← Lean.getConstInfo right.getAppFn.constName!
  for x in a.value!.getUsedConstants do
    unless (← Lean.Meta.getMatcherInfo? x).isSome do continue
    let ex ← Lean.Meta.mkConstWithFreshMVarLevels x
    for y in b.value!.getUsedConstants do
      unless (← Lean.Meta.getMatcherInfo? y).isSome do continue
      let ey ← Lean.Meta.mkConstWithFreshMVarLevels y
      if ← Lean.Meta.isDefEq (← Lean.Meta.inferType ex) (← Lean.Meta.inferType ey) then
        if ← Lean.Meta.isDefEq ex ey then
          return ← Lean.Meta.mkEq ex ey
  throwError "No equal matcher bodies in the supplied definitions"

namespace AvailableChain.GridCO

open AvailableChain.Generic

-- ROOT-DIGEST-2 option 3: use a private copy of the same matcher (BUILD B3).
private def hygiene_goldfishScoreOn {n : Nat} {mode : HeadMode} (domain tree : List Block)
    (raw support : List (Wire n mode)) (b : Block) : Nat :=
  ((seats n raw).filter (fun i =>
    equivocates raw i || (seatVotes support i).any (fun o =>
      match headTarget? o with
      | none => false
      | some target => match resolveTarget mode domain target with
        | none => false
        | some B => decide (B ∈ tree) && decide (B.slot ≤ (headLabel? o).getD 0) &&
            Block.preceq b B))).length

-- The generated matcher bodies are definitionally equal. The module hides this helper.
theorem gen_hygiene_goldfishScoreOn_match_1_eq :
    hygieneEq% (@goldfishScoreOn) (@hygiene_goldfishScoreOn) := rfl

end AvailableChain.GridCO

namespace AvailableChain.GridCO

open AvailableChain.Generic

-- ROOT-DIGEST-2 option 3: use a private copy of the same matcher (BUILD B3).
private def hygiene_resolvedBefore {n : Nat} {mode : HeadMode}
    (st : State n mode) (o : Wire n mode) (cutoff : Time) : Bool :=
  match resolvedHead? st o with
  | none => false
  | some B => decide (B.slot ≤ (headLabel? o).getD 0) &&
      decide (stampVote st o < cutoff) && decide (stampBlock st B < cutoff)

-- The generated matcher bodies are definitionally equal. The module hides this helper.
theorem gen_hygiene_resolvedBefore_match_1_eq :
    hygieneEq% (@resolvedBefore) (@hygiene_goldfishScoreOn) := rfl

end AvailableChain.GridCO

attribute [local simp]
  AvailableChain.GridCO.gen_hygiene_goldfishScoreOn_match_1_eq
  AvailableChain.GridCO.gen_hygiene_resolvedBefore_match_1_eq

local macro "hygiene_split" : tactic =>
  `(tactic| (
    try rw [AvailableChain.GridCO.gen_hygiene_goldfishScoreOn_match_1_eq] at *;
    try rw [AvailableChain.GridCO.gen_hygiene_resolvedBefore_match_1_eq] at *;
    all_goals split))

local macro "hygiene_split" "at" h:ident : tactic =>
  `(tactic| (
    try rw [AvailableChain.GridCO.gen_hygiene_goldfishScoreOn_match_1_eq] at *;
    try rw [AvailableChain.GridCO.gen_hygiene_resolvedBefore_match_1_eq] at *;
    all_goals split at $h:ident))

public section

namespace AvailableChain.Gen.AC.Root

open AvailableChain AvailableChain.GridCO

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Confirmation.lean:210;
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

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Confirmation.lean:210;
INTENTIONAL: Use the A2 ancestry proposition for resolved blocks;
record blueprint/02-clean.md:354. -/
theorem goldfishScore_antitone {n : Nat} (tree : List Block)
    (raw support : List (Wire n HeadMode.root)) (X B : Block) (hXB : Block.Preceq X B) :
    goldfishScore tree raw support B ≤ goldfishScore tree raw support X :=
  goldfishScore_antitone_statement tree raw support X B hXB

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Confirmation.lean:210;
INTENTIONAL: Give a Boolean ancestry bridge for the resolved-block pool contract;
record blueprint/02-clean.md:354. -/
theorem goldfishScore_antitone_of_preceq {n : Nat} (tree : List Block)
    (raw support : List (Wire n HeadMode.root)) (X B : Block) (hXB : Block.preceq X B = true) :
    goldfishScore tree raw support B ≤ goldfishScore tree raw support X :=
  goldfishScore_antitone tree raw support X B hXB

-- The local notation expands to the scoreVoters set used by A2's score-card lemma.
local notation "scoreVoters" =>
  (fun {n : Nat} (tree : List Block) (raw support : List (Wire n HeadMode.root)) (B : Block) =>
    Finset.filter (fun i => (equivocates raw i || poolSupports tree support i B) = true)
      (List.toFinset (seats n raw)))

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Adoption.lean:257;
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

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Adoption.lean:257;
INTENTIONAL: Expose the equivocation-free self-pool count bound;
record blueprint/02-clean.md:116. -/
theorem conflicting_score_sum_le {n : Nat} (tree : List Block)
    (pool : List (Wire n HeadMode.root)) (B D : Block) (hclean : ∀ i, equivocates pool i = false)
    (hconf : Block.compatible B D = false) :
    goldfishScore tree pool pool B + goldfishScore tree pool pool D ≤ voterCount pool :=
  conflicting_score_sum_le_statement tree pool B D hclean hconf

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Adoption.lean:128;
INTENTIONAL: Require seat inclusion directly, without a transport or run premise;
record blueprint/02-clean.md:340. -/
theorem voterCount_le_of_seats_subset_statement : VoterCountLeOfSeatsSubsetStatement := by
  rw [VoterCountLeOfSeatsSubsetStatement_def]
  intro n pool late hsub
  rw [vote_pool_voterCount_card, vote_pool_voterCount_card]
  exact Finset.card_le_card hsub

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Adoption.lean:128;
INTENTIONAL: Expose the finite-seat count bound;
record blueprint/02-clean.md:340. -/
theorem voterCount_le_of_seats_subset {n : Nat} (pool late : List (Wire n HeadMode.root))
    (hsub : (seats n pool).toFinset ⊆ (seats n late).toFinset) :
    voterCount pool ≤ voterCount late :=
  voterCount_le_of_seats_subset_statement pool late hsub

/-- [ROOT-DIGEST-2 W1; DC fixed resolution domain] Active filtering keeps score ancestry. -/
theorem goldfishScoreOn_antitone {n : Nat} (domain tree : List Block)
    (raw support : List (Wire n .root)) (X B : Block) (hXB : Block.Preceq X B) :
    goldfishScoreOn domain tree raw support B ≤ goldfishScoreOn domain tree raw support X := by
  unfold goldfishScoreOn
  apply List.Sublist.length_le
  apply List.monotone_filter_right
  intro i hi
  rcases Bool.or_eq_true_iff.mp hi with he | hb
  · exact Bool.or_eq_true_iff.mpr (Or.inl he)
  · apply Bool.or_eq_true_iff.mpr
    right
    obtain ⟨o, ho, hv⟩ := List.any_eq_true.mp hb
    apply List.any_eq_true.mpr
    refine ⟨o, ho, ?_⟩
    hygiene_split at hv
    · contradiction
    · rename_i r hr
      hygiene_split at hv
      · contradiction
      · rename_i C hC
        simp only [Bool.and_eq_true] at hv ⊢
        exact ⟨hv.1, Gen.Pure.block_preceq_trans hXB hv.2⟩

/-- [ROOT-DIGEST-2 W1; DC fixed resolution domain] Active filtering can only remove support. -/
theorem goldfishScoreOn_le {n : Nat} (domain tree : List Block)
    (raw support : List (Wire n .root)) (B : Block) :
    goldfishScoreOn domain tree raw support B ≤ goldfishScore domain raw support B := by
  unfold goldfishScore goldfishScoreOn
  apply List.Sublist.length_le
  apply List.monotone_filter_right
  intro i hi
  rcases Bool.or_eq_true_iff.mp hi with he | hb
  · exact Bool.or_eq_true_iff.mpr (Or.inl he)
  · apply Bool.or_eq_true_iff.mpr
    right
    obtain ⟨o, ho, hv⟩ := List.any_eq_true.mp hb
    apply List.any_eq_true.mpr
    refine ⟨o, ho, ?_⟩
    hygiene_split at hv
    · contradiction
    · rename_i r hr
      hygiene_split at hv
      · contradiction
      · rename_i C hC
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hv ⊢
        exact ⟨⟨Block.findByRoot?_mem hC, hv.1.2⟩, hv.2⟩

/-- [ROOT-DIGEST-2 W1; DC fixed resolution domain] Conflicting active scores are disjoint. -/
theorem conflicting_scoreOn_sum_le {n : Nat} (domain tree : List Block)
    (pool : List (Wire n .root)) (B D : Block) (hclean : ∀ i, equivocates pool i = false)
    (hconf : Block.compatible B D = false) :
    goldfishScoreOn domain tree pool pool B + goldfishScoreOn domain tree pool pool D ≤
      voterCount pool :=
  (Nat.add_le_add (goldfishScoreOn_le domain tree pool pool B)
    (goldfishScoreOn_le domain tree pool pool D)).trans
      (conflicting_score_sum_le domain pool B D hclean hconf)

end AvailableChain.Gen.AC.Root
