module
public import AvailableChainGeneric.Statements.AC.Votes -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.Gen.AC

open AvailableChain AvailableChain.GridCO

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Confirmation.lean:210;
INTENTIONAL: Use resolved blocks and retain the fixed equivocation contribution;
record blueprint/02-clean.md:354. -/
def GoldfishScoreAntitoneStatement : Prop :=
  ∀ {n : Nat} (tree : List Block) (raw support : List (Wire n)) (X B : Block),
    Block.Preceq X B →
    goldfishScore tree raw support B ≤ goldfishScore tree raw support X

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Confirmation.lean:210;
INTENTIONAL: Give the defining equation of the resolved-block score contract;
record blueprint/02-clean.md:354. -/
theorem GoldfishScoreAntitoneStatement_def : GoldfishScoreAntitoneStatement =
    (∀ {n : Nat} (tree : List Block) (raw support : List (Wire n)) (X B : Block),
      Block.Preceq X B →
      goldfishScore tree raw support B ≤ goldfishScore tree raw support X) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Adoption.lean:257;
INTENTIONAL: Use one pool without equivocators, so both scores count plain supporters;
record blueprint/02-clean.md:116. -/
def ConflictingScoreSumLeStatement : Prop :=
  ∀ {n : Nat} (tree : List Block) (pool : List (Wire n)) (B D : Block),
    (∀ i, equivocates pool i = false) →
    Block.compatible B D = false →
    goldfishScore tree pool pool B + goldfishScore tree pool pool D ≤ voterCount pool

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Adoption.lean:257;
INTENTIONAL: Give the defining equation of the pool count contract;
record blueprint/02-clean.md:116. -/
theorem ConflictingScoreSumLeStatement_def : ConflictingScoreSumLeStatement =
    (∀ {n : Nat} (tree : List Block) (pool : List (Wire n)) (B D : Block),
      (∀ i, equivocates pool i = false) →
      Block.compatible B D = false →
      goldfishScore tree pool pool B + goldfishScore tree pool pool D ≤ voterCount pool) :=
  by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Adoption.lean:128;
INTENTIONAL: Require seat inclusion directly, without a transport or run premise;
record blueprint/02-clean.md:340. -/
def VoterCountLeOfSeatsSubsetStatement : Prop :=
  ∀ {n : Nat} (pool late : List (Wire n)),
    (seats n pool).toFinset ⊆ (seats n late).toFinset → voterCount pool ≤ voterCount late

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Adoption.lean:128;
INTENTIONAL: Give the defining equation of the seat count contract;
record blueprint/02-clean.md:340. -/
theorem VoterCountLeOfSeatsSubsetStatement_def : VoterCountLeOfSeatsSubsetStatement =
    (∀ {n : Nat} (pool late : List (Wire n)),
      (seats n pool).toFinset ⊆ (seats n late).toFinset →
      voterCount pool ≤ voterCount late) := by rfl

namespace Root

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Confirmation.lean:210;
INTENTIONAL: Use resolved blocks and retain the fixed equivocation contribution;
record blueprint/02-clean.md:354. -/
def GoldfishScoreAntitoneStatement : Prop :=
  ∀ {n : Nat} (tree : List Block) (raw support : List (Wire n .root)) (X B : Block),
    Block.Preceq X B →
    goldfishScore tree raw support B ≤ goldfishScore tree raw support X

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Confirmation.lean:210;
INTENTIONAL: Give the defining equation of the resolved-block score contract;
record blueprint/02-clean.md:354. -/
theorem GoldfishScoreAntitoneStatement_def : GoldfishScoreAntitoneStatement =
    (∀ {n : Nat} (tree : List Block) (raw support : List (Wire n .root)) (X B : Block),
      Block.Preceq X B →
      goldfishScore tree raw support B ≤ goldfishScore tree raw support X) := by rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Adoption.lean:257;
INTENTIONAL: Use one pool without equivocators, so both scores count plain supporters;
record blueprint/02-clean.md:116. -/
def ConflictingScoreSumLeStatement : Prop :=
  ∀ {n : Nat} (tree : List Block) (pool : List (Wire n .root)) (B D : Block),
    (∀ i, equivocates pool i = false) →
    Block.compatible B D = false →
    goldfishScore tree pool pool B + goldfishScore tree pool pool D ≤ voterCount pool

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Adoption.lean:257;
INTENTIONAL: Give the defining equation of the pool count contract;
record blueprint/02-clean.md:116. -/
theorem ConflictingScoreSumLeStatement_def : ConflictingScoreSumLeStatement =
    (∀ {n : Nat} (tree : List Block) (pool : List (Wire n .root)) (B D : Block),
      (∀ i, equivocates pool i = false) →
      Block.compatible B D = false →
      goldfishScore tree pool pool B + goldfishScore tree pool pool D ≤ voterCount pool) :=
  by rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Adoption.lean:128;
INTENTIONAL: Require seat inclusion directly, without a transport or run premise;
record blueprint/02-clean.md:340. -/
def VoterCountLeOfSeatsSubsetStatement : Prop :=
  ∀ {n : Nat} (pool late : List (Wire n .root)),
    (seats n pool).toFinset ⊆ (seats n late).toFinset → voterCount pool ≤ voterCount late

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Adoption.lean:128;
INTENTIONAL: Give the defining equation of the seat count contract;
record blueprint/02-clean.md:340. -/
theorem VoterCountLeOfSeatsSubsetStatement_def : VoterCountLeOfSeatsSubsetStatement =
    (∀ {n : Nat} (pool late : List (Wire n .root)),
      (seats n pool).toFinset ⊆ (seats n late).toFinset →
      voterCount pool ≤ voterCount late) := by rfl

end Root

end AvailableChain.Gen.AC
