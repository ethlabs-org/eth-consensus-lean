module
public import AvailableChainSimplexFG.Objects

@[expose] public section

namespace AvailableChain.SimplexFG

-- port: DC/DecoupledConsensusModel/Protocol/ChainState.lean:59-64 (conflictsWithFinality)
/-- The height-pair half of E1: a height pair conflicts with a nonempty
finality pair `(h, T)` when the heights agree and the pair does not target
`T`. A timeout at `h` always conflicts with a finality pair at `h`, whatever
its target. The empty pair conflicts with nothing. -/
def conflictsWithFinality : NamedHeightPair → FinalityPair → Bool
  | .empty, _ => false
  | .vote height _ true, pair => decide (height = pair.height)
  | .vote height entry false, pair =>
      decide (height = pair.height) && !decide (entry = pair.target)

variable {V : Type} [DecidableEq V]

-- port: DC/DecoupledConsensusModel/Protocol/ChainState.lean:70-71 (sameValidator)
/-- [helper] Two rows carry the same signer. -/
def sameSigner (left right : Row V) : Bool := decide (left.signer = right.signer)

-- port: DC/DecoupledConsensusModel/Protocol/ChainState.lean:83-85 (e1Fields)
/-- E1's field conflict, before the one-signer test. Either row may supply
the finality pair; taking `left = right` is what lets the conflicting
occurrences be in one row. -/
def e1Fields (left right : Row V) : Bool :=
  left.finality_pair.elim false (conflictsWithFinality right.height_pair) ||
    right.finality_pair.elim false (conflictsWithFinality left.height_pair)

-- port: DC/DecoupledConsensusModel/Protocol/ChainState.lean:87-90 (e2Fields)
/-- E2's field conflict, before the one-signer test: two target pairs at one
height for different roots. A timeout or the empty pair on either side is
not E2 (DC `e2Fields`). -/
def e2Fields (left right : Row V) : Bool :=
  match left.height_pair, right.height_pair with
  | .vote lh lTarget false, .vote rh rTarget false =>
      decide (lh = rh) && !decide (lTarget = rTarget)
  | _, _ => false

-- port: DC/DecoupledConsensusModel/Protocol/ChainState.lean:96-97 (e1Slashable)
/-- [helper] **E1** (alfs4 lines 239–240): one finality pair is `(h, T)`, and
one height pair at `h` is a timeout or a target vote `(h, T', false)` with
`T' ≠ T`. The empty pair `(⊥, ⊥, ⊥)` is not E1. -/
def e1Slashable (left right : Row V) : Bool :=
  sameSigner left right && e1Fields left right

-- port: DC/DecoupledConsensusModel/Protocol/ChainState.lean:103-104 (e2Slashable)
/-- [helper] **E2** (alfs4 lines 241–242): two target votes are `(h, T, false)`
and `(h, T', false)` with `T ≠ T'`. A timeout or the empty pair is not E2. -/
def e2Slashable (left right : Row V) : Bool :=
  sameSigner left right && e2Fields left right

-- port: DC/DecoupledConsensusModel/Protocol/ChainState.lean:110-111 (slashable)
/-- [helper] Slashable under either condition. -/
def slashable (left right : Row V) : Bool :=
  e1Slashable left right || e2Slashable left right

-- port: DC/DecoupledConsensusModel/Protocol/ChainState.lean:122-124 (Slashable)
/-- E1 or E2, as a proposition. -/
def Slashable (left right : Row V) : Prop := slashable left right = true

instance (left right : Row V) : Decidable (Slashable left right) :=
  inferInstanceAs (Decidable (slashable left right = true))

variable [Fintype V]

-- port: DC/DecoupledConsensusModel/Protocol/Evidence.lean:59-64 (SlashableBetween)
/-- A signer `i` is slashable **between** two evidence sets: one occurrence
from each, both `i`'s, satisfying E1 or E2. `A₁ = A₂` and `a = b` are both
permitted: "the conflicting occurrences can be in one attestation" is, at
`a = b`, self-slashability. -/
def SlashableBetween (A₁ A₂ : Finset (Row V)) (i : V) : Prop :=
  ∃ a ∈ A₁, ∃ b ∈ A₂, a.signer = i ∧ b.signer = i ∧ Slashable a b

-- port: DC/DecoupledConsensusModel/Protocol/Evidence.lean:83-84 (HasIntersectionWeight)
/-- [helper] The weight floor `2q ≤ W + w(S)` for an intersection of two
quorums, written additively so no natural-number subtraction appears. -/
def HasIntersectionWeight (E : Electorate V) (S : Finset V) : Prop :=
  2 * E.q ≤ E.totalWeight + E.weightOf S

-- port: DC/DecoupledConsensusModel/Protocol/Evidence.lean:88-90 (HasSlashableWeightBetween)
/-- Slashable weight `2q − W` **between** two evidence sets: the
accountability conclusion form. -/
def HasSlashableWeightBetween (E : Electorate V) (A₁ A₂ : Finset (Row V)) : Prop :=
  ∃ S : Finset V, HasIntersectionWeight E S ∧ ∀ i ∈ S, SlashableBetween A₁ A₂ i

-- port: DC/DecoupledConsensusInternal/Derived.lean:121-124 (E2EvidenceAtHeight)
/-- [helper] One signer's E2 evidence against one fixed height and pair of
roots: `h`, `T₁` and `T₂` are parameters, bound outside the signer set, so
every counted signer convicts at the same height for the same two roots. -/
def E2EvidenceAtHeight (h : Height) (T₁ T₂ : BlockId) (A₁ A₂ : Finset (Row V))
    (i : V) : Prop :=
  ∃ a ∈ A₁, ∃ b ∈ A₂, a.signer = i ∧ b.signer = i ∧
    a.height_pair = NamedHeightPair.vote h T₁ false ∧
    b.height_pair = NamedHeightPair.vote h T₂ false

-- port: DC/DecoupledConsensusInternal/Derived.lean:129-132 (HasE2WeightAt)
/-- At least `2q − W` weight has E2 evidence at one height against two
roots. This is the conclusion type of DC `justification_unique_per_height`
(vcE:243): two target quorums at one height for different roots expose this
weight of E2 evidence. -/
def HasE2WeightAt (E : Electorate V) (h : Height) (T₁ T₂ : BlockId)
    (A₁ A₂ : Finset (Row V)) : Prop :=
  ∃ S : Finset V, HasIntersectionWeight E S ∧
    ∀ i ∈ S, E2EvidenceAtHeight h T₁ T₂ A₁ A₂ i

/-- At least `2q − W` weight has E1 evidence between two evidence sets: like
`HasSlashableWeightBetween`, but with E1 only (the conclusion form of
`fj.crossingNoFinal.v1` clause 1; Astra H03). -/
def HasE1WeightBetween (E : Electorate V) (A₁ A₂ : Finset (Row V)) : Prop :=
  ∃ S : Finset V, HasIntersectionWeight E S ∧
    ∀ i ∈ S, ∃ a ∈ A₁, ∃ b ∈ A₂, a.signer = i ∧ b.signer = i ∧ e1Slashable a b = true

/-- The empty pair conflicts with no finality pair. -/
example : conflictsWithFinality .empty ⟨2, ⟨4⟩⟩ = false := by decide
/-- A timeout at `h` conflicts with a finality pair at `h`, whatever its
target. -/
example : conflictsWithFinality (.vote 2 ⟨9⟩ true) ⟨2, ⟨4⟩⟩ = true := by decide
/-- A target vote for the finalized checkpoint itself does not conflict. -/
example : conflictsWithFinality (.vote 2 ⟨4⟩ false) ⟨2, ⟨4⟩⟩ = false := by decide
/-- A target vote for a different checkpoint at the same height conflicts. -/
example : conflictsWithFinality (.vote 2 ⟨1⟩ false) ⟨2, ⟨4⟩⟩ = true := by decide

def rowFin (i : Fin 2) (hp : NamedHeightPair) (fp : Option FinalityPair) : Row (Fin 2) :=
  ⟨i, hp, fp⟩
/-- Signer `0` finalizes `(5, ⟨9⟩)` on one row and votes target `⟨2⟩` at
height 5 on another: E1. -/
example :
    e1Slashable (rowFin 0 (.vote 3 ⟨1⟩ false) (some ⟨5, ⟨9⟩⟩))
      (rowFin 0 (.vote 5 ⟨2⟩ false) none) = true := by decide
/-- A target vote for the finalized checkpoint itself is not E1. -/
example :
    e1Slashable (rowFin 0 (.vote 3 ⟨1⟩ false) (some ⟨5, ⟨9⟩⟩))
      (rowFin 0 (.vote 5 ⟨9⟩ false) none) = false := by decide
/-- Signer `0` targets two different roots at height 5: E2. -/
example :
    e2Slashable (rowFin 0 (.vote 5 ⟨9⟩ false) none)
      (rowFin 0 (.vote 5 ⟨2⟩ false) none) = true := by decide
/-- A timeout on one side is not E2, even at a shared height. -/
example :
    e2Slashable (rowFin 0 (.vote 5 ⟨9⟩ true) none)
      (rowFin 0 (.vote 5 ⟨2⟩ false) none) = false := by decide
/-- Different signers are never slashable between each other. -/
example :
    e2Slashable (rowFin 0 (.vote 5 ⟨9⟩ false) none)
      (rowFin 1 (.vote 5 ⟨2⟩ false) none) = false := by decide

end AvailableChain.SimplexFG
end
