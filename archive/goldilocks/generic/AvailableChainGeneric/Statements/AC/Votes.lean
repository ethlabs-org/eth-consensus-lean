module
public import AvailableChainGridCO.Model.Protocol
public import AvailableChainGeneric.Statements.Pure.Quorum
public import Mathlib.Data.Finset.Card -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.Gen.AC

open AvailableChain
open AvailableChain.GridCO
open AvailableChain.Gen.Pure

/-! Pool transport, candidate scores, cap admission, and batch counts.
DGF means DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish.
DS means DecoupledConsensusProofs/Protocol/Schedule.
S1a and P3 name the design records in a2design-final.md. -/

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: Model/Protocol/ForkChoice/Goldfish:97; INTENTIONAL: Use the existing resolved-block model;
record Model/Objects/Blocks:107. -/
def voteSupports {n : Nat}
    (tree : List Block) (B : Block) (o : Wire n) : Bool :=
  match headTarget? o with
  | none => false
  | some target =>
      decide (target ∈ tree) &&
      decide (target.slot ≤ (headLabel? o).getD 0) &&
      Block.preceq B target

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Defining equation. DC: Model/Protocol/ForkChoice/Goldfish:97; INTENTIONAL: Use the existing
resolved-block model; record Model/Objects/Blocks:107. -/
theorem voteSupports_def {n : Nat}
    (tree : List Block) (B : Block) (o : Wire n) :
    voteSupports tree B o =
    (match headTarget? o with
  | none => false
  | some target =>
      decide (target ∈ tree) &&
      decide (target.slot ≤ (headLabel? o).getD 0) &&
      Block.preceq B target) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: Model/Protocol/ForkChoice/Goldfish:104; same: Read support incidence in the existing
score; record blueprint/02-clean.md:380. -/
def poolSupports {n : Nat}
    (tree : List Block) (support : List (Wire n))
    (i : Fin n) (B : Block) : Bool :=
  (seatVotes support i).any (voteSupports tree B)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Defining equation. DC: Model/Protocol/ForkChoice/Goldfish:104; same: Read support incidence in
the existing score; record blueprint/02-clean.md:380. -/
theorem poolSupports_def {n : Nat}
    (tree : List Block) (support : List (Wire n))
    (i : Fin n) (B : Block) :
    poolSupports tree support i B =
    ((seatVotes support i).any (voteSupports tree B)) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: Model/Protocol/ForkChoice/Goldfish:104; same: Exclude equivocators from plain support;
record blueprint/02-clean.md:339. -/
def plainSupporters {n : Nat}
    (tree : List Block) (raw support : List (Wire n))
    (B : Block) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    equivocates raw i = false ∧
    poolSupports tree support i B = true)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Defining equation. DC: Model/Protocol/ForkChoice/Goldfish:104; same: Exclude equivocators from
plain support; record blueprint/02-clean.md:339. -/
theorem plainSupporters_def {n : Nat}
    (tree : List Block) (raw support : List (Wire n))
    (B : Block) :
    plainSupporters tree raw support B =
    (Finset.univ.filter (fun i =>
    equivocates raw i = false ∧
    poolSupports tree support i B = true)) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: DGF/Adoption:104,128,158,311; INTENTIONAL: Collect the transport and count facts; record
blueprint/02-clean.md:339. -/
def TransferBounds {n : Nat}
    (P : Finset (Fin n)) (late : List (Wire n))
    (tree : List Block) (raw support : List (Wire n))
    (B : Block) : Prop :=
  P ⊆ plainSupporters tree raw support B ∧
  voterCount raw < 2 * (plainSupporters tree raw support B).card ∧
  P.card ≤ goldfishScore tree raw support B ∧
  (∀ C, Block.compatible B C = false →
    P.card + goldfishScore tree raw support C ≤ voterCount late) ∧
  voterCount raw ≤ voterCount late ∧
  voterCount raw < 2 * goldfishScore tree raw support B ∧
  (∀ C, Block.compatible B C = false →
    goldfishScore tree raw support C <
      goldfishScore tree raw support B)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Defining equation. DC: DGF/Adoption:104,128,158,311; INTENTIONAL: Collect the transport and
count facts; record blueprint/02-clean.md:339. -/
theorem TransferBounds_def {n : Nat}
    (P : Finset (Fin n)) (late : List (Wire n))
    (tree : List Block) (raw support : List (Wire n))
    (B : Block) :
    TransferBounds P late tree raw support B =
    (P ⊆ plainSupporters tree raw support B ∧
  voterCount raw < 2 * (plainSupporters tree raw support B).card ∧
  P.card ≤ goldfishScore tree raw support B ∧
  (∀ C, Block.compatible B C = false →
    P.card + goldfishScore tree raw support C ≤ voterCount late) ∧
  voterCount raw ≤ voterCount late ∧
  voterCount raw < 2 * goldfishScore tree raw support B ∧
  (∀ C, Block.compatible B C = false →
    goldfishScore tree raw support C <
      goldfishScore tree raw support B)) := by rfl

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: DGF/Confirmation:112,152,169; INTENTIONAL: Use atomic pool premises and combined bounds;
record blueprint/02-clean.md:330. -/
def TransferStatement : Prop :=
  ∀ {n : Nat}
    (sourceTree targetTree : List Block)
    (P L U V : List (Wire n)) (B : Block)
    (hPL : P ⊆ L)
    (hclean : ∀ o ∈ P, ∀ i, headSeat? o = some i →
      equivocates L i = false)
    (hforward : ∀ o ∈ P, ∀ i, headSeat? o = some i →
      voteSupports sourceTree B o = true →
      (o ∈ V ∧ voteSupports targetTree B o = true) ∨
        equivocates U i = true)
    (hbackward : ∀ o ∈ U, ∀ i, headSeat? o = some i →
      o ∈ L ∨ equivocates L i = true)
    (hsupport : V ⊆ U)
    (hmajority :
      voterCount L < 2 * goldfishScore sourceTree P P B),
    TransferBounds (plainSupporters sourceTree P P B)
      L targetTree U V B

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Defining equation. DC: DGF/Confirmation:112,152,169; INTENTIONAL: Use atomic pool premises and
combined bounds; record blueprint/02-clean.md:330. -/
theorem TransferStatement_def : TransferStatement =
    (∀ {n : Nat}
    (sourceTree targetTree : List Block)
    (P L U V : List (Wire n)) (B : Block)
    (hPL : P ⊆ L)
    (hclean : ∀ o ∈ P, ∀ i, headSeat? o = some i →
      equivocates L i = false)
    (hforward : ∀ o ∈ P, ∀ i, headSeat? o = some i →
      voteSupports sourceTree B o = true →
      (o ∈ V ∧ voteSupports targetTree B o = true) ∨
        equivocates U i = true)
    (hbackward : ∀ o ∈ U, ∀ i, headSeat? o = some i →
      o ∈ L ∨ equivocates L i = true)
    (hsupport : V ⊆ U)
    (hmajority :
      voterCount L < 2 * goldfishScore sourceTree P P B),
    TransferBounds (plainSupporters sourceTree P P B)
      L targetTree U V B) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: DGF/Confirmation:494,508,567; INTENTIONAL: Keep denominator and score pools separate;
record S1a:327. -/
def BatchBounds {n : Nat}
    (tree : List Block) (D raw support : List (Wire n))
    (Hon : Finset (Fin n)) (h m : Nat) (X : Block) : Prop :=
  Hon ⊆ plainSupporters tree raw support X ∧
  voterCount D ≤ h + m ∧
  (∀ Y, Block.Preceq Y X →
    h ≤ goldfishScore tree raw support Y ∧
    voterCount D < 2 * goldfishScore tree raw support Y) ∧
  (∀ C, Block.compatible X C = false →
    goldfishScore tree raw support C ≤ m) ∧
  (∀ C, (∀ i ∈ Hon, poolSupports tree support i C = false) →
    2 * goldfishScore tree raw support C ≤ voterCount D)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Defining equation. DC: DGF/Confirmation:494,508,567; INTENTIONAL: Keep denominator and score
pools separate; record S1a:327. -/
theorem BatchBounds_def {n : Nat}
    (tree : List Block) (D raw support : List (Wire n))
    (Hon : Finset (Fin n)) (h m : Nat) (X : Block) :
    BatchBounds tree D raw support Hon h m X =
    (Hon ⊆ plainSupporters tree raw support X ∧
  voterCount D ≤ h + m ∧
  (∀ Y, Block.Preceq Y X →
    h ≤ goldfishScore tree raw support Y ∧
    voterCount D < 2 * goldfishScore tree raw support Y) ∧
  (∀ C, Block.compatible X C = false →
    goldfishScore tree raw support C ≤ m) ∧
  (∀ C, (∀ i ∈ Hon, poolSupports tree support i C = false) →
    2 * goldfishScore tree raw support C ≤ voterCount D)) := by rfl

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: DGF/Confirmation:494,508,567; INTENTIONAL: Use separate honest support and count facts;
record S1a:327. -/
def BatchCountsStatement : Prop :=
  ∀ {n : Nat}
    (tree : List Block) (D raw support : List (Wire n))
    (Hon : Finset (Fin n)) (h m : Nat) (X : Block)
    (hraw : raw ⊆ D)
    (hsupport : support ⊆ raw)
    (hcard : Hon.card = h)
    (hclean : ∀ i ∈ Hon, equivocates raw i = false)
    (hbatch : ∀ i ∈ Hon, poolSupports tree support i X = true)
    (hother : ((seats n D).toFinset \ Hon).card ≤ m)
    (hb : Batch h m),
    BatchBounds tree D raw support Hon h m X

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Defining equation. DC: DGF/Confirmation:494,508,567; INTENTIONAL: Use separate honest support
and count facts; record S1a:327. -/
theorem BatchCountsStatement_def : BatchCountsStatement =
    (∀ {n : Nat}
    (tree : List Block) (D raw support : List (Wire n))
    (Hon : Finset (Fin n)) (h m : Nat) (X : Block)
    (hraw : raw ⊆ D)
    (hsupport : support ⊆ raw)
    (hcard : Hon.card = h)
    (hclean : ∀ i ∈ Hon, equivocates raw i = false)
    (hbatch : ∀ i ∈ Hon, poolSupports tree support i X = true)
    (hother : ((seats n D).toFinset \ Hon).card ≤ m)
    (hb : Batch h m),
    BatchBounds tree D raw support Hon h m X) := by rfl

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: DGF/Confirmation:494,508; DGF/Adoption:311,334; INTENTIONAL: Honest non-equivocation
replaces backward relay; record P3:2554. -/
def TransferN2Statement : Prop :=
  ∀ {n : Nat}
    (tree : List Block) (raw support : List (Wire n))
    (Hon : Finset (Fin n)) (h a : Nat) (Q : Block)
    (hsupport : support ⊆ raw)
    (hcard : Hon.card = h)
    (hclean : ∀ i ∈ Hon, equivocates raw i = false)
    (hbatch : ∀ i ∈ Hon, poolSupports tree support i Q = true)
    (hother : ((seats n raw).toFinset \ Hon).card ≤ a)
    (ha : a < h),
    h ≤ (plainSupporters tree raw support Q).card ∧
    h ≤ goldfishScore tree raw support Q ∧
    voterCount raw ≤ h + a ∧
    h + a < 2 * h ∧
    (∀ C, Block.compatible Q C = false →
      goldfishScore tree raw support C ≤ a) ∧
    voterCount raw < 2 * goldfishScore tree raw support Q ∧
    (∀ C, Block.compatible Q C = false →
      goldfishScore tree raw support C <
        goldfishScore tree raw support Q)

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Defining equation. DC: DGF/Confirmation:494,508; DGF/Adoption:311,334; INTENTIONAL: Honest
non-equivocation replaces backward relay; record P3:2554. -/
theorem TransferN2Statement_def : TransferN2Statement =
    (∀ {n : Nat}
    (tree : List Block) (raw support : List (Wire n))
    (Hon : Finset (Fin n)) (h a : Nat) (Q : Block)
    (hsupport : support ⊆ raw)
    (hcard : Hon.card = h)
    (hclean : ∀ i ∈ Hon, equivocates raw i = false)
    (hbatch : ∀ i ∈ Hon, poolSupports tree support i Q = true)
    (hother : ((seats n raw).toFinset \ Hon).card ≤ a)
    (ha : a < h),
    h ≤ (plainSupporters tree raw support Q).card ∧
    h ≤ goldfishScore tree raw support Q ∧
    voterCount raw ≤ h + a ∧
    h + a < 2 * h ∧
    (∀ C, Block.compatible Q C = false →
      goldfishScore tree raw support C ≤ a) ∧
    voterCount raw < 2 * goldfishScore tree raw support Q ∧
    (∀ C, Block.compatible Q C = false →
      goldfishScore tree raw support C <
        goldfishScore tree raw support Q)) := by rfl

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: DS/ProposalSnapshot:65,223,239,257; DGF/ProposalSnapshotBridge:210; INTENTIONAL: Use
candidate incidence when support inclusion fails; record blueprint/02-clean.md:390. -/
def ScoreEqOnStatement : Prop :=
  ∀ {n : Nat}
    (tree tree' : List Block)
    (U U' support support' : List (Wire n))
    (Cand : Set Block)
    (hraw : U ⊆ U')
    (hextra : ∀ o ∈ U', ∀ i, headSeat? o = some i →
      o ∉ U → equivocates U i = true)
    (hinc : ∀ B ∈ Cand, ∀ i, equivocates U i = false →
      poolSupports tree support i B =
        poolSupports tree' support' i B),
    (seats n U).toFinset = (seats n U').toFinset ∧
    (∀ i, equivocates U i = equivocates U' i) ∧
    voterCount U = voterCount U' ∧
    (∀ B ∈ Cand,
      goldfishScore tree U support B =
        goldfishScore tree' U' support' B)

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Defining equation. DC: DS/ProposalSnapshot:65,223,239,257; DGF/ProposalSnapshotBridge:210;
INTENTIONAL: Use candidate incidence when support inclusion fails; record
blueprint/02-clean.md:390. -/
theorem ScoreEqOnStatement_def : ScoreEqOnStatement =
    (∀ {n : Nat}
    (tree tree' : List Block)
    (U U' support support' : List (Wire n))
    (Cand : Set Block)
    (hraw : U ⊆ U')
    (hextra : ∀ o ∈ U', ∀ i, headSeat? o = some i →
      o ∉ U → equivocates U i = true)
    (hinc : ∀ B ∈ Cand, ∀ i, equivocates U i = false →
      poolSupports tree support i B =
        poolSupports tree' support' i B),
    (seats n U).toFinset = (seats n U').toFinset ∧
    (∀ i, equivocates U i = equivocates U' i) ∧
    voterCount U = voterCount U' ∧
    (∀ B ∈ Cand,
      goldfishScore tree U support B =
        goldfishScore tree' U' support' B)) := by rfl

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: DS/AdoptionTransport:157; INTENTIONAL: Separate pool admission from timely settlement;
record S1a:892,931. -/
def CapVoteStatement : Prop :=
  ∀ (p : GridCO.Params) {n : Nat}
    (st : GridCO.State n) (s : Slot) (i : Fin n) (B : Block)
    (hlo : (st.now / (4 * p.Δ)).toNat - 1 ≤ s)
    (hhi : s ≤ (st.now / (4 * p.Δ)).toNat),
    let o : GridCO.Wire n := ⟨.seat s i, .head B⟩
    o ∈ (GridCO.admitVote p st o).votes ∨
      GridCO.equivocates
        (GridCO.votesAt (GridCO.admitVote p st o) s) i = true

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Defining equation. DC: DS/AdoptionTransport:157; INTENTIONAL: Separate pool admission from
timely settlement; record S1a:892,931. -/
theorem CapVoteStatement_def : CapVoteStatement =
    (∀ (p : GridCO.Params) {n : Nat}
    (st : GridCO.State n) (s : Slot) (i : Fin n) (B : Block)
    (hlo : (st.now / (4 * p.Δ)).toNat - 1 ≤ s)
    (hhi : s ≤ (st.now / (4 * p.Δ)).toNat),
    let o : GridCO.Wire n := ⟨.seat s i, .head B⟩
    o ∈ (GridCO.admitVote p st o).votes ∨
      GridCO.equivocates
        (GridCO.votesAt (GridCO.admitVote p st o) s) i = true) := by rfl

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: Model/Protocol/Schedule:99; same: Two distinct HEADs give the finite-pool cap test; record
S1a:931. -/
def CapPairStatement : Prop :=
  ∀ {n : Nat} (pool : List (GridCO.Wire n)) (i : Fin n),
    GridCO.equivocates pool i = true ↔
      ∃ u ∈ pool, ∃ v ∈ pool,
        u ≠ v ∧
        GridCO.headSeat? u = some i ∧
        GridCO.headSeat? v = some i

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Defining equation. DC: Model/Protocol/Schedule:99; same: Two distinct HEADs give the finite-
pool cap test; record S1a:931. -/
theorem CapPairStatement_def : CapPairStatement =
    (∀ {n : Nat} (pool : List (GridCO.Wire n)) (i : Fin n),
    GridCO.equivocates pool i = true ↔
      ∃ u ∈ pool, ∃ v ∈ pool,
        u ≠ v ∧
        GridCO.headSeat? u = some i ∧
        GridCO.headSeat? v = some i) := by rfl

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: DGF/Confirmation:494,508; DGF/Adoption:415; INTENTIONAL: Common-prefix heads need an
eligible compatible anchor; record blueprint/02-clean.md:86; P3:4866. -/
def BatchStatement : Prop :=
  ∀ {n : Nat}
    (tree : List Block) (D raw support : List (Wire n))
    (Hon : Finset (Fin n)) (h m : Nat) (anchor X : Block)
    (hraw : raw ⊆ D)
    (hsupport : support ⊆ raw)
    (hcard : Hon.card = h)
    (hclean : ∀ i ∈ Hon, equivocates raw i = false)
    (hbatch : ∀ i ∈ Hon, poolSupports tree support i X = true)
    (hother : ((seats n D).toFinset \ Hon).card ≤ m)
    (hb : Batch h m)
    (hcompatible : Block.Compatible anchor X)
    (hpath : ∀ C, Block.Prec anchor C → Block.Preceq C X →
      C ∈ tree)
    (hanchor :
      voterCount D < 2 * goldfishScore tree raw support anchor),
    let score := goldfishScore tree raw support
    let eligible := fun B => decide (voterCount D < 2 * score B)
    BatchBounds tree D raw support Hon h m X ∧
      Block.Preceq X (GridCO.ghost anchor tree score eligible) ∧
      eligible (GridCO.ghost anchor tree score eligible) = true

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Defining equation. DC: DGF/Confirmation:494,508; DGF/Adoption:415; INTENTIONAL: Common-prefix
heads need an eligible compatible anchor; record blueprint/02-clean.md:86; P3:4866. -/
theorem BatchStatement_def : BatchStatement =
    (∀ {n : Nat}
    (tree : List Block) (D raw support : List (Wire n))
    (Hon : Finset (Fin n)) (h m : Nat) (anchor X : Block)
    (hraw : raw ⊆ D)
    (hsupport : support ⊆ raw)
    (hcard : Hon.card = h)
    (hclean : ∀ i ∈ Hon, equivocates raw i = false)
    (hbatch : ∀ i ∈ Hon, poolSupports tree support i X = true)
    (hother : ((seats n D).toFinset \ Hon).card ≤ m)
    (hb : Batch h m)
    (hcompatible : Block.Compatible anchor X)
    (hpath : ∀ C, Block.Prec anchor C → Block.Preceq C X →
      C ∈ tree)
    (hanchor :
      voterCount D < 2 * goldfishScore tree raw support anchor),
    let score := goldfishScore tree raw support
    let eligible := fun B => decide (voterCount D < 2 * score B)
    BatchBounds tree D raw support Hon h m X ∧
      Block.Preceq X (GridCO.ghost anchor tree score eligible) ∧
      eligible (GridCO.ghost anchor tree score eligible) = true) := by rfl

namespace Root

/-- [ROOT-DIGEST-2 W1; DC Goldfish.find?] Read the body resolved in this support domain. -/
def resolvedTarget? {n : Nat} (tree : List Block) (o : Wire n .root) : Option Block :=
  (headTarget? o).bind (Block.findByRoot? tree)

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: Model/Protocol/ForkChoice/Goldfish:97; INTENTIONAL: Use the existing resolved-block model;
record Model/Objects/Blocks:107. -/
def voteSupports {n : Nat}
    (tree : List Block) (B : Block) (o : Wire n .root) : Bool :=
  match resolvedTarget? tree o with
  | none => false
  | some target =>
      decide (target ∈ tree) &&
      decide (target.slot ≤ (headLabel? o).getD 0) &&
      Block.preceq B target

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
Defining equation. DC: Model/Protocol/ForkChoice/Goldfish:97; INTENTIONAL: Use the existing
resolved-block model; record Model/Objects/Blocks:107. -/
theorem voteSupports_def {n : Nat}
    (tree : List Block) (B : Block) (o : Wire n .root) :
    voteSupports tree B o =
    (match resolvedTarget? tree o with
  | none => false
  | some target =>
      decide (target ∈ tree) &&
      decide (target.slot ≤ (headLabel? o).getD 0) &&
      Block.preceq B target) := by rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: Model/Protocol/ForkChoice/Goldfish:104; same: Read support incidence in the existing
score; record blueprint/02-clean.md:380. -/
def poolSupports {n : Nat}
    (tree : List Block) (support : List (Wire n .root))
    (i : Fin n) (B : Block) : Bool :=
  (seatVotes support i).any (voteSupports tree B)

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
Defining equation. DC: Model/Protocol/ForkChoice/Goldfish:104; same: Read support incidence in
the existing score; record blueprint/02-clean.md:380. -/
theorem poolSupports_def {n : Nat}
    (tree : List Block) (support : List (Wire n .root))
    (i : Fin n) (B : Block) :
    poolSupports tree support i B =
    ((seatVotes support i).any (voteSupports tree B)) := by rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: Model/Protocol/ForkChoice/Goldfish:104; same: Exclude equivocators from plain support;
record blueprint/02-clean.md:339. -/
def plainSupporters {n : Nat}
    (tree : List Block) (raw support : List (Wire n .root))
    (B : Block) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    equivocates raw i = false ∧
    poolSupports tree support i B = true)

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
Defining equation. DC: Model/Protocol/ForkChoice/Goldfish:104; same: Exclude equivocators from
plain support; record blueprint/02-clean.md:339. -/
theorem plainSupporters_def {n : Nat}
    (tree : List Block) (raw support : List (Wire n .root))
    (B : Block) :
    plainSupporters tree raw support B =
    (Finset.univ.filter (fun i =>
    equivocates raw i = false ∧
    poolSupports tree support i B = true)) := by rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DGF/Adoption:104,128,158,311; INTENTIONAL: Collect the transport and count facts; record
blueprint/02-clean.md:339. -/
def TransferBounds {n : Nat}
    (P : Finset (Fin n)) (late : List (Wire n .root))
    (tree : List Block) (raw support : List (Wire n .root))
    (B : Block) : Prop :=
  P ⊆ plainSupporters tree raw support B ∧
  voterCount raw < 2 * (plainSupporters tree raw support B).card ∧
  P.card ≤ goldfishScore tree raw support B ∧
  (∀ C, Block.compatible B C = false →
    P.card + goldfishScore tree raw support C ≤ voterCount late) ∧
  voterCount raw ≤ voterCount late ∧
  voterCount raw < 2 * goldfishScore tree raw support B ∧
  (∀ C, Block.compatible B C = false →
    goldfishScore tree raw support C <
      goldfishScore tree raw support B)

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
Defining equation. DC: DGF/Adoption:104,128,158,311; INTENTIONAL: Collect the transport and
count facts; record blueprint/02-clean.md:339. -/
theorem TransferBounds_def {n : Nat}
    (P : Finset (Fin n)) (late : List (Wire n .root))
    (tree : List Block) (raw support : List (Wire n .root))
    (B : Block) :
    TransferBounds P late tree raw support B =
    (P ⊆ plainSupporters tree raw support B ∧
  voterCount raw < 2 * (plainSupporters tree raw support B).card ∧
  P.card ≤ goldfishScore tree raw support B ∧
  (∀ C, Block.compatible B C = false →
    P.card + goldfishScore tree raw support C ≤ voterCount late) ∧
  voterCount raw ≤ voterCount late ∧
  voterCount raw < 2 * goldfishScore tree raw support B ∧
  (∀ C, Block.compatible B C = false →
    goldfishScore tree raw support C <
      goldfishScore tree raw support B)) := by rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DGF/Confirmation:112,152,169; INTENTIONAL: Use atomic pool premises and combined bounds;
record blueprint/02-clean.md:330. -/
def TransferStatement : Prop :=
  ∀ {n : Nat}
    (sourceTree targetTree : List Block)
    (P L U V : List (Wire n .root)) (B : Block)
    (_hPL : P ⊆ L)
    (_hclean : ∀ o ∈ P, ∀ i, headSeat? o = some i →
      equivocates L i = false)
    (_hforward : ∀ o ∈ P, ∀ i, headSeat? o = some i →
      voteSupports sourceTree B o = true →
      (o ∈ V ∧ voteSupports targetTree B o = true) ∨
        equivocates U i = true)
    (_hbackward : ∀ o ∈ U, ∀ i, headSeat? o = some i →
      o ∈ L ∨ equivocates L i = true)
    (_hsupport : V ⊆ U)
    (_hmajority :
      voterCount L < 2 * goldfishScore sourceTree P P B),
    TransferBounds (plainSupporters sourceTree P P B)
      L targetTree U V B

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
Defining equation. DC: DGF/Confirmation:112,152,169; INTENTIONAL: Use atomic pool premises and
combined bounds; record blueprint/02-clean.md:330. -/
theorem TransferStatement_def : TransferStatement =
    (∀ {n : Nat}
    (sourceTree targetTree : List Block)
    (P L U V : List (Wire n .root)) (B : Block)
    (_hPL : P ⊆ L)
    (_hclean : ∀ o ∈ P, ∀ i, headSeat? o = some i →
      equivocates L i = false)
    (_hforward : ∀ o ∈ P, ∀ i, headSeat? o = some i →
      voteSupports sourceTree B o = true →
      (o ∈ V ∧ voteSupports targetTree B o = true) ∨
        equivocates U i = true)
    (_hbackward : ∀ o ∈ U, ∀ i, headSeat? o = some i →
      o ∈ L ∨ equivocates L i = true)
    (_hsupport : V ⊆ U)
    (_hmajority :
      voterCount L < 2 * goldfishScore sourceTree P P B),
    TransferBounds (plainSupporters sourceTree P P B)
      L targetTree U V B) := by rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DGF/Confirmation:494,508,567; INTENTIONAL: Keep denominator and score pools separate;
record S1a:327. -/
def BatchBounds {n : Nat}
    (tree : List Block) (D raw support : List (Wire n .root))
    (Hon : Finset (Fin n)) (h m : Nat) (X : Block) : Prop :=
  Hon ⊆ plainSupporters tree raw support X ∧
  voterCount D ≤ h + m ∧
  (∀ Y, Block.Preceq Y X →
    h ≤ goldfishScore tree raw support Y ∧
    voterCount D < 2 * goldfishScore tree raw support Y) ∧
  (∀ C, Block.compatible X C = false →
    goldfishScore tree raw support C ≤ m) ∧
  (∀ C, (∀ i ∈ Hon, poolSupports tree support i C = false) →
    2 * goldfishScore tree raw support C ≤ voterCount D)

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
Defining equation. DC: DGF/Confirmation:494,508,567; INTENTIONAL: Keep denominator and score
pools separate; record S1a:327. -/
theorem BatchBounds_def {n : Nat}
    (tree : List Block) (D raw support : List (Wire n .root))
    (Hon : Finset (Fin n)) (h m : Nat) (X : Block) :
    BatchBounds tree D raw support Hon h m X =
    (Hon ⊆ plainSupporters tree raw support X ∧
  voterCount D ≤ h + m ∧
  (∀ Y, Block.Preceq Y X →
    h ≤ goldfishScore tree raw support Y ∧
    voterCount D < 2 * goldfishScore tree raw support Y) ∧
  (∀ C, Block.compatible X C = false →
    goldfishScore tree raw support C ≤ m) ∧
  (∀ C, (∀ i ∈ Hon, poolSupports tree support i C = false) →
    2 * goldfishScore tree raw support C ≤ voterCount D)) := by rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DGF/Confirmation:494,508,567; INTENTIONAL: Use separate honest support and count facts;
record S1a:327. -/
def BatchCountsStatement : Prop :=
  ∀ {n : Nat}
    (tree : List Block) (D raw support : List (Wire n .root))
    (Hon : Finset (Fin n)) (h m : Nat) (X : Block)
    (_hraw : raw ⊆ D)
    (_hsupport : support ⊆ raw)
    (_hcard : Hon.card = h)
    (_hclean : ∀ i ∈ Hon, equivocates raw i = false)
    (_hbatch : ∀ i ∈ Hon, poolSupports tree support i X = true)
    (_hother : ((seats n D).toFinset \ Hon).card ≤ m)
    (_hb : Batch h m),
    BatchBounds tree D raw support Hon h m X

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
Defining equation. DC: DGF/Confirmation:494,508,567; INTENTIONAL: Use separate honest support
and count facts; record S1a:327. -/
theorem BatchCountsStatement_def : BatchCountsStatement =
    (∀ {n : Nat}
    (tree : List Block) (D raw support : List (Wire n .root))
    (Hon : Finset (Fin n)) (h m : Nat) (X : Block)
    (_hraw : raw ⊆ D)
    (_hsupport : support ⊆ raw)
    (_hcard : Hon.card = h)
    (_hclean : ∀ i ∈ Hon, equivocates raw i = false)
    (_hbatch : ∀ i ∈ Hon, poolSupports tree support i X = true)
    (_hother : ((seats n D).toFinset \ Hon).card ≤ m)
    (_hb : Batch h m),
    BatchBounds tree D raw support Hon h m X) := by rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DGF/Confirmation:494,508; DGF/Adoption:311,334; INTENTIONAL: Honest non-equivocation
replaces backward relay; record P3:2554. -/
def TransferN2Statement : Prop :=
  ∀ {n : Nat}
    (tree : List Block) (raw support : List (Wire n .root))
    (Hon : Finset (Fin n)) (h a : Nat) (Q : Block)
    (_hsupport : support ⊆ raw)
    (_hcard : Hon.card = h)
    (_hclean : ∀ i ∈ Hon, equivocates raw i = false)
    (_hbatch : ∀ i ∈ Hon, poolSupports tree support i Q = true)
    (_hother : ((seats n raw).toFinset \ Hon).card ≤ a)
    (_ha : a < h),
    h ≤ (plainSupporters tree raw support Q).card ∧
    h ≤ goldfishScore tree raw support Q ∧
    voterCount raw ≤ h + a ∧
    h + a < 2 * h ∧
    (∀ C, Block.compatible Q C = false →
      goldfishScore tree raw support C ≤ a) ∧
    voterCount raw < 2 * goldfishScore tree raw support Q ∧
    (∀ C, Block.compatible Q C = false →
      goldfishScore tree raw support C <
        goldfishScore tree raw support Q)

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
Defining equation. DC: DGF/Confirmation:494,508; DGF/Adoption:311,334; INTENTIONAL: Honest
non-equivocation replaces backward relay; record P3:2554. -/
theorem TransferN2Statement_def : TransferN2Statement =
    (∀ {n : Nat}
    (tree : List Block) (raw support : List (Wire n .root))
    (Hon : Finset (Fin n)) (h a : Nat) (Q : Block)
    (_hsupport : support ⊆ raw)
    (_hcard : Hon.card = h)
    (_hclean : ∀ i ∈ Hon, equivocates raw i = false)
    (_hbatch : ∀ i ∈ Hon, poolSupports tree support i Q = true)
    (_hother : ((seats n raw).toFinset \ Hon).card ≤ a)
    (_ha : a < h),
    h ≤ (plainSupporters tree raw support Q).card ∧
    h ≤ goldfishScore tree raw support Q ∧
    voterCount raw ≤ h + a ∧
    h + a < 2 * h ∧
    (∀ C, Block.compatible Q C = false →
      goldfishScore tree raw support C ≤ a) ∧
    voterCount raw < 2 * goldfishScore tree raw support Q ∧
    (∀ C, Block.compatible Q C = false →
      goldfishScore tree raw support C <
        goldfishScore tree raw support Q)) := by rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DS/ProposalSnapshot:65,223,239,257; DGF/ProposalSnapshotBridge:210; INTENTIONAL: Use
candidate incidence when support inclusion fails; record blueprint/02-clean.md:390. -/
def ScoreEqOnStatement : Prop :=
  ∀ {n : Nat}
    (tree tree' : List Block)
    (U U' support support' : List (Wire n .root))
    (Cand : Set Block)
    (_hraw : U ⊆ U')
    (_hextra : ∀ o ∈ U', ∀ i, headSeat? o = some i →
      o ∉ U → equivocates U i = true)
    (_hinc : ∀ B ∈ Cand, ∀ i, equivocates U i = false →
      poolSupports tree support i B =
        poolSupports tree' support' i B),
    (seats n U).toFinset = (seats n U').toFinset ∧
    (∀ i, equivocates U i = equivocates U' i) ∧
    voterCount U = voterCount U' ∧
    (∀ B ∈ Cand,
      goldfishScore tree U support B =
        goldfishScore tree' U' support' B)

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
Defining equation. DC: DS/ProposalSnapshot:65,223,239,257; DGF/ProposalSnapshotBridge:210;
INTENTIONAL: Use candidate incidence when support inclusion fails; record
blueprint/02-clean.md:390. -/
theorem ScoreEqOnStatement_def : ScoreEqOnStatement =
    (∀ {n : Nat}
    (tree tree' : List Block)
    (U U' support support' : List (Wire n .root))
    (Cand : Set Block)
    (_hraw : U ⊆ U')
    (_hextra : ∀ o ∈ U', ∀ i, headSeat? o = some i →
      o ∉ U → equivocates U i = true)
    (_hinc : ∀ B ∈ Cand, ∀ i, equivocates U i = false →
      poolSupports tree support i B =
        poolSupports tree' support' i B),
    (seats n U).toFinset = (seats n U').toFinset ∧
    (∀ i, equivocates U i = equivocates U' i) ∧
    voterCount U = voterCount U' ∧
    (∀ B ∈ Cand,
      goldfishScore tree U support B =
        goldfishScore tree' U' support' B)) := by rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DS/AdoptionTransport:157; INTENTIONAL: Separate pool admission from timely settlement;
record S1a:892,931. -/
def CapVoteStatement : Prop :=
  ∀ (p : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (s : Slot) (i : Fin n) (B : BlockId)
    (_hlo : (st.now / (4 * p.Δ)).toNat - 1 ≤ s)
    (_hhi : s ≤ (st.now / (4 * p.Δ)).toNat),
    let o : GridCO.Wire n .root := ⟨.seat s i, .head B⟩
    o ∈ (GridCO.admitVote p st o).votes ∨
      GridCO.equivocates
        (GridCO.votesAt (GridCO.admitVote p st o) s) i = true

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
Defining equation. DC: DS/AdoptionTransport:157; INTENTIONAL: Separate pool admission from
timely settlement; record S1a:892,931. -/
theorem CapVoteStatement_def : CapVoteStatement =
    (∀ (p : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (s : Slot) (i : Fin n) (B : BlockId)
    (_hlo : (st.now / (4 * p.Δ)).toNat - 1 ≤ s)
    (_hhi : s ≤ (st.now / (4 * p.Δ)).toNat),
    let o : GridCO.Wire n .root := ⟨.seat s i, .head B⟩
    o ∈ (GridCO.admitVote p st o).votes ∨
      GridCO.equivocates
        (GridCO.votesAt (GridCO.admitVote p st o) s) i = true) := by rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: Model/Protocol/Schedule:99; same: Two distinct HEADs give the finite-pool cap test; record
S1a:931. -/
def CapPairStatement : Prop :=
  ∀ {n : Nat} (pool : List (GridCO.Wire n .root)) (i : Fin n),
    GridCO.equivocates pool i = true ↔
      ∃ u ∈ pool, ∃ v ∈ pool,
        u ≠ v ∧
        GridCO.headSeat? u = some i ∧
        GridCO.headSeat? v = some i

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
Defining equation. DC: Model/Protocol/Schedule:99; same: Two distinct HEADs give the finite-
pool cap test; record S1a:931. -/
theorem CapPairStatement_def : CapPairStatement =
    (∀ {n : Nat} (pool : List (GridCO.Wire n .root)) (i : Fin n),
    GridCO.equivocates pool i = true ↔
      ∃ u ∈ pool, ∃ v ∈ pool,
        u ≠ v ∧
        GridCO.headSeat? u = some i ∧
        GridCO.headSeat? v = some i) := by rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
DC: DGF/Confirmation:494,508; DGF/Adoption:415; INTENTIONAL: Common-prefix heads need an
eligible compatible anchor; record blueprint/02-clean.md:86; P3:4866. -/
def BatchStatement : Prop :=
  ∀ {n : Nat}
    (tree : List Block) (D raw support : List (Wire n .root))
    (Hon : Finset (Fin n)) (h m : Nat) (anchor X : Block)
    (_hraw : raw ⊆ D)
    (_hsupport : support ⊆ raw)
    (_hcard : Hon.card = h)
    (_hclean : ∀ i ∈ Hon, equivocates raw i = false)
    (_hbatch : ∀ i ∈ Hon, poolSupports tree support i X = true)
    (_hother : ((seats n D).toFinset \ Hon).card ≤ m)
    (_hb : Batch h m)
    (_hcompatible : Block.Compatible anchor X)
    (_hpath : ∀ C, Block.Prec anchor C → Block.Preceq C X →
      C ∈ tree)
    (_hanchor :
      voterCount D < 2 * goldfishScore tree raw support anchor),
    let score := goldfishScore tree raw support
    let eligible := fun B => decide (voterCount D < 2 * score B)
    BatchBounds tree D raw support Hon h m X ∧
      Block.Preceq X (GridCO.ghost anchor tree score eligible) ∧
      eligible (GridCO.ghost anchor tree score eligible) = true

/-- [ROOT-DIGEST-2 W1; DC root HEAD support]
Defining equation. DC: DGF/Confirmation:494,508; DGF/Adoption:415; INTENTIONAL: Common-prefix
heads need an eligible compatible anchor; record blueprint/02-clean.md:86; P3:4866. -/
theorem BatchStatement_def : BatchStatement =
    (∀ {n : Nat}
    (tree : List Block) (D raw support : List (Wire n .root))
    (Hon : Finset (Fin n)) (h m : Nat) (anchor X : Block)
    (_hraw : raw ⊆ D)
    (_hsupport : support ⊆ raw)
    (_hcard : Hon.card = h)
    (_hclean : ∀ i ∈ Hon, equivocates raw i = false)
    (_hbatch : ∀ i ∈ Hon, poolSupports tree support i X = true)
    (_hother : ((seats n D).toFinset \ Hon).card ≤ m)
    (_hb : Batch h m)
    (_hcompatible : Block.Compatible anchor X)
    (_hpath : ∀ C, Block.Prec anchor C → Block.Preceq C X →
      C ∈ tree)
    (_hanchor :
      voterCount D < 2 * goldfishScore tree raw support anchor),
    let score := goldfishScore tree raw support
    let eligible := fun B => decide (voterCount D < 2 * score B)
    BatchBounds tree D raw support Hon h m X ∧
      Block.Preceq X (GridCO.ghost anchor tree score eligible) ∧
      eligible (GridCO.ghost anchor tree score eligible) = true) := by rfl

end Root

end AvailableChain.Gen.AC
