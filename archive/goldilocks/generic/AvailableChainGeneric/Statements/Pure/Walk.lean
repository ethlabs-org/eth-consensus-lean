module
public import Mathlib.Data.List.Basic -- shake: keep (re-export)
public import AvailableChainModel.Objects.Blocks -- shake: keep (re-export)
public import AvailableChainGridCO.Model.Walk

@[expose] public section

/-! E-4 statements only (D01). GLY is `generic-layer.md` r3.13;
P3 is `fgsa-f0-f2-plan-r3.5-2a9a5877.md`; S1 is `a0-s1-reuse-map.md`.
The premise bodies below are designs from the cited prose. The anchor need
not be in the tree, except where `AnchorClosed` itself requires this.
Only vertices strictly after the anchor have path premises. -/

namespace AvailableChain.Gen.Pure

open AvailableChain

/-- Each vertex on the suffix is present, eligible, and has a strictly
greater score than each other eligible child of its parent.
Source: GLY:667–670; P3:4396–4403. -/
def DominatedSuffix (anchor target : Block) (tree : List Block)
    (score : Block → Nat) (eligible : Block → Bool) : Prop :=
  ∀ C, Block.Prec anchor C → Block.Preceq C target →
    C ∈ tree ∧ eligible C = true ∧
      ∀ D ∈ tree, D.parent? = C.parent? → eligible D = true → D ≠ C →
        score D < score C

theorem DominatedSuffix_def (anchor target : Block) (tree : List Block)
    (score : Block → Nat) (eligible : Block → Bool) :
    DominatedSuffix anchor target tree score eligible =
      (∀ C, Block.Prec anchor C → Block.Preceq C target →
        C ∈ tree ∧ eligible C = true ∧
          ∀ D ∈ tree, D.parent? = C.parent? → eligible D = true → D ≠ C →
            score D < score C) := by
  rw [DominatedSuffix]

/-- No stored child of this block is eligible. Source: S1:707–709. -/
def NoEligibleChild (tree : List Block) (eligible : Block → Bool) (B : Block) : Prop :=
  ∀ C ∈ tree, C.parent? = some B → eligible C = false

theorem NoEligibleChild_def (tree : List Block) (eligible : Block → Bool) (B : Block) :
    NoEligibleChild tree eligible B =
      (∀ C ∈ tree, C.parent? = some B → eligible C = false) := by
  rw [NoEligibleChild]

/-- Closure is required only between the anchor and its stored descendants.
Source: GLY:674–676; P3:4488–4490. -/
def AnchorClosed (anchor : Block) (tree : List Block) : Prop :=
  ∀ B ∈ tree, Block.Preceq anchor B → ∀ A, Block.Preceq anchor A →
    Block.Preceq A B → A ∈ tree

theorem AnchorClosed_def (anchor : Block) (tree : List Block) :
    AnchorClosed anchor tree =
      (∀ B ∈ tree, Block.Preceq anchor B → ∀ A, Block.Preceq anchor A →
        Block.Preceq A B → A ∈ tree) := by
  rw [AnchorClosed]

/-- The fuel bound concerns only stored descendants of the current anchor.
Source: GLY:671–673; P3:4480–4486. -/
def DescendantDepthBound (anchor : Block) (tree : List Block) (fuel : Nat) : Prop :=
  ∀ B ∈ tree, Block.Preceq anchor B → B.depth ≤ anchor.depth + fuel

theorem DescendantDepthBound_def (anchor : Block) (tree : List Block) (fuel : Nat) :
    DescendantDepthBound anchor tree fuel =
      (∀ B ∈ tree, Block.Preceq anchor B → B.depth ≤ anchor.depth + fuel) := by
  rw [DescendantDepthBound]

/-- Source choices on the suffix remain present and eligible in the target.
Source: GLY:680–682; S1:737–741. -/
def SuffixPersists (anchor target : Block) (sourceTree targetTree : List Block)
    (sourceScore : Block → Nat) (sourceEligible targetEligible : Block → Bool) : Prop :=
  ∀ X C, Block.Preceq anchor X → Block.Prec X target →
    GridCO.ghostStep sourceTree sourceScore sourceEligible X = some C →
    Block.Preceq C target → C ∈ targetTree ∧ targetEligible C = true

theorem SuffixPersists_def (anchor target : Block) (sourceTree targetTree : List Block)
    (sourceScore : Block → Nat) (sourceEligible targetEligible : Block → Bool) :
    SuffixPersists anchor target sourceTree targetTree sourceScore
      sourceEligible targetEligible =
      (∀ X C, Block.Preceq anchor X → Block.Prec X target →
        GridCO.ghostStep sourceTree sourceScore sourceEligible X = some C →
        Block.Preceq C target → C ∈ targetTree ∧ targetEligible C = true) := by
  rw [SuffixPersists]

/-- Each eligible target child on the suffix was an eligible source child.
Source: GLY:680–682; S1:737–741. -/
def SuffixReflects (anchor target : Block) (sourceTree targetTree : List Block)
    (sourceEligible targetEligible : Block → Bool) : Prop :=
  ∀ X C, Block.Preceq anchor X → Block.Prec X target →
    C ∈ targetTree → C.parent? = some X → targetEligible C = true →
    C ∈ sourceTree ∧ sourceEligible C = true

theorem SuffixReflects_def (anchor target : Block) (sourceTree targetTree : List Block)
    (sourceEligible targetEligible : Block → Bool) :
    SuffixReflects anchor target sourceTree targetTree sourceEligible targetEligible =
      (∀ X C, Block.Preceq anchor X → Block.Prec X target →
        C ∈ targetTree → C.parent? = some X → targetEligible C = true →
        C ∈ sourceTree ∧ sourceEligible C = true) := by
  rw [SuffixReflects]

/-- Scores agree only on eligible target children of suffix parents.
Source: GLY:680–682; S1:737–741. -/
def SuffixScoresAgree (anchor target : Block) (targetTree : List Block)
    (sourceScore targetScore : Block → Nat) (targetEligible : Block → Bool) : Prop :=
  ∀ X C, Block.Preceq anchor X → Block.Prec X target →
    C ∈ targetTree → C.parent? = some X → targetEligible C = true →
    targetScore C = sourceScore C

theorem SuffixScoresAgree_def (anchor target : Block) (targetTree : List Block)
    (sourceScore targetScore : Block → Nat) (targetEligible : Block → Bool) :
    SuffixScoresAgree anchor target targetTree sourceScore targetScore targetEligible =
      (∀ X C, Block.Preceq anchor X → Block.Prec X target →
        C ∈ targetTree → C.parent? = some X → targetEligible C = true →
        targetScore C = sourceScore C) := by
  rw [SuffixScoresAgree]

/-- `walk_covers_of_dominated_suffix`. Compatibility includes the case
`target ⪯ anchor`; in that case the suffix premise has no vertices.
Source: P3:4396–4403; GLY:667–670. Consumer: F1b.4a, then F1b.1. -/
def WalkCoversOfDominatedSuffixStatement : Prop :=
  ∀ (anchor target : Block) (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool),
    Block.Compatible anchor target → DominatedSuffix anchor target tree score eligible →
    Block.Preceq target (GridCO.ghost anchor tree score eligible)

theorem WalkCoversOfDominatedSuffixStatement_def :
    WalkCoversOfDominatedSuffixStatement =
      (∀ (anchor target : Block) (tree : List Block) (score : Block → Nat)
        (eligible : Block → Bool),
        Block.Compatible anchor target → DominatedSuffix anchor target tree score eligible →
        Block.Preceq target (GridCO.ghost anchor tree score eligible)) := by
  rw [WalkCoversOfDominatedSuffixStatement]

/-- `walk_exact_of_dominated_suffix`. A dominated suffix ending at a block
with no eligible child gives the exact result. Source: S1:707–708;
GLY:669. Consumers: F1b.4a, exact-head instances in F4/F5. -/
def WalkExactOfDominatedSuffixStatement : Prop :=
  ∀ (anchor target : Block) (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool),
    Block.Preceq anchor target → DominatedSuffix anchor target tree score eligible →
    NoEligibleChild tree eligible target → GridCO.ghost anchor tree score eligible = target

theorem WalkExactOfDominatedSuffixStatement_def :
    WalkExactOfDominatedSuffixStatement =
      (∀ (anchor target : Block) (tree : List Block) (score : Block → Nat)
        (eligible : Block → Bool),
        Block.Preceq anchor target → DominatedSuffix anchor target tree score eligible →
        NoEligibleChild tree eligible target → GridCO.ghost anchor tree score eligible = target
      ) := by
  rw [WalkExactOfDominatedSuffixStatement]

/-- `walk_reanchor_of_dominated_suffix`. Moving the anchor along a
dominated suffix preserves the result. Source: S1:710; GLY:669.
Consumers: F1b.4a and the G11 transport instances. -/
def WalkReanchorOfDominatedSuffixStatement : Prop :=
  ∀ (anchor target : Block) (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool),
    Block.Preceq anchor target → DominatedSuffix anchor target tree score eligible →
    GridCO.ghost anchor tree score eligible = GridCO.ghost target tree score eligible

theorem WalkReanchorOfDominatedSuffixStatement_def :
    WalkReanchorOfDominatedSuffixStatement =
      (∀ (anchor target : Block) (tree : List Block) (score : Block → Nat)
        (eligible : Block → Bool),
        Block.Preceq anchor target → DominatedSuffix anchor target tree score eligible →
        GridCO.ghost anchor tree score eligible = GridCO.ghost target tree score eligible) := by
  rw [WalkReanchorOfDominatedSuffixStatement]

/-- `walk_avoids_unsupported_child`. An instance supplies the fact that an
unsupported child is ineligible. A walk from an ancestor of its parent cannot
cover that child. Source: GLY:669; S1:490 (unsupported-child clause).
Consumers: F1b.1 and F1b.4a after the instance's support bound. -/
def WalkAvoidsUnsupportedChildStatement : Prop :=
  ∀ (anchor parent child : Block) (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool),
    Block.Preceq anchor parent → child.parent? = some parent → eligible child = false →
    ¬ Block.Preceq child (GridCO.ghost anchor tree score eligible)

theorem WalkAvoidsUnsupportedChildStatement_def :
    WalkAvoidsUnsupportedChildStatement =
      (∀ (anchor parent child : Block) (tree : List Block) (score : Block → Nat)
        (eligible : Block → Bool),
        Block.Preceq anchor parent → child.parent? = some parent → eligible child = false →
        ¬ Block.Preceq child (GridCO.ghost anchor tree score eligible)) := by
  rw [WalkAvoidsUnsupportedChildStatement]

/-- `walk_covers_of_dominated_suffix_of_anchor_eligible`. The eligibility
test at the result passes even when the target is below the anchor.
Source: P3:4433–4451; GLY:669. Consumer: F1b.1 (`confirmationFrom`). -/
def WalkCoversOfDominatedSuffixOfAnchorEligibleStatement : Prop :=
  ∀ (anchor target : Block) (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool),
    Block.Compatible anchor target → DominatedSuffix anchor target tree score eligible →
    eligible anchor = true →
    Block.Preceq target (GridCO.ghost anchor tree score eligible) ∧
      eligible (GridCO.ghost anchor tree score eligible) = true

theorem WalkCoversOfDominatedSuffixOfAnchorEligibleStatement_def :
    WalkCoversOfDominatedSuffixOfAnchorEligibleStatement =
      (∀ (anchor target : Block) (tree : List Block) (score : Block → Nat)
        (eligible : Block → Bool),
        Block.Compatible anchor target → DominatedSuffix anchor target tree score eligible →
        eligible anchor = true →
        Block.Preceq target (GridCO.ghost anchor tree score eligible) ∧
          eligible (GridCO.ghost anchor tree score eligible) = true) := by
  rw [WalkCoversOfDominatedSuffixOfAnchorEligibleStatement]

/-- `walk_terminal_of_descendant_depth_bound`. Unrelated tree branches
need no depth bound. Source: GLY:671–673; P3:4480–4486.
Consumer: F1b.5 through the anchor-closed terminal form. -/
def WalkTerminalOfDescendantDepthBoundStatement : Prop :=
  ∀ (anchor : Block) (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (fuel : Nat),
    DescendantDepthBound anchor tree fuel →
    GridCO.ghostStep tree score eligible (GridCO.ghostWalk tree score eligible fuel anchor) = none

theorem WalkTerminalOfDescendantDepthBoundStatement_def :
    WalkTerminalOfDescendantDepthBoundStatement =
      (∀ (anchor : Block) (tree : List Block) (score : Block → Nat)
        (eligible : Block → Bool) (fuel : Nat),
        DescendantDepthBound anchor tree fuel →
        GridCO.ghostStep tree score eligible
          (GridCO.ghostWalk tree score eligible fuel anchor) = none) := by
  rw [WalkTerminalOfDescendantDepthBoundStatement]

/-- ROOT-DIGEST W1b: tree root uniqueness excludes a refused tie.
`walk_noEligibleChild_of_anchorClosed`. The conclusion is written in
the source. Source: GLY:674–676; P3:4488–4490. Consumer: F1b.5. -/
def WalkNoEligibleChildOfAnchorClosedStatement : Prop :=
  ∀ (anchor : Block) (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool),
    (∀ A ∈ tree, ∀ B ∈ tree, A.root = B.root → A = B) →
    AnchorClosed anchor tree →
    ∀ B ∈ tree, B.parent? = some (GridCO.ghost anchor tree score eligible) → eligible B = false

/-- ROOT-DIGEST W1b: the defining equation includes the approved tree premise. -/
theorem WalkNoEligibleChildOfAnchorClosedStatement_def :
    WalkNoEligibleChildOfAnchorClosedStatement =
      (∀ (anchor : Block) (tree : List Block) (score : Block → Nat)
        (eligible : Block → Bool),
        (∀ A ∈ tree, ∀ B ∈ tree, A.root = B.root → A = B) →
        AnchorClosed anchor tree →
        ∀ B ∈ tree, B.parent? = some (GridCO.ghost anchor tree score eligible) → eligible B = false
      ) := by
  rw [WalkNoEligibleChildOfAnchorClosedStatement]

/-- `ghost_transfer_sfx`. A covered source prefix transfers under local
persist/reflect and score agreement. Persistence supplies the stored suffix;
no separate path premise is needed. Source: GLY:680–682; S1:737–741.
Consumers: F1b.4b; G11 instances at 03 §4 and 21 H.5/H.6/H.17. -/
def GhostTransferSfxStatement : Prop :=
  ∀ (anchor target : Block) (sourceTree targetTree : List Block)
    (sourceScore targetScore : Block → Nat) (sourceEligible targetEligible : Block → Bool),
    Block.Preceq anchor target →
    Block.Preceq target (GridCO.ghost anchor sourceTree sourceScore sourceEligible) →
    SuffixPersists anchor target sourceTree targetTree sourceScore sourceEligible targetEligible →
    SuffixReflects anchor target sourceTree targetTree sourceEligible targetEligible →
    SuffixScoresAgree anchor target targetTree sourceScore targetScore targetEligible →
    Block.Preceq target (GridCO.ghost anchor targetTree targetScore targetEligible)

theorem GhostTransferSfxStatement_def : GhostTransferSfxStatement =
    (∀ (anchor target : Block) (sourceTree targetTree : List Block)
      (sourceScore targetScore : Block → Nat) (sourceEligible targetEligible : Block → Bool),
      Block.Preceq anchor target →
      Block.Preceq target (GridCO.ghost anchor sourceTree sourceScore sourceEligible) →
      SuffixPersists anchor target sourceTree targetTree sourceScore sourceEligible targetEligible →
      SuffixReflects anchor target sourceTree targetTree sourceEligible targetEligible →
      SuffixScoresAgree anchor target targetTree sourceScore targetScore targetEligible →
      Block.Preceq target (GridCO.ghost anchor targetTree targetScore targetEligible)) := by
  rw [GhostTransferSfxStatement]

end AvailableChain.Gen.Pure

namespace AvailableChain.Gen.Pure

open AvailableChain

/-- Class (iii). DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Walk.lean:433.
INTENTIONAL: name the full score/root order of the selected path steps. -/
def BestAncestry (anchor target : Block) (tree : List Block)
    (score : Block → Nat) (eligible : Block → Bool) : Prop :=
  ∀ X, Block.Preceq anchor X → Block.Prec X target →
    ∃ C, C.parent? = some X ∧ Block.Preceq C target ∧
      C ∈ tree ∧ eligible C = true ∧
      ∀ B ∈ tree, B.parent? = some X → eligible B = true →
        score B ≤ score C ∧ (score B = score C → B.root ≤ C.root)

/-- Class (iii). DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Walk.lean:433.
INTENTIONAL: the defining equation for the selected score/root path order. -/
theorem BestAncestry_def (anchor target : Block) (tree : List Block)
    (score : Block → Nat) (eligible : Block → Bool) :
    BestAncestry anchor target tree score eligible =
      (∀ X, Block.Preceq anchor X → Block.Prec X target →
        ∃ C, C.parent? = some X ∧ Block.Preceq C target ∧
          C ∈ tree ∧ eligible C = true ∧
          ∀ B ∈ tree, B.parent? = some X → eligible B = true →
            score B ≤ score C ∧ (score B = score C → B.root ≤ C.root)) := rfl

/-- Class (iii).
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/ProposalWalkTransportCore.lean:162,259;
DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Walk.lean:433.
INTENTIONAL: state per-reader retained transport with atomic premises and source coverage.
ROOT-DIGEST W1c: require root uniqueness on targetTree.
Use the existing list fuel and score/root order. -/
def WalkCoversOfRetainedTransportStatement : Prop :=
  ∀ (sourceAnchor targetAnchor cut parent : Block)
    (sourceTree targetTree : List Block)
    (sourceScore targetScore : Block → Nat)
    (sourceEligible targetEligible : Block → Bool),
    (∀ A ∈ targetTree, ∀ B ∈ targetTree, A.root = B.root → A = B) →
    Block.Preceq parent (GridCO.ghost sourceAnchor sourceTree sourceScore sourceEligible) →
    Block.Preceq sourceAnchor cut →
    Block.Preceq targetAnchor cut →
    Block.Preceq cut parent →
    BestAncestry targetAnchor cut targetTree targetScore targetEligible →
    SuffixPersists cut parent sourceTree targetTree sourceScore sourceEligible targetEligible →
    SuffixReflects cut parent sourceTree targetTree sourceEligible targetEligible →
    SuffixScoresAgree cut parent targetTree sourceScore targetScore targetEligible →
    Block.Preceq parent (GridCO.ghost targetAnchor targetTree targetScore targetEligible)

/-- Class (iii).
DC: DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/ProposalWalkTransportCore.lean:162,259;
DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Walk.lean:433.
INTENTIONAL: the defining equation for the Generic retained-transport statement.
ROOT-DIGEST W1c: the same targetTree premise as the definition. -/
theorem WalkCoversOfRetainedTransportStatement_def :
    WalkCoversOfRetainedTransportStatement =
      (∀ (sourceAnchor targetAnchor cut parent : Block)
        (sourceTree targetTree : List Block)
        (sourceScore targetScore : Block → Nat)
        (sourceEligible targetEligible : Block → Bool),
        (∀ A ∈ targetTree, ∀ B ∈ targetTree, A.root = B.root → A = B) →
        Block.Preceq parent (GridCO.ghost sourceAnchor sourceTree sourceScore sourceEligible) →
        Block.Preceq sourceAnchor cut →
        Block.Preceq targetAnchor cut →
        Block.Preceq cut parent →
        BestAncestry targetAnchor cut targetTree targetScore targetEligible →
        SuffixPersists cut parent sourceTree targetTree sourceScore sourceEligible targetEligible →
        SuffixReflects cut parent sourceTree targetTree sourceEligible targetEligible →
        SuffixScoresAgree cut parent targetTree sourceScore targetScore targetEligible →
        Block.Preceq parent
          (GridCO.ghost targetAnchor targetTree targetScore targetEligible)) := rfl

end AvailableChain.Gen.Pure
