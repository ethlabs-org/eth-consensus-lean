module
public import AvailableChainModel.Objects.CommonAncestor

@[expose] public section

namespace AvailableChain.Gen.Pure

/-- The common ancestor precedes both inputs. -/
def MeetPrefixStatement : Prop :=
  ∀ (B C : Block), Block.Preceq (Block.meet B C) B ∧ Block.Preceq (Block.meet B C) C

/-- Defining equation. -/
theorem MeetPrefixStatement_def : MeetPrefixStatement =
    (∀ (B C : Block), Block.Preceq (Block.meet B C) B ∧ Block.Preceq (Block.meet B C) C) := by rfl

/-- Every common ancestor precedes the deepest common ancestor. -/
def MeetMaximalStatement : Prop :=
  ∀ (X B C : Block), Block.Preceq X B → Block.Preceq X C →
    Block.Preceq X (Block.meet B C)

/-- Defining equation. -/
theorem MeetMaximalStatement_def : MeetMaximalStatement =
    (∀ (X B C : Block), Block.Preceq X B → Block.Preceq X C →
    Block.Preceq X (Block.meet B C)) := by rfl

/-- Input order does not change the common ancestor. -/
def MeetCommStatement : Prop :=
  ∀ (B C : Block), Block.meet B C = Block.meet C B

/-- Defining equation. -/
theorem MeetCommStatement_def : MeetCommStatement =
    (∀ (B C : Block), Block.meet B C = Block.meet C B) := by rfl

/-- Prefixes of the meet are exactly the common prefixes. -/
def MeetInclusionStatement : Prop :=
  ∀ (X B C : Block), Block.Preceq X (Block.meet B C) ↔
    Block.Preceq X B ∧ Block.Preceq X C

/-- Defining equation. -/
theorem MeetInclusionStatement_def : MeetInclusionStatement =
    (∀ (X B C : Block), Block.Preceq X (Block.meet B C) ↔
    Block.Preceq X B ∧ Block.Preceq X C) := by rfl

/-- If the first input precedes the second input, their meet is the first input. -/
def MeetOfPreceqStatement : Prop :=
  ∀ (B C : Block), Block.Preceq B C → Block.meet B C = B

/-- Defining equation. -/
theorem MeetOfPreceqStatement_def : MeetOfPreceqStatement =
    (∀ (B C : Block), Block.Preceq B C → Block.meet B C = B) := by rfl

/-- A prefix of the meet is compatible with both inputs. -/
def MeetCompatibilityTransferStatement : Prop :=
  ∀ (K C H X : Block), K = Block.meet C H → Block.Preceq X K →
    Block.Compatible X C ∧ Block.Compatible X H

/-- Defining equation. -/
theorem MeetCompatibilityTransferStatement_def : MeetCompatibilityTransferStatement =
    (∀ (K C H X : Block), K = Block.meet C H → Block.Preceq X K →
    Block.Compatible X C ∧ Block.Compatible X H) := by rfl

end AvailableChain.Gen.Pure
