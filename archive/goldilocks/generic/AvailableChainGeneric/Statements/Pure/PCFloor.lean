module
public import AvailableChainModel.Objects.Blocks

@[expose] public section

/-! Generic Pure layer: the PC output floor of PC-SA. Source:
`tip-stability/codex/reports/sa-alternatives/pcsa-decisions.md` R-g and its
clarification: the available output is `S` if the PC target is `⪯ S`, else
the PC target, also when `S` conflicts with the target. The order is
`Block.Preceq` (`AvailableChainModel/Objects/Blocks.lean`), the order of the
Generic AvailableChain contract (`MonotoneFrom`, `OutputOrder`). The PC enters
as its target, `none` when no PC is held. Definitions, contract Props and
defining equations only. -/

namespace AvailableChain.Gen.Pure

/-- The available output: `S` if the held PC target is `⪯ S` or no PC is held,
else the PC target. -/
def pcFloor (S : Block) (target : Option Block) : Block :=
  target.elim S fun T => if Block.Preceq T S then S else T

theorem pcFloor_def (S : Block) (target : Option Block) :
    pcFloor S target = target.elim S fun T => if Block.Preceq T S then S else T := by rfl

/-- The output extends the held PC target. -/
def PCFloorTargetStatement : Prop :=
  ∀ (S T : Block), Block.Preceq T (pcFloor S (some T))

/-- Defining equation. -/
theorem PCFloorTargetStatement_def : PCFloorTargetStatement =
    (∀ (S T : Block), Block.Preceq T (pcFloor S (some T))) := by rfl

/-- A block below `S` and compatible with the held PC target is below the
output. Consumers: the contract's `stable ⪯ confirmed` (`OutputOrder`), the
anchor and lease bounds below the output. -/
def PCFloorNestStatement : Prop :=
  ∀ (X S : Block) (target : Option Block),
    Block.Preceq X S → (∀ T, target = some T → Block.Compatible X T) →
      Block.Preceq X (pcFloor S target)

/-- Defining equation. -/
theorem PCFloorNestStatement_def : PCFloorNestStatement =
    (∀ (X S : Block) (target : Option Block),
      Block.Preceq X S → (∀ T, target = some T → Block.Compatible X T) →
        Block.Preceq X (pcFloor S target)) := by rfl

/-- The output only moves forward when `S` moves forward, each held PC target
has a later held target that extends it, and the later target is compatible
with the later `S`. The earlier state needs no compatibility. Consumer: the
contract's `MonotoneFrom` for the available output. -/
def PCFloorMonoStatement : Prop :=
  ∀ (S S' : Block) (target target' : Option Block),
    Block.Preceq S S' →
    (∀ T, target = some T → ∃ T', target' = some T' ∧ Block.Preceq T T') →
    (∀ T', target' = some T' → Block.Compatible T' S') →
      Block.Preceq (pcFloor S target) (pcFloor S' target')

/-- Defining equation. -/
theorem PCFloorMonoStatement_def : PCFloorMonoStatement =
    (∀ (S S' : Block) (target target' : Option Block),
      Block.Preceq S S' →
      (∀ T, target = some T → ∃ T', target' = some T' ∧ Block.Preceq T T') →
      (∀ T', target' = some T' → Block.Compatible T' S') →
        Block.Preceq (pcFloor S target) (pcFloor S' target')) := by rfl

end AvailableChain.Gen.Pure
