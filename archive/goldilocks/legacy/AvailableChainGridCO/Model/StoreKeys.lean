module
public import AvailableChainGridCO.Model.Protocol

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy] {mode : HeadMode}

/-- [ROOT-DIGEST-2 W1; DC shared HEAD modes] Write the same keys in each mode. -/
def writeKeys {n : Nat} (st : State n mode)
    (keys : List (Block × Nat)) (limit : Time) : State n mode :=
  keys.foldl (fun acc key => writeObligation acc key.1 key.2 limit) st

theorem writeKeys_def {n : Nat} (st : State n mode)
    (keys : List (Block × Nat)) (limit : Time) :
    writeKeys st keys limit =
      keys.foldl (fun acc key => writeObligation acc key.1 key.2 limit) st := by
  rw [writeKeys]

/-- [ROOT-DIGEST-2 W1; DC shared HEAD modes] Read the same gate keys in each mode. -/
def gateWriteKeys (p : Params) {n : Nat} (st : State n mode)
    (r : Slot) (C : Block) : List (Block × Nat) :=
  (st.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
    (fun b => (admissionLevels p st r b).map (fun g => (b, g)))

theorem gateWriteKeys_def (p : Params) {n : Nat} (st : State n mode)
    (r : Slot) (C : Block) :
    gateWriteKeys p st r C =
      (st.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
        (fun b => (admissionLevels p st r b).map (fun g => (b, g))) := by
  rw [gateWriteKeys]

/-- [ROOT-DIGEST-2 W1; DC scoped roots]
Root identity on the ancestors of this explicit tree is a premise.
The nominal Block datatype does not give global root injectivity. -/
def RootInjectiveBelow (tree : List Block) : Prop :=
  ∀ A C, (∃ B ∈ tree, Block.Preceq A B) →
    (∃ B ∈ tree, Block.Preceq C B) → A.root = C.root → A = C

end AvailableChain.GridCO
end
