module
public import AvailableChainModel.Objects.Blocks

@[expose] public section

-- Register the namespaces for the AC open list without an engine import.
namespace AvailableChain.V2.Engine
end AvailableChain.V2.Engine

namespace AvailableChain.Gen.AC

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

/-- Each earlier honest result is a prefix of a result at slot `r`.
Source: step4b-plan.md, S4b-10, Q6 A;
AvailableChainGridCO/Proofs/HistoryInduction.lean:9–14. -/
def GenuineExtends {V : Type} (honest : V → Prop)
    (result : Slot → V → Option Block) (r : Slot) : Prop :=
  ∀ s, s < r → ∀ source, honest source → ∀ b,
    result s source = some b → ∀ reader, honest reader →
      ∃ c, result r reader = some c ∧ Block.Preceq b c

theorem GenuineExtends_def {V : Type} (honest : V → Prop)
    (result : Slot → V → Option Block) (r : Slot) :
    GenuineExtends honest result r =
      (∀ s, s < r → ∀ source, honest source → ∀ b,
        result s source = some b → ∀ reader, honest reader →
          ∃ c, result r reader = some c ∧ Block.Preceq b c) := by
  rw [GenuineExtends]

/-- Each honest result is a prefix of the next honest head.
Source: step4b-plan.md, S4b-10, Q6 A;
AvailableChainGridCO/Proofs/HistoryInduction.lean:18–22. -/
def GenuineContinues {V : Type} (honest : V → Prop)
    (result : Slot → V → Option Block) (next : Slot → V → Block) (r : Slot) : Prop :=
  ∀ source, honest source → ∀ b, result r source = some b →
    ∀ reader, honest reader → Block.Preceq b (next r reader)

theorem GenuineContinues_def {V : Type} (honest : V → Prop)
    (result : Slot → V → Option Block) (next : Slot → V → Block) (r : Slot) :
    GenuineContinues honest result next r =
      (∀ source, honest source → ∀ b, result r source = some b →
        ∀ reader, honest reader → Block.Preceq b (next r reader)) := by
  rw [GenuineContinues]

/-- Honest results extend earlier results and continue to the next head.
Source: step4b-plan.md, S4b-10, Q6 A; GLY r3.14:736–737,1868–1870. -/
def GenuineHistory {V : Type} (honest : V → Prop)
    (result : Slot → V → Option Block) (next : Slot → V → Block) (r : Slot) : Prop :=
  GenuineExtends honest result r ∧ GenuineContinues honest result next r

theorem GenuineHistory_def {V : Type} (honest : V → Prop)
    (result : Slot → V → Option Block) (next : Slot → V → Block) (r : Slot) :
    GenuineHistory honest result next r =
      (GenuineExtends honest result r ∧ GenuineContinues honest result next r) := by
  rw [GenuineHistory]

end AvailableChain.Gen.AC
