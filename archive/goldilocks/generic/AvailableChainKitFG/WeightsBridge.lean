module
public import AvailableChainSimplexFG.Objects
public import AvailableChainGeneric.Statements.Pure.Quorum

public section

namespace AvailableChain.SimplexFG.Electorate

open AvailableChain.Gen.Pure

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Use the electorate's positive weights in the Generic Pure layer (GLY E-5). -/
def toWeights (E : Electorate V) : Weights V := ⟨E.weight, E.weight_pos⟩

end AvailableChain.SimplexFG.Electorate

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG AvailableChain.Gen.Pure

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem toWeights_totalWeight (E : Electorate V) :
    E.toWeights.totalWeight = E.totalWeight := by
  unfold Electorate.toWeights
  rfl

omit [DecidableEq V] in
theorem toWeights_weightOf (E : Electorate V) (S : Finset V) :
    E.toWeights.weightOf S = E.weightOf S := by
  unfold Electorate.toWeights
  rfl

omit [DecidableEq V] in
theorem toWeights_q (E : Electorate V) : E.toWeights.q = E.q := by
  unfold Electorate.toWeights
  rfl

omit [DecidableEq V] in
theorem isQuorum_toWeights_iff (E : Electorate V) (S : Finset V) :
    E.toWeights.IsQuorum S ↔ E.IsQuorum S := by
  unfold Electorate.toWeights
  rfl

theorem unit_toWeights_q (n : Nat) :
    (⟨fun _ => 1, fun _ => Nat.one_pos⟩ : Electorate (Fin n)).toWeights.q = qF n := by
  rw [toWeights_q, qF_def]
  dsimp only [Electorate.q, Electorate.totalWeight]
  simp only [Finset.sum_const, Nat.nsmul_eq_mul, mul_one]
  change (2 * (List.finRange n).length + 2) / 3 = (2 * n + 2) / 3
  rw [List.length_finRange]

end AvailableChain.KitFG
