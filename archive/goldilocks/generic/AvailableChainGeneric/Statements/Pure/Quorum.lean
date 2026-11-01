module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic -- shake: keep (re-export)
public import Mathlib.Data.Fintype.Basic -- shake: keep (re-export)

@[expose] public section

/-! Generic Pure layer: positive weights, the unit-weight quorum, and the regime
records `FaultQ`, `FaultX` and `Batch` (GLY A.3, C.1, E-5; ruling D05).
Definitions and defining equations only. Each regime record has one field,
so a proof reads that field and needs no equation lemma. -/

namespace AvailableChain.Gen.Pure

/-- The unit-weight quorum `q_F = (2n+2) div 3`. The body is the body of
`AvailableChain.SimplexFG.Electorate.q` (AvailableChainSimplexFG/Objects.lean:209,
`(2 * E.totalWeight + 2) / 3`) with `E.totalWeight = n`, its value for unit
weights. -/
def qF (n : Nat) : Nat := (2 * n + 2) / 3

theorem qF_def (n : Nat) : qF n = (2 * n + 2) / 3 := by rw [qF]

/-- `a < q_F n`: one `q_F` set has an honest member (GLY C.1).
DC: Conditions.lean:180; INTENTIONAL: Keep the weaker FaultQ; GLY r3.19 S043. -/
structure FaultQ (n a : Nat) : Prop where
  lt : a < qF n

/-- `a + n < 2 q_F n`: two `q_F` sets meet in an honest member (GLY C.1).
DC: Conditions.lean:180; Conditions.lean:105; INTENTIONAL: Fault counts separate; GLY r3.19 S044. -/
structure FaultX (n a : Nat) : Prop where
  lt : a + n < 2 * qF n

/-- `m < h`: an honest batch beats the rest (GLY C.1).
DC: Conditions.lean:169; INTENTIONAL: Point count; producer window; GLY r3.19 S045. -/
structure Batch (h m : Nat) : Prop where
  lt : m < h

/-- Fixed positive weights for a finite set of identities (GLY E-5). -/
structure Weights (V : Type) [Fintype V] where
  weight : V → Nat
  weight_pos : ∀ i, 0 < weight i

namespace Weights
variable {V : Type} [Fintype V] [DecidableEq V]

def totalWeight (E : Weights V) : Nat := ∑ i, E.weight i

omit [DecidableEq V] in
theorem totalWeight_def (E : Weights V) : E.totalWeight = ∑ i, E.weight i := by
  rw [totalWeight]

def weightOf (E : Weights V) (S : Finset V) : Nat := ∑ i ∈ S, E.weight i

omit [DecidableEq V] in
theorem weightOf_def (E : Weights V) (S : Finset V) :
    E.weightOf S = ∑ i ∈ S, E.weight i := by
  rw [weightOf]

def q (E : Weights V) : Nat := (2 * E.totalWeight + 2) / 3

omit [DecidableEq V] in
theorem q_def (E : Weights V) : E.q = (2 * E.totalWeight + 2) / 3 := by
  rw [q]

def IsQuorum (E : Weights V) (S : Finset V) : Prop := E.q ≤ E.weightOf S

omit [DecidableEq V] in
theorem IsQuorum_def (E : Weights V) (S : Finset V) :
    E.IsQuorum S = (E.q ≤ E.weightOf S) := by
  rw [IsQuorum]

end Weights

end AvailableChain.Gen.Pure
