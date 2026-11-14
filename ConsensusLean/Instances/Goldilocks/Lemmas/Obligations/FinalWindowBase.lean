module
public import Mathlib.Data.Fin.VecNotation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.WindowAnchorRoute
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Obligations: the span of the final pattern

The final pattern `[0, c, 2c, 3c]` spans `3c` slots (`finalWindow_span_of_offsets`), used by the
final query timing (`FinalQueryTiming`). -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The final pattern with offsets `[0, c, 2c, 3c]` spans `3c` slots. -/
theorem finalWindow_span_of_offsets {c : Nat}
    (hpat : (finalWindow A).offsets = [0, c, 2 * c, 3 * c]) : (finalWindow A).span = 3 * c := by
  unfold Pattern.span
  rw [hpat]
  simp only [List.foldr_cons, List.foldr_nil]
  omega

end Consensus.Goldilocks.Obligations

end
