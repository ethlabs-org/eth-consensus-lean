module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.WindowAnchorRoute
import ConsensusLean.Lemmas.Tactic.Linarith
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation

public section

/-! # Goldilocks Obligations: slot arithmetic of the anchor gap

`c` slots after `s` the slot time is `4Δ·c` later (`ts_add_gap`), and the slot-free delivery premise
`6Δ + ΔF ≤ 4Δ·c` gives `t_s + 6Δ + ΔF ≤ t_{s+c}` at every slot (`gap_delivery`). The anchor steps
at gap `c` are `anchorSteps_gap_at` (`Growing/Obligations/Healthy/AnchorStepsGap`). -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams}

/-! ## Arithmetic of the gap -/

/-- `c` slots after `s`, the slot time is `4Δ·c` later. -/
theorem ts_add_gap (s c : Nat) : sp.ts (s + c : Nat) = sp.ts s + 4 * sp.Δ * c := by
  simp only [SAParams.ts]; push_cast; ring

/-- The slot-free delivery premise gives the delivery inequality at every slot. -/
theorem gap_delivery {ΔF : Time} {c : Nat} (h : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * c) (s : Nat) :
    sp.ts s + 6 * sp.Δ + ΔF ≤ sp.ts (s + c : Nat) := by
  have := ts_add_gap (sp := sp) s c
  linarith

end Consensus.Goldilocks.Obligations

end
