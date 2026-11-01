module
public import Mathlib.Data.Rat.Defs
public import AvailableChainModel.Objects.Time

@[expose] public section

namespace AvailableChain.Statements.Generic

/-- Time bounds are absolute integer time units, normally expressed using `E.Δ`. -/
structure Constants where
  /-- η, the history window. -/
  η : Time
  /-- Confirmed inclusion delay. -/
  D_c : Time
  /-- Stable inclusion delay. -/
  D_s : Time
  /-- Fast stable inclusion delay. -/
  D_f : Time
  /-- A, the lag before an outage can start. -/
  armingLag : Time
  /-- Arming lag with at least half of the seats honestly awake. -/
  fastArmingLag : Time
  /-- Π, the maximum outage duration. -/
  budget : Time
  /-- ρ, the recovery bound after GST. -/
  recoveryBound : Time
  /-- G, the maximum gap between honest awake opening proposers in the
  Recovery regime. A premise parameter; ρ may depend on it. -/
  proposerGap : Time
  /-- θ, the η-sleepy weight threshold. -/
  θ : ℚ
  /-- θrec, the current-participation threshold after GST. -/
  θrec : ℚ
  /-- Whether recovery also requires every honest validator to be awake. -/
  recoveryFull : Bool

/-- Bounds fixed by the contract. -/
structure Constants.Valid (C : Constants) : Prop where
  theta_lower : (1 / 2 : ℚ) ≤ C.θ
  theta_upper : C.θ ≤ (3 / 4 : ℚ)
  thetaRec_lower : (1 / 2 : ℚ) ≤ C.θrec
  thetaRec_upper : C.θrec ≤ (3 / 4 : ℚ)
  eta_nonneg : 0 ≤ C.η
  delays_nonneg : 0 ≤ C.D_c ∧ 0 ≤ C.D_s ∧ 0 ≤ C.D_f
  armingLag_nonneg : 0 ≤ C.armingLag
  fastArmingLag_nonneg : 0 ≤ C.fastArmingLag
  fastArmingLag_le : C.fastArmingLag ≤ C.armingLag
  budget_nonneg : 0 ≤ C.budget
  budget_le_eta : C.budget ≤ C.η
  recoveryBound_nonneg : 0 ≤ C.recoveryBound
  proposerGap_pos : 0 < C.proposerGap

end AvailableChain.Statements.Generic
end
