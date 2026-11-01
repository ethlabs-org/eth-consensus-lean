module
public import AvailableChainFGCompose.Statements.Bounds
public import Mathlib.Tactic.Linarith -- shake: keep (arithmetic tactics)

public section

/-! Blueprint 21 HG.3 gap. The repair allowance is the published local repair service.
The proposer floor, the held gate copy, the continuing local service and the common
opening of a seed-qualified proposal are explicit leaves; the age service is the
generic d5b consumer with its own leaves. -/

namespace AvailableChain.FGCompose

variable (T : FGTiming)

/-- Blueprint 21 HG.3. DC: SAME period bound for the first opening. -/
theorem frontierSearch_period_bound_core (hT : FGTimingLaws T) : 8 * T.delta ≤ FGCompose.P T := by
  have hR : (2 : Time) ≤ T.roundSlots := by exact_mod_cast hT.rounds
  change 8 * T.delta ≤ 4 * (T.roundSlots : Time) * T.delta
  nlinarith [hT.delta_pos]

end AvailableChain.FGCompose
end
