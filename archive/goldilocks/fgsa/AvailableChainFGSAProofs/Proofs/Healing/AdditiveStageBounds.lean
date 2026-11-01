module
public import AvailableChainFGSAClaims.Statements.Bounds

public section

namespace AvailableChain.FGSA.Run

/-- This bridge groups the existing Bounds.B_reset scalar budgets.
Consumers: F5.H.10, H.11 and HG.6. Sources: 21:1293–1318,1619–1622,1654–1663.
DC: additive (no DC counterpart); reason: ordered deadline sums are scalar helpers.
Lane definitions: Claims/Statements/Bounds.B_reset, P, E_g, E_j, B_c and D_c. -/
theorem fgsa_reset_stage_sum (p : Params) (G ρbar : Time) :
    B_reset p G ρbar =
      3 * P p + (2 * E_g p G ρbar + 2 * E_j p G ρbar +
        B_c p G ρbar + D_c p ρbar) := by
  change 3 * P p + 2 * E_g p G ρbar + 2 * E_j p G ρbar +
    B_c p G ρbar + D_c p ρbar = _
  simp only [add_assoc]

end AvailableChain.FGSA.Run
