module
public import AvailableChainGeneric.Proofs.Pure.OpeningAfterGate
public import AvailableChainFGSAProofs.Proofs.Shared.GridSchedule

public section

namespace AvailableChain.FGSA.Run

open Gen.Pure

/-- The Gen inclusive-opening bound uses the FG-SA action and SA gate clocks.
Consumers: F5.HG.1 and F5.HG.3. Sources: 21:1343–1346,1413–1415,1488–1506.
DC: additive (no DC counterpart); reason: the gate-grid bound is sharper.
Clock bridges: Shared/GridSchedule; SA.gateTime, Params.actionTime and Bounds.P. -/
theorem fgsa_firstOpening_after_gate (p : Params) (q r : Nat)
    (hfirst : SA.gateTime p.toParams q ≤ p.actionTime r ∧
      ∀ j : Nat, j < r → p.actionTime j < SA.gateTime p.toParams q) :
    0 ≤ p.actionTime r - SA.gateTime p.toParams q ∧
      p.actionTime r - SA.gateTime p.toParams q ≤ P p - 4 * p.Δ := by
  have hR : 1 ≤ p.R := le_trans (by decide) p.RLarge
  have hg : SlotGrid.d p.Δ q ≤ SlotGrid.a p.Δ p.R r ∧
      ∀ j : Nat, j < r → SlotGrid.a p.Δ p.R j < SlotGrid.d p.Δ q := by
    simpa only [fgsa_grid_sa_gateTime, fgsa_grid_action_time] using hfirst
  simpa only [fgsa_grid_sa_gateTime, fgsa_grid_action_time, fgsa_grid_period]
    using Gen.Pure.firstOpening_after_gate p.Δ p.R q r p.deltaPos hR hg

end AvailableChain.FGSA.Run
