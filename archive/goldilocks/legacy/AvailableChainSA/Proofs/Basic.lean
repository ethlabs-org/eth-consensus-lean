module
public import AvailableChainSA.Statements.Contract
public import AvailableChainGridCO.Proofs.Basic

@[expose] public section
namespace AvailableChain.SA
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- The single release level is positive and is a valid seat count. -/
theorem releaseThreshold_bounds (p : Params) :
    0 < releaseThreshold p ∧ releaseThreshold p ≤ p.n := by
  change 0 < (p.n + 1) / 2 ∧ (p.n + 1) / 2 ≤ p.n
  have := p.nPos
  omega

/-- A current honest majority puts the static fault count below τ. -/
theorem faults_lt_releaseThreshold (p : Params) (a h : Nat)
    (hmaj : a < h) (hsize : h + a ≤ p.n) : a < releaseThreshold p := by
  change a < (p.n + 1) / 2
  omega

theorem saConstants_valid (p : Params) (G : Time) (hG : 0 < G) :
    (saConstants p G).Valid := by
  have hL : 0 ≤ lifetime p := GridCO.lifetime_nonneg p.engine
  have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
  have hd := p.deltaPos
  refine ⟨by norm_num [saConstants], by norm_num [saConstants],
    by norm_num [saConstants], by norm_num [saConstants], p.etaNonneg,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hG⟩
  · dsimp [saConstants]; exact ⟨by linarith, by linarith, by linarith⟩
  · dsimp [saConstants]; exact mul_nonneg (by linarith) (le_of_lt hd)
  · dsimp [saConstants]; linarith
  · dsimp [saConstants]; nlinarith
  · exact le_min p.etaNonneg hL
  · exact min_le_left _ _
  · dsimp [saConstants]; linarith

theorem outputOrder {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sa p)) : OutputOrder (sa p) (saInterface p) rho := by
  constructor
  intro v _ t
  exact GridCO.block_preceq_self _

theorem fastLag_le_slowLag (p : Params) (G : Time) :
    (saConstants p G).fastArmingLag ≤ (saConstants p G).armingLag := by
  have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
  dsimp [saConstants]
  nlinarith [p.deltaPos]

/-- A conflicting row older than the full slow window expires before
its final transfer HEAD, including equality at the release cutoff. -/
theorem slow_window_expiry (p : Params) (r : Slot) (hr : p.k ≤ r) :
    gateTime p (r - p.k) + lifetime p = releaseTime p r := by
  simp only [gateTime, lifetime, releaseTime, GridCO.gateTime, GridCO.releaseTime,
    GridCO.proposalTime, GridCO.lifetime, Params.engine, Nat.cast_sub hr]
  ring

theorem recoveryBound_eq_paper (p : Params) (G : Time) :
    (saConstants p G).recoveryBound = lifetime p + G + (4 * (p.k : Time) + 7) * p.Δ := by
  simp only [saConstants, lifetime, GridCO.lifetime, Params.engine]
  ring

end AvailableChain.SA
end
