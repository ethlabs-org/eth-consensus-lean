module
public import AvailableChainSAPC.Statements.Contract
public import AvailableChainSA.Proofs.Basic

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic

theorem sapcConstants_valid (p : Params) (G : Time) (hG : 0 < G) :
    (sapcConstants p G).Valid := by
  exact { SA.saConstants_valid p G hG with
    thetaRec_lower := by norm_num [sapcConstants]
    thetaRec_upper := by norm_num [sapcConstants] }

theorem sapcStrongConstants_valid (p : Params) : (sapcStrongConstants p).Valid := by
  constructor
  dsimp [sapcStrongConstants]
  linarith [p.deltaPos]

theorem outputOrder {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) : OutputOrder (sapc p) (sapcInterface p).toInterface rho := by
  constructor
  intro v _ t
  exact GridCO.block_preceq_self _

theorem quorum_bounds (p : Params) :
    0 < pcQuorum p ∧ pcQuorum p ≤ p.n ∧ p.n < 2 * pcQuorum p := by
  dsimp [pcQuorum]
  have := p.nPos
  omega

theorem cap_bounds (p : Params) :
    3 * pcFaultCap p < p.n ∧ pcFaultCap p < releaseThreshold p ∧
      p.n + pcFaultCap p < 2 * pcQuorum p := by
  change 3 * ((p.n - 1) / 3) < p.n ∧
    (p.n - 1) / 3 < (p.n + 1) / 2 ∧
    p.n + (p.n - 1) / 3 < 2 * ((2 * p.n + 2) / 3)
  have := p.nPos
  omega

theorem capped_counts (p : Params) (a h : Nat)
    (hcap : a ≤ pcFaultCap p) (hfull : h + a = p.n) :
    a < pcQuorum p ∧ p.n + a < 2 * pcQuorum p ∧ pcQuorum p ≤ h ∧
      2 * pcFaultCap p < h := by
  dsimp [pcFaultCap, pcQuorum] at *
  have := p.nPos
  omega

/-- The clean majority gives q > a without the one-third cap. -/
theorem quorum_above_faults (p : Params) (a h : Nat)
    (hmaj : a < h) (hsize : h + a ≤ p.n) : a < pcQuorum p := by
  have := (quorum_bounds p).2.2
  omega

theorem recovery_count_implies_cap (p : Params) (a h : Nat)
    (hsize : h + a = p.n)
    (hrec : (2 / 3 : ℚ) * ((h : ℚ) + a) < h) : a ≤ pcFaultCap p := by
  have ha : 2 * a < h := by
    have : (2 : ℚ) * a < h := by linarith
    exact_mod_cast this
  dsimp [pcFaultCap]
  omega

/-- The full-participation recovery genuine support is an F4 floor.
This inequality does not assume every supporting seat is honest. -/
theorem recovery_support_above_floor (p : Params) (a h support denominator : Nat)
    (hcap : a ≤ pcFaultCap p) (hfull : h + a = p.n)
    (hdenom : h ≤ denominator) (hgenuine : denominator < 2 * support) :
    pcFaultCap p < support := by
  have := (capped_counts p a h hcap hfull).2.2.2
  omega

/-- An awake quorum is strictly larger than twice the fixed fault cap. -/
theorem quorum_above_twice_cap (p : Params) : 2 * pcFaultCap p < pcQuorum p := by
  dsimp [pcFaultCap, pcQuorum]
  have := p.nPos
  omega

/-- The raw majority gives an F4 floor from an awake quorum. Supporting
seats need not all be honest. -/
theorem quorum_support_above_floor (p : Params) (h support denominator : Nat)
    (hq : pcQuorum p ≤ h) (hdenom : h ≤ denominator)
    (hgenuine : denominator < 2 * support) : pcFaultCap p < support := by
  have := quorum_above_twice_cap p
  omega

end AvailableChain.SAPC
end
