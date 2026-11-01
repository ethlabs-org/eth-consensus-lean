module
public import AvailableChainGeneric.Proofs.Pure.HeadAfterSettlement
public import AvailableChainFGSAProofs.Proofs.Shared.GridSchedule

public section

namespace AvailableChain.FGSA.Run

open Gen.Pure

/-- This bridge selects the source HEAD through the SA vote and proposal clocks.
Consumers: F5.HG.7 and F5.HG.8a. Sources: S1b:815–817; 21:1721–1727,1840,2208–2217.
DC: additive (no DC counterpart); reason: the settlement HEAD cut is an FG-SA input.
Clock definitions: SA.voteTime and SA.proposalTime, bridged by Shared/GridSchedule. -/
theorem fgsa_firstHead_after (p : Params) (w : Time) (b : Nat)
    (hw : 0 ≤ w + 2 * p.Δ)
    (hfirst : w + 3 * p.Δ ≤ SA.voteTime p.toParams b ∧
      ∀ j : Nat, j < b → SA.voteTime p.toParams j < w + 3 * p.Δ) :
    SA.proposalTime p.toParams b =
      4 * p.Δ * ((w + 2 * p.Δ + 4 * p.Δ - 1) / (4 * p.Δ)) := by
  simpa only [fgsa_grid_sa_voteTime, fgsa_grid_sa_proposalTime] using
    (Gen.Pure.firstHead_after p.Δ w b p.deltaPos hw
      (by simpa only [fgsa_grid_sa_voteTime] using hfirst))

/-- This bridge bounds the selected HEAD by the ceiling at an upper cut.
Consumers: F5.HG.7 and F5.HG.8a. Sources: 21:1726,1840,2208–2217.
DC: additive (no DC counterpart); reason: the settlement HEAD cut is an FG-SA input.
Clock definitions: SA.voteTime and SA.proposalTime, bridged by Shared/GridSchedule. -/
theorem fgsa_firstHead_after_bound (p : Params) (w U : Time) (b : Nat)
    (hw : 0 ≤ w + 2 * p.Δ) (hwU : w ≤ U)
    (hfirst : w + 3 * p.Δ ≤ SA.voteTime p.toParams b ∧
      ∀ j : Nat, j < b → SA.voteTime p.toParams j < w + 3 * p.Δ) :
    SA.proposalTime p.toParams b ≤
      4 * p.Δ * ((U + 2 * p.Δ + 4 * p.Δ - 1) / (4 * p.Δ)) := by
  simpa only [fgsa_grid_sa_voteTime, fgsa_grid_sa_proposalTime] using
    (Gen.Pure.firstHead_after_bound p.Δ w U b p.deltaPos hw hwU
      (by simpa only [fgsa_grid_sa_voteTime] using hfirst))

end AvailableChain.FGSA.Run
