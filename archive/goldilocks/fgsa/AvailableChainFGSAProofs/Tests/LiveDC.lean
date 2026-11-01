module
public import AvailableChainFGSAProofs.Proofs.Assembly.Root -- shake: keep (LIVE-DC root checks)

namespace AvailableChain.FGSA.Run

#check @liveDCDeadline_W
#check @LiveDCConcl_W
#check @FinalityLivenessGSTClaim_W
#check @healing_liveDCFromWindows
#check @fgsaClaims

-- Both forms retain the old conclusion and supply the three DC clauses together.
example (p : Params) (form : FinFormW) (G ΔF : Time) (g : Nat)
    (hδ : p.δt = 2 * p.R) {V : Type} [DecidableEq V] [Fintype V]
    {In : Type} (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (pt : PtT)
    (h : FinalityLivenessGSTPrem_W p c G ΔF form g E rho pt)
    (hhor : pt.t + liveDCDeadline_W p ΔF G g ≤ rho.horizon) :
    FinalityLivenessConcl_W p c E rho pt.t (pt.t + W_W p ΔF g) ∧
      LiveDCConcl_W p c E rho pt.t (pt.t + liveDCDeadline_W p ΔF G g) := by
  have hc : FinalityLivenessGSTClaim_W p form := by
    cases form with
    | recFE => exact (fgsaClaims p).finalityLivenessGSTRecFE
    | recF4 => exact (fgsaClaims p).finalityLivenessGSTRecF4
  obtain ⟨_, _, _, hold, hDC⟩ := hc G ΔF g hδ c E rho pt h
  exact ⟨hold, hDC hhor⟩

-- Equality at the larger horizon is sufficient; no strict horizon is required.
example (p : Params) (G ΔF : Time) (g : Nat) (hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type}
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtT)
    (h : FinalityLivenessGSTPrem_W p c G ΔF .recFE g E rho pt)
    (hhor : pt.t + liveDCDeadline_W p ΔF G g = rho.horizon) :
    LiveDCConcl_W p c E rho pt.t rho.horizon := by
  obtain ⟨_, _, _, _, hDC⟩ := (fgsaClaims p).finalityLivenessGSTRecFE G ΔF g hδ c E rho pt h
  simpa only [hhor] using hDC hhor.le

end AvailableChain.FGSA.Run
