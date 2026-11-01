module
public import AvailableChainFGCompose.Proofs.Finality.MiddleSupport

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

/-- Paper 22:1265–1289: the terminal carrier slot is after row delivery, its read plus one
delay is the kernel deadline, and it precedes the next action.
DC: INTENTIONAL: the W deadline bounds the actual terminal read. -/
theorem kernel_terminal_bounds_W_core (T : FGTiming) (L : FGTimingLaws T) {ΔF gst : Time}
    (q : Nat) (bound : LivenessBoundW T ΔF) (hF : 0 ≤ ΔF) (hG : gst ≤ T.action q) :
    max (T.action q) gst + ΔF ≤ T.proposal (q * T.roundSlots + kappaF T ΔF) ∧
      T.proposal (q * T.roundSlots + kappaF T ΔF) + T.delta = kernelDeadlineW T ΔF q ∧
      T.proposal (q * T.roundSlots + kappaF T ΔF) < T.action (q + 1) := by
  have hcov := kmid_kappa_cover T L ΔF hF
  have hκ := bound.kappa_le_R
  have hd := L.delta_pos
  have hκR : (kappaF T ΔF : Time) ≤ T.roundSlots := by exact_mod_cast hκ
  rw [max_eq_left hG]
  refine ⟨?_, ?_, ?_⟩
  · rw [kmid_actionTime_eq T L, L.proposal_eq]
    push_cast at hcov ⊢
    nlinarith
  · rw [L.proposal_eq]
    unfold kernelDeadlineW betaF FGCompose.P
    push_cast
    ring
  · rw [kmid_actionTime_eq T L, L.proposal_eq]
    push_cast
    nlinarith

end AvailableChain.FGCompose
end
