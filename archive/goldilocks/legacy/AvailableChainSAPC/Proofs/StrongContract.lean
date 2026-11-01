module
public import AvailableChainSAPC.Proofs.RecoveryStrong

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- SA-PC satisfies every additive strong claim under its explicit cap.
No existing contract definition or base fault scope is changed. -/
theorem sapcStrong_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (G : Time) (hG : 0 < G) (hΔ : E.Δ = p.Δ) :
    SAPCStrong p G E := by
  refine ⟨hΔ, {
    constants := sapcStrongConstants_valid p
    strongSafe := ?_
    strongIncluded := ?_
    strongResilient := ?_
    strongRecoveredSafe := ?_
    strongRecoveredIncluded := ?_ }⟩
  · intro rho t₀ hs cap
    exact strong_safe_from_engine p E rho hΔ t₀ hs cap
  · intro rho t₀ hs cap full
    exact strong_included_from_engine p E rho hΔ t₀ hs cap full
  · intro rho T b₀ armed
    exact strong_resilient_from_engine p E rho hΔ T b₀ armed
  · intro rho hrec _
    exact strong_recovered_safe_from_engine p E rho hΔ G hG hrec
  · intro rho hrec _
    exact strong_recovered_included_from_engine p E rho hΔ G hG hrec

end AvailableChain.SAPC
end
