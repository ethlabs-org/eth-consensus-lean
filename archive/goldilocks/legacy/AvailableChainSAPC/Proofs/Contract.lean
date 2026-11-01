module
public import AvailableChainSAPC.Proofs.RecoverySafety

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- SA-PC satisfies the complete Draft 4.3 bundle. Only Recovery uses
full participation and the derived cap; the base fault scopes are unchanged. -/
theorem sapcContract_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (G : Time) (hG : 0 < G) (hΔ : E.Δ = p.Δ) :
    SAPCContract p G E := by
  refine ⟨hΔ, {
    constants := sapcConstants_valid p G hG
    confirmedSafe := ?_
    stableSafe := ?_
    monotone := ?_
    nested := outputOrder p
    confirmedIncluded := ?_
    stableIncluded := ?_
    stableIncludedFast := ?_
    stableResilient := ?_
    stableResilientFast := fastP1_from_engine p E G hΔ
    recovered := ?_ }⟩
  · intro rho t₀ hs
    exact (clean_safety_from_engine p E rho hΔ t₀ hs).2
  · intro rho t₀ hs
    exact (clean_safety_from_engine p E rho hΔ t₀ hs).1
  · intro rho t₀ hs
    have safe := clean_safety_from_engine p E rho hΔ t₀ hs
    exact ⟨safe.2.monotone, safe.1.monotone⟩
  · intro rho t₀ hs
    exact (included_from_engine p E rho hΔ t₀ hs).2
  · intro rho t₀ hs
    exact stable_included_from_engine p E rho hΔ G t₀ hs
  · intro rho t₀ hs
    exact fast_included_from_engine p E rho hΔ G t₀ hs
  · intro rho T b₀ b₁ ho
    exact stable_resilient_from_engine p E rho hΔ G T b₀ b₁ ho
  · intro rho hrec
    exact recovered_from_engine p E rho hΔ G hG hrec

end AvailableChain.SAPC
end
