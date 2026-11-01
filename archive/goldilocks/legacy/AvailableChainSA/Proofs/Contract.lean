module
public import AvailableChainSA.Proofs.FastOutage
public import AvailableChainSA.Proofs.Outage
public import AvailableChainSA.Proofs.Recovery

@[expose] public section
namespace AvailableChain.SA
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- SA satisfies the complete Draft 4.3 contract, with slow arming and one
release level. Every run premise is supplied by the fixed contract regimes. -/
theorem saContract_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (G : Time) (hG : 0 < G) (hΔ : E.Δ = p.Δ) :
    SAContract p G E := by
  refine ⟨hΔ, {
    constants := saConstants_valid p G hG
    confirmedSafe := ?_
    stableSafe := ?_
    monotone := ?_
    nested := outputOrder p
    confirmedIncluded := ?_
    stableIncluded := ?_
    stableIncludedFast := ?_
    stableResilient := ?_
    stableResilientFast := ?_
    recovered := ?_ }⟩
  · intro rho t₀ hs
    exact (clean_safety_from_engine p E rho hΔ t₀ hs).2
  · intro rho t₀ hs
    exact (clean_safety_from_engine p E rho hΔ t₀ hs).1
  · intro rho t₀ hs
    exact monotone_from_engine p E rho hΔ t₀ hs
  · intro rho t₀ hs
    exact included_from_engine p E rho hΔ t₀ hs
  · intro rho t₀ hs
    exact included_from_engine p E rho hΔ t₀ hs.toSleepyRegime
  · intro rho t₀ hs
    exact included_from_engine p E rho hΔ t₀ hs.toSleepyRegime
  · intro rho T b₀ b₁ ho
    exact stable_resilient_from_engine p E rho hΔ G T b₀ b₁ ho
  · intro rho T b₀ b₁ ho
    exact fastP1_from_engine p E G hΔ rho T b₀ b₁ ho
  · intro rho hrec
    exact recovered_from_engine p E rho hΔ G hrec

end AvailableChain.SA
end
