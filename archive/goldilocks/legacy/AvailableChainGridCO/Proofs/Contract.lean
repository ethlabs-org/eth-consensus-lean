module
public import AvailableChainGridCO.Proofs.Outage
public import AvailableChainGridCO.Proofs.CleanInclusion
public import AvailableChainGridCO.Proofs.Recovery

@[expose] public section

namespace AvailableChain.GridCO

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Grid CO satisfies the complete Draft 4.3 contract. Every field follows
from the engine and the regime premises. The parameter conditions are
a positive proposer gap and matching time units. -/
theorem gridContract_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (G : Time) (hG : 0 < G) (hΔ : E.Δ = p.Δ) :
    GridContract p G E := by
  refine ⟨hΔ, {
    constants := gridConstants_valid p G hG
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
    exact stable_resilient_from_engine p E rho hΔ G T b₀ b₁ ho.toOutageRegime
  · intro rho hrec
    exact recovered_from_engine p E rho hΔ G hG hrec

end AvailableChain.GridCO
end
