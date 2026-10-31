module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Votes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Confirmed

public section

/-! # Goldilocks Healing: H.2, AC inclusion from the retention premise

H.2 over driven AC traces of the SA with their frames, under `Healthy(g)`, `Catch(2Δ)` and
`Inv(t₀)` (`InclusionRun`), assembled as in workbench `h2-open-items.md`: the locks are settled
from `t₀ + 2Θ + 4Δ` (§5 drain and §6.1 raw-origin transfer, `H2Transfer`), so before every
proposal of a slot `p` with `t_p ≥ t₀ + 2Θ + 8Δ`; then (i) from `Geo(P)` (§§1, 4, 6, `H2Votes`)
and (ii) from the unanimous slot-`p` votes (§7, `H2Confirmed`). H.1 does not route through
here. -/

namespace Consensus.Goldilocks.SA

/-- **H.2, AC inclusion from the retention premise.** -/
theorem ac_inclusion (sp : SAParams) : ACInclusion (sp := sp) := by
  intro FGP ro H U tr proposer g t₀ hrun hdr hh hc hg hinv p P hpH hP hp
  have hI : InclusionRun tr H U proposer g t₀ := ⟨⟨hrun, hdr, hh, hc⟩, hg, hinv⟩
  have hΔ := sp.toParams.hΔ
  have hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ) :=
    (h2_locks_settled hI).mono (by linarith)
  exact ⟨h2_proposal_votes hI hpH hP hp hset, h2_proposal_confirmed hI hpH hP hp⟩

end Consensus.Goldilocks.SA

end
