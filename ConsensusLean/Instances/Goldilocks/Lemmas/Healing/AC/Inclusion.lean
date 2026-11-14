module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Votes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Confirmed
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: H.2, AC inclusion from the retention premise

H.2 over driven AC traces of the SA with their frames, under `Healthy(g)`, `Catch(2Δ)` and `Inv(t₀)`
(`InclusionRun`), assembled as follows: the locks are settled from `t₀ + 2Θ + 4Δ` (drain and
raw-origin transfer, `H2Transfer`), so before every proposal of a slot `p` with
`t_p ≥ t₀ + 2Θ + 8Δ`; then (i) from `Geo(P)` (`H2Votes`) and (ii) from the unanimous slot-`p` votes
(`H2Confirmed`). H.1 does not route through here. -/

namespace Consensus.Goldilocks.SA

/-- **H.2, AC inclusion from the retention premise**, for population-sized committees. -/
theorem ac_inclusion (sp : SAParams) (hstock : sp.committeeSize = sp.n) :
    ACInclusion (sp := sp) := by
  intro FGP ro H U tr proposer g t₀ hrun hdr hh hc hg hinv p P hpH hP hp
  have hI : InclusionRun tr H U proposer g t₀ := ⟨⟨hrun, hdr, hh, hc, hstock⟩, hg, hinv⟩
  have hΔ := sp.toParams.hΔ
  have hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ) :=
    (h2_locks_settled hI).mono (by linarith)
  exact ⟨h2_proposal_votes hI hpH hP hp hset, h2_proposal_confirmed hI hpH hP hp⟩

end Consensus.Goldilocks.SA

end
