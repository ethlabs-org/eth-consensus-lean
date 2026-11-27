module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Saved
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Ready
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Conditional post-stop outage adapters -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams Payload)

/-- Among a slow lock's consecutive labels, at least one is outside the outage pollution
window, under the gap budget `(4k − 5)Δ`: the polluted slot starts lie in the open interval
`(start − 2Δ, stop − Δ)`, of length at most `(4k − 4)Δ`, so at most `k − 1` of them. -/
theorem exists_unpolluted_label (sp : AC.ACParams) {start stop : Time}
    (hgap : stop - start ≤ (4 * (sp.k : Time) - 5) * sp.Δ) (s : Int) :
    ∃ m : Int, s - (sp.k : Int) < m ∧ m ≤ s ∧
      (sp.ts m + 2 * sp.Δ ≤ start ∨ stop ≤ sp.ts m + sp.Δ) := by
  have hk : (2 : Int) ≤ sp.k := by exact_mod_cast sp.two_le_k
  by_contra hn
  have hfirst : start < sp.ts (s - sp.k + 1) + 2 * sp.Δ := by
    by_contra h
    exact hn ⟨s - sp.k + 1, by omega, by omega, Or.inl (le_of_not_gt h)⟩
  have hlast : sp.ts s + sp.Δ < stop := by
    by_contra h
    exact hn ⟨s, by omega, le_rfl, Or.inr (le_of_not_gt h)⟩
  simp only [AC.ACParams.ts] at hfirst hlast
  linarith

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n}

end Consensus.Goldilocks.Compose
