module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.PublishedBlocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Chains
import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.BlockView
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeBlockView

public section

/-! # Collision freedom of the canonical trace under growing faults

Every block call, including a refused delivery, exposes its canonical object at the
corresponding engine event. The reader is honest at that event's cut; it need not remain
honest at the final cut. Tagged genesis and injectivity of observed headers then suffice.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- An occurring block's object is observed while its engine reader is still honest, even if
the reader is compromised later. Refused deliveries count as observations too. -/
theorem occurs_blockObj_observed_at (hv : rho.ExecutionValid)
    {B : Blk (S.params (pubOf E) hn)} (hB : (simTraceAt S rho hn).Occurs B) :
    B.parent ≠ none ∧ blockObj (binding := S.vote) _ B ∈ rho.Observed := by
  rw [simTraceAt_eq] at hB
  obtain ⟨hp, i, ev, he, hb⟩ := block_call_in_view_of_releases S rho hn
    (fun he hp r hr => (tick_block_vote_releases_at S rho hn hv he hp r hr).1) hB
  exact ⟨hp, NodeAsChainShape.CanonicalTrace.observed_of_event_view rho hv he hb⟩

/-- An occurring block is observed while its engine reader is still honest. -/
theorem occurring_observed_at (hv : rho.ExecutionValid)
    {B : Blk (S.params (pubOf E) hn)} (hB : (simTraceAt S rho hn).Occurs B) :
    B.parent ≠ none ∧ rho.ObservedItem (headerOf (S.params (pubOf E) hn) B) :=
  have h := occurs_blockObj_observed_at S rho hn hv hB
  ⟨h.1, blockObj _ B, h.2, rfl⟩

/-- Absence of observed engine hash collisions gives collision freedom for every canonical
block call, without a constant-fault premise. -/
theorem noCollRun_simTraceAt (hv : rho.ExecutionValid) (hc : ¬ rho.HashCollision) :
    Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn) := by
  rw [simTraceAt_eq]
  exact noCollRun_of_observed S rho hn hc fun B hB =>
    occurring_observed_at S rho hn hv (by rwa [simTraceAt_eq])

end Consensus.Goldilocks.Simulation
