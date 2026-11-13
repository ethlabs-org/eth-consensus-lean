module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.PublishedBlocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Evidence
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.BlockView

public section

/-! # Collision freedom of the canonical trace under growing faults

Every block call, including a refused delivery, exposes its canonical object at the
corresponding engine event. The reader is honest at that event's cut; it need not remain
honest at the final cut. Tagged genesis and injectivity of observed headers then suffice.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- An occurring block is observed while its engine reader is still honest, even if the
reader is compromised later. Refused deliveries count as observations too. -/
theorem occurring_observed_at (hv : rho.ExecutionValid)
    {B : Blk (S.params (pubOf E) hn)} (hB : (simTraceAt S rho hn).Occurs B) :
    B.parent ≠ none ∧ rho.ObservedItem (headerOf (S.params (pubOf E) hn) B) := by
  rw [simTraceAt_eq] at hB
  obtain ⟨hp, i, ev, he, hb⟩ := block_call_in_view_of_releases S rho hn
    (fun he hp r hr => (tick_block_vote_releases_at S rho hn hv he hp r hr).1) hB
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  refine ⟨hp, blockObj _ B, ⟨ev.node, i + 1, by omega, ?_, hb⟩, rfl⟩
  change ev.node ∉ rho.faultyAt (rho.cutTime (i + 1))
  simpa only [Model.Run.cutTime, he, Option.elim_some] using hv.honest_only ev
    (List.mem_of_getElem? he)

/-- Absence of observed engine hash collisions gives collision freedom for every canonical
block call, without a constant-fault premise. -/
theorem noCollRun_simTraceAt (hv : rho.ExecutionValid) (hc : ¬ rho.HashCollision) :
    Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn) := by
  rw [simTraceAt_eq]
  exact noCollRun_of_observed S rho hn hc fun B hB =>
    occurring_observed_at S rho hn hv (by rwa [simTraceAt_eq])

end Consensus.Goldilocks.Simulation
