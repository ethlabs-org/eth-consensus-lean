module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.PublishedBlocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EmitRelease

public section

/-! # Publication of votes emitted by the growing canonical trace -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- An emitted vote is released at its cut's time, including pending votes at restart. -/
theorem simTraceAt_vote_released (hv : rho.ExecutionValid) :
    ∀ y k m, y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time k) →
      (simTraceAt S rho hn).EmitAt y k m →
      ReleasedFrom S rho (rho.key y) (voteObj m) ((simTraceAt S rho hn).time k) := by
  rw [simTraceAt_eq]
  intro y k m _ hc
  exact emit_released_of S rho hn hv
    (fun he hp r hr => (tick_block_vote_releases_at S rho hn hv he hp r hr).2) hc

end Consensus.Goldilocks.Simulation
