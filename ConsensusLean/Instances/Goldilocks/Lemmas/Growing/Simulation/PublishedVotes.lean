module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.PublishedBlocks
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.HandlerFields
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Groups
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
      ∃ z, ReleasedFrom S rho (rho.key y) (voteObj m z) ((simTraceAt S rho hn).time k) := by
  intro y k m _ hc
  obtain ⟨ℓ, hcall, em, hem, rfl⟩ := hc
  obtain ⟨-, hstep, -, -⟩ := simTraceAt_cutLaw S rho hn hv y k (.ac ℓ) hcall
  have hgate := AC.emits_mayVote y _ ℓ.frame _ ℓ.call em (by rw [hstep]; exact hem)
  rw [simTraceAt_mayVote S rho hn hv y k] at hgate
  rw [simTraceAt_eq] at hcall ⊢
  apply emit_released_of S rho hn hv
    (fun he hp r hr => (tick_block_vote_releases_at S rho hn hv he hp r hr).2)
    ⟨ℓ, hcall, em, hem, rfl⟩
  rw [← stateAt_voteIO S rho hn (rho.key y) 0]
  apply stateAt_ownToken_exists S rho hn hv
  rw [stateAt_mayVote S rho hn hv, ownKey_key]
  exact hgate

end Consensus.Goldilocks.Simulation
