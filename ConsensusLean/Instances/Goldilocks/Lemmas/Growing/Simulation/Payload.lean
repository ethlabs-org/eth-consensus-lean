module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Votes
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PayloadSource

public section

/-! # Provenance of payloads at their processing time

Honesty is checked at the consuming block cut. It transports backward to the proposal view
or the delivery credentials, never forward across a compromise.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- A payload object signed by a key honest at processing has an earlier genuine release. -/
theorem block_payload_source_at (hv : rho.ExecutionValid) {k : Nat} {y}
    {B : Blk (S.params (pubOf E) hn)} (hc : (simTraceAt S rho hn).BlockCallAt y k B)
    {o : Wire (Fintype.card V) S.vote} (ho : o ∈ payloadObjs B.fgPayload B.acPayload)
    {u : V} (hu : u ∉ rho.faultyAt ((simTraceAt S rho hn).time k))
    (hsign : rho.signerOf o = some u) :
    ∃ i t, cutMap S rho hn (i + 1) ≤ k ∧ rho.SendsAt u i t ∧ o ∈ rho.releasesAt i := by
  rw [simTraceAt_eq] at hc hu
  exact block_payload_source_of S rho hn hv (preNode_releasable_at S rho hn hv) hc ho hu hsign

end Consensus.Goldilocks.Simulation
