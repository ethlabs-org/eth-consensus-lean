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
open SA (Vote blockVotes)

variable {binding : VoteBinding}

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- A payload object signed by a key honest at processing has an earlier genuine release. -/
theorem block_payload_source_at (hv : rho.ExecutionValid) {k : Nat} {y}
    {B : Blk (S.params (pubOf E) hn)} (hc : (simTraceAt S rho hn).BlockCallAt y k B)
    {o : Wire (Fintype.card V) S.vote} (ho : o ∈ payloadObjs B.fgPayload B.acPayload)
    {u : V} (hu : u ∉ rho.faultyAt ((simTraceAt S rho hn).time k))
    (hsign : rho.signerOf o = some u) :
    ∃ i t, cutMap S rho hn (i + 1) ≤ k ∧ rho.SendsAt u i t ∧ o ∈ rho.releasesAt i := by
  rw [simTraceAt_eq] at hc hu
  exact block_payload_source_of S rho hn hv (preNode_releasable_at S rho hn hv) hc ho hu hsign

/-- Votes carried by processed blocks were emitted while their signer was still honest. -/
theorem simTraceAt_carried_vote_unforgeable (hv : rho.ExecutionValid) :
    ∀ y i B, y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i) →
      (simTraceAt S rho hn).BlockCallAt y i B →
      ∀ v ∈ blockVotes B, v.val ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i) →
        ∃ j < i, (simTraceAt S rho hn).EmitAt v.val j v := by
  intro y k B _ hc m hm hh
  have hmem : voteObj (binding := S.vote) m ∈ payloadObjs B.fgPayload B.acPayload :=
    List.mem_append_right _ (List.mem_map.mpr ⟨m, List.mem_append_left _ hm, rfl⟩)
  have ht : (simTraceAt S rho hn).time k ≤ rho.horizon := by
    obtain ⟨acc, _, hl⟩ := hc
    exact simTraceAt_labelled_time_le S rho hn hv (by rw [hl]; simp)
  have hh' : rho.key m.val ∉ rho.faultyAt ((simTraceAt S rho hn).time k) := by
    rwa [mem_honestKeysAt_iff, min_eq_left ht] at hh
  obtain ⟨i, t, hik, hs, hr⟩ := block_payload_source_at S rho hn hv hc hmem hh'
    (show rho.signerOf (voteObj m) = some (rho.key m.val) from rfl)
  obtain ⟨q, hq, he⟩ := released_vote_cut_at S rho hn hv hs hr
  exact ⟨q, hq.trans_le hik, by simpa only [ownKey_key] using he⟩

end Consensus.Goldilocks.Simulation
