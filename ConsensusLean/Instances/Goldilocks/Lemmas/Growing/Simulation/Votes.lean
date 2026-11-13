module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Release
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Events
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Unforgeable

public section

/-! # Genuine vote releases in the canonical growing trace -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)
open SA (Vote)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- A genuine release of a canonical vote comes from a local emission before the end cut. -/
theorem released_vote_cut_at (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {t : Time} (hs : rho.SendsAt v i t) {m : Vote (Fintype.card V)}
    (hb : voteObj m ∈ rho.releasesAt i) :
    ∃ k < cutMap S rho hn (i + 1), (simTraceAt S rho hn).EmitAt (rho.ownKey v) k m := by
  rw [simTraceAt_eq]
  exact released_vote_cut_of S rho hn hv hs (event_honest_zero S rho hv)
    (preNode_releasable_at S rho hn hv) hb

/-- A signer still honest when its message is processed genuinely emitted it earlier. -/
theorem simTraceAt_msg_unforgeable (hv : rho.ExecutionValid) :
    ∀ y i (m : Vote (Fintype.card V)), y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i) →
      (simTraceAt S rho hn).MsgCallAt y i m →
      m.val ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i) →
        ∃ j < i, (simTraceAt S rho hn).EmitAt m.val j m := by
  rw [simTraceAt_eq]
  rintro y k m _ hc hhon
  have hl : (simTrace S rho hn).label k ≠ none := by
    obtain ⟨_, ⟨_, hl⟩, _⟩ := hc
    rw [hl]; simp
  refine msgCall_emit_of_released S rho hn hv hc ?_ fun hs hb => ?_
  · rwa [mem_honestKeysAt_iff, min_eq_left (simTrace_labelled_time_le S rho hn hv hl)] at hhon
  · simpa only [simTraceAt_eq, ownKey_key] using released_vote_cut_at S rho hn hv hs hb

end Consensus.Goldilocks.Simulation
