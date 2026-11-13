module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Events
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Release
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Unforgeable

public section

/-! # Genuine block releases under growing faults

Release analysis needs only the sender's local proposal inventory. It does not replace the
time-indexed honest set by a terminal one.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- A genuine block release originated in a proposer tick preceding its release cut. -/
theorem released_block_cut_at (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {t : Time} (hs : rho.SendsAt v i t)
    {B : Blk (S.params (pubOf E) hn)} (hpar : B.parent ≠ none)
    (hroot : B.RootOk (digestOf S rho))
    (hb : blockObj (S.params (pubOf E) hn) B ∈ rho.releasesAt i) :
    ∃ k < cutMap S rho hn (i + 1), (simTraceAt S rho hn).OwnBlockAt B.proposer k B := by
  rw [simTraceAt_eq]
  exact released_block_cut_of S rho hn hv hs (event_honest_zero S rho hv)
    (preNode_releasable_at S rho hn hv)
    (fun C hpC hrC h => blockObj_fields S rho hn hpar hpC hroot hrC h) hb

/-- A proposer honest at delivery cannot have its block forged before that delivery.
After compromise this conclusion is deliberately unavailable. -/
theorem simTraceAt_block_unforgeable (hv : rho.ExecutionValid) :
    ∀ y i B, y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i) →
      (simTraceAt S rho hn).BlockCallAt y i B →
      B.proposer ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i) →
      ∃ j ≤ i, (simTraceAt S rho hn).OwnBlockAt B.proposer j B := by
  rw [simTraceAt_eq]
  rintro y k B _ hc hhon
  have hl : (simTrace S rho hn).label k ≠ none := by
    obtain ⟨_, _, hl⟩ := hc
    rw [hl]; simp
  refine blockCall_ownBlock_of_released S rho hn hv hc ?_ fun hs hpar hroot hb => ?_
  · rwa [mem_honestKeysAt_iff, min_eq_left (simTrace_labelled_time_le S rho hn hv hl)] at hhon
  · simpa only [simTraceAt_eq] using released_block_cut_at S rho hn hv hs hpar hroot hb

end Consensus.Goldilocks.Simulation
