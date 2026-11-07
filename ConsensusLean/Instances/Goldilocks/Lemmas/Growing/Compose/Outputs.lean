module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Accountable

public section

/-! # Outputs of nodes honest at their observation horizon

The node-local always rows reuse the static proofs on a retained prefix. No fault count or
sleepy invariant is transported: the only cohort is the node honest at the final observation.
-/

namespace Consensus.Goldilocks.Regimes.Growing

/-- The finalized, confirmed and head tips are nested at every honest cut. -/
theorem outputs_nested : OutputsNested := by
  intro sp ro dg H tr proposer h y i hy
  have hs := RunTrace.upTo_state_of_le (y := y) h.time_mono (le_refl (tr.time i))
  have ht := Regimes.outputs_nested sp ro dg (H (tr.time i)) (tr.upTo (tr.time i)) proposer
    (h.upTo (h.time_nonneg i)) y hy i
  simpa only [RunTrace.finalizedAt, RunTrace.confirmedAt, RunTrace.headAt, hs,
    Trace.upTo_time] using ht

/-- A node honest at the later cut has monotonically finalized tips. -/
theorem finalized_monotone : FinalizedMonotone := by
  intro sp ro dg H tr proposer h y i j hij hy
  have hsi := RunTrace.upTo_state_of_le (y := y) h.time_mono (h.time_mono hij)
  have hsj := RunTrace.upTo_state_of_le (y := y) h.time_mono (le_refl (tr.time j))
  have ht := Regimes.finalized_monotone sp ro dg (H (tr.time j)) (tr.upTo (tr.time j)) proposer
    (h.upTo (h.time_nonneg j)) y hy i j hij
  simpa only [RunTrace.finalizedAt, hsi, hsj] using ht

/-- Both always outputs carry valid chains and accepted-block provenance. -/
theorem outputs_valid : OutputsValid := by
  intro sp ro dg H tr proposer h y i hy
  have hs := RunTrace.upTo_state_of_le (y := y) h.time_mono (le_refl (tr.time i))
  have ht := Regimes.outputs_valid sp ro dg (H (tr.time i)) (tr.upTo (tr.time i)) proposer
    (h.upTo (h.time_nonneg i)) y hy i
  have conv : ∀ X, ValidOutput (tr.upTo (tr.time i)) proposer dg y i X →
      ValidOutput tr proposer dg y i X := by
    intro X hv
    obtain ⟨hX, hall⟩ := hv
    rw [hs] at hX
    refine ⟨hX, fun Z hZX hZg => ?_⟩
    rw [← hs] at hZX
    obtain ⟨hr, ⟨k, hki, hk⟩, hp, Pz, hPz, hpar, hslot⟩ := hall Z hZX hZg
    exact ⟨hr, ⟨k, hki, ((RunTrace.upTo_acceptAt _).mp hk).2⟩, hp, Pz,
      hs ▸ hPz, hpar, hslot⟩
  constructor
  · apply conv
    simpa only [RunTrace.finalizedAt, hs] using ht.1
  · apply conv
    simpa only [RunTrace.confirmedAt, hs, Trace.upTo_time] using ht.2

/-- A validator honest at both signing cuts cannot frame itself. -/
theorem non_framing : NonFraming := by
  intro sp ro dg H tr proposer h v k k' a b ha hb hv
  have hkd : tr.time k ≤ max (tr.time k) (tr.time k') := le_max_left _ _
  have hkd' : tr.time k' ≤ max (tr.time k) (tr.time k') := le_max_right _ _
  exact Regimes.non_framing sp ro dg (H (max (tr.time k) (tr.time k')))
    (tr.upTo (max (tr.time k) (tr.time k'))) proposer
    (h.upTo ((h.time_nonneg k).trans hkd)) v hv k k' a b
    ((RunTrace.upTo_signAt _).mpr ⟨hkd, ha⟩) ((RunTrace.upTo_signAt _).mpr ⟨hkd', hb⟩)

end Consensus.Goldilocks.Regimes.Growing

end
