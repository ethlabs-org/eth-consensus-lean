module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Accountable
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.FG.Safety

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

private theorem fg_run {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {H : Time → Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) :
    Consensus.Goldilocks.Growing.FGLocalRun (goldilocksNode sp ro).genesisPayload H
      (tr.HonestBlocksAt H) tr.projFG :=
  have h := SA.interface_requirements sp (List (FG.Att sp.n)) ro
  Compose.Growing.fg_projection _ _ dg H _ tr proposer
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, SA.proposal_payload_valid sp _ ro⟩
    hrun.genesis_root_ok hrun.toLocalRun hnc

private theorem store_eq {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {H : Time → Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) :
    tr.projFG.store y i = (tr.state y i).fg := by
  have h := Compose.projFG_state (hrun.toLocalRun.upTo (hrun.time_nonneg i)) hy i
  rw [RunTrace.upTo_projFG,
    Trace.upTo_state tr.projFG y (i := i) (fun k hk => hrun.time_mono hk.le),
    RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h
  exact congrArg Prod.fst h

/-- Conflicting finalizations expose a slashable quorum intersection in the held chains. -/
theorem final_accountable : FinalAccountable := by
  intro sp ro dg H tr proposer hrun hnc y z i j hy hz hne
  have hr := fg_run hrun hnc
  obtain ⟨c₁, σ₁, h₁, hF₁, hU₁, hc₁, _, X₁, hX₁, hb₁⟩ := hr.finalized_chain hy
  obtain ⟨c₂, σ₂, h₂, hF₂, hU₂, hc₂, _, X₂, hX₂, hb₂⟩ := hr.finalized_chain hz
  rw [store_eq hrun hy] at hF₁ hU₁ hc₁ hX₁ hb₁
  rw [store_eq hrun hz] at hF₂ hU₂ hc₂ hX₂ hb₂
  obtain ⟨S, hS, hSv⟩ := FG.accountable_safety sp.toParams.fg c₁ c₂ σ₁ σ₂ h₁ h₂
    (fun h => hne (hc₂ _ hU₁ (hF₁ ▸ h))) (fun h => hne (hc₁ _ hU₂ (hF₂ ▸ h)).symm)
  have hmem : ∀ a ∈ sp.toParams.fg.chainAtts c₁ ++ sp.toParams.fg.chainAtts c₂,
      a ∈ ChainAtts tr y i X₁ ∪ ChainAtts tr z j X₂ := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨Y, hY, hYX, haY⟩ := hb₁ a ha
      exact Or.inl ⟨Y, hY, hYX, haY⟩
    · obtain ⟨Y, hY, hYX, haY⟩ := hb₂ a ha
      exact Or.inr ⟨Y, hY, hYX, haY⟩
  refine ⟨X₁, hX₁, X₂, hX₂, S, hS, fun v hv => ?_⟩
  obtain ⟨a, ha, b, hb, hav, hab⟩ := hSv v hv
  exact ⟨a, hmem a ha, b, hmem b hb, hav, hab⟩

/-- Finalized tips agree with the quorum bound charged at the later reader horizon. -/
theorem finalized_safe : FinalizedSafe := by
  intro sp ro dg H tr proposer hrun hnc y z i j hy hz hf
  have h := (fg_run hrun hnc).finalized_safety hy hz hf
  rwa [store_eq hrun hy, store_eq hrun hz] at h

end Consensus.Goldilocks.Regimes.Growing

end
