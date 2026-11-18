module
public import ConsensusLean.Instances.Goldilocks.Results.Spec.SleepyGrowth
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Premises

@[expose] public section

/-! # Sleepy strict growth (R.2) under growing faults, at a committee

The R.2 rows for a time-indexed honest set `H` (antitone), over `Growing.GoldilocksRun` from the
committee start of a slot dictionary `K` (`SA.committeeStart`), with the committee facts of `K`
(`CommitteeFacts`) and the committee support `CommitteeSleepy`. Readers, proposers and the sleepy
look-ahead are those of `Statements/Regimes/Growing`; the margins (`τ + 6Δ`, `D = (4k + 6)Δ`) are
those of the static rows.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Regimes.Growing

open SA (SAParams ReplayOrder Payload)

/-- **R.2, inclusion, under growing faults, at a committee.** From the committee start of a slot
dictionary `K`, with its committee facts and committee support, under `Sleepy` with look-ahead
`ahead`, every honest proposal released at `τ` by a proposer ready at `τ` and still honest at
`τ + hold` is in the confirmed read of every node ready at `t`, for every `t ≥ τ + 6Δ`. -/
def IncludeSleepy : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n) (ΔF : Time)
    (K : SA.CommitteeDict sp.n),
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (SA.committeeStart sp.genesisRoot K) →
    Compose.NoCollRun dg tr → Compose.Growing.CommitteeFacts tr H K →
    tr.SleepyRunAt H ΔF (ahead sp) → CommitteeSleepy tr H K →
    ∀ τ P, ReadyProposalAt tr H (catchUp sp) τ (hold sp) P →
      ∀ y t j, τ + 6 * sp.Δ ≤ t → ReadyAt tr H (catchUp sp) y t → CutAfter tr j t →
        Anc (tr.HonestBlocksAt H) P (readAfter tr y j t)

/-- **R.2, growth, under growing faults, at a committee.** From the committee start of a slot
dictionary `K`, with its committee facts and committee support, under `Sleepy` with look-ahead
`ahead`, for every `t ≥ 0` with one proposer ready and honest through its hold in every window of
`k ≥ 1` slots up to `t + D`, `D = (4k + 6)Δ`, some honest proposal `P` released at `τ > t` by a
proposer ready at `τ` and honest through its hold is a new common entry at `t + D`: in the read at
`t + D` of every node ready then, in none of the reads at `t` of the nodes ready then, and each of
those reads is an ancestor of each ready read at `t + D`. -/
def GrowSleepy : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n) (ΔF : Time) (k : Nat)
    (K : SA.CommitteeDict sp.n),
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (SA.committeeStart sp.genesisRoot K) →
    Compose.NoCollRun dg tr → Compose.Growing.CommitteeFacts tr H K →
    tr.SleepyRunAt H ΔF (ahead sp) → CommitteeSleepy tr H K → 1 ≤ k →
    let D := (4 * k + 6) * sp.Δ
    ∀ t, 0 ≤ t → ProposerRecurrence tr H proposer (catchUp sp) k (hold sp) 0 (t + D) →
      ∃ τ P, t < τ ∧ ReadyProposalAt tr H (catchUp sp) τ (hold sp) P ∧
        (∀ y j, ReadyAt tr H (catchUp sp) y (t + D) → CutAfter tr j (t + D) →
          Anc (tr.HonestBlocksAt H) P (readAfter tr y j (t + D))) ∧
        (∀ x jx, ReadyAt tr H (catchUp sp) x t → CutAfter tr jx t →
          ¬ Anc (tr.HonestBlocksAt H) P (readAfter tr x jx t)) ∧
        ∀ x jx y j, ReadyAt tr H (catchUp sp) x t → CutAfter tr jx t →
          ReadyAt tr H (catchUp sp) y (t + D) → CutAfter tr j (t + D) →
          Anc (tr.HonestBlocksAt H) (readAfter tr x jx t) (readAfter tr y j (t + D))

end Consensus.Goldilocks.Regimes.Growing

end
