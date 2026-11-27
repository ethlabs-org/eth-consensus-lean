module
public import ConsensusLean.Instances.Goldilocks.Results.Spec.SleepyGrowth
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run

@[expose] public section

/-! # Optimistic inclusion under growing faults, at a committee

* `Regimes.Growing.OptimisticInclusion`: with the optimistic confirmation on, an honest proposal
  that the honest votes of its slot all back, and whose slot committee has at least three
  quarters of its public size among the members awake and joined one delay after the slot start
  and honest through `t_p + 2Δ`, is in the confirmed read of every ready node awake and joined
  through `[t_p, t_p + 2Δ]`, from `t_p + 2Δ` on, four delays earlier than R.2's `t_p + 6Δ`.

An internal result on confirmation speed with an adversary of at most a quarter of the committee:
not a correctness row, not part of the challenge or the obligations. The setting is R.2's
(`IncludeSleepy`): `Growing.GoldilocksRun` from the committee start of a slot dictionary `K`, with
its committee facts and committee support, under `Sleepy` with look-ahead `ahead`; readers and
proposers are those of `Statements/Regimes/Growing`.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Regimes.Growing

open AC (ACParams Payload)

/-- **Optimistic inclusion, under growing faults, at a committee.** In R.2's setting, with the
optimistic confirmation on: let `P` be an honest proposal released at the start `t_p` of slot `p`
by a proposer ready then and still honest at `t_p + hold`, such that every slot-`p` vote of a node
honest at `t_p + Δ` has head `P`, and such that at least three quarters of the committee size are
members of slot `p`'s committee awake and joined at `t_p + Δ` and still honest at `t_p + 2Δ`, so
honest through the optimistic window (an adversary of at most a quarter of the committee). Then
`P` is in the confirmed read of every node ready at `t` and awake and joined throughout
`[t_p, t_p + 2Δ]`, for every `t ≥ t_p + 2Δ`. -/
def OptimisticInclusion : Prop :=
  ∀ (sp : ACParams)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp) (proposer : Nat → Fin sp.n) (ΔF : Time)
    (K : AC.CommitteeDict sp.n),
    sp.optimistic = true →
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K) →
    Compose.NoCollRun dg tr → Compose.Growing.CommitteeFacts tr H K →
    tr.SleepyRunAt H ΔF (ahead sp) → CommitteeSleepy tr H K →
    ∀ (p : Nat) P, ReadyProposalAt tr H (catchUp sp) (sp.ts p) (hold sp) P →
      Healing.Unanimous tr (H (sp.ts p + sp.Δ)) p P →
      3 * sp.committeeSize ≤
        4 * {x | x ∈ K.committee p ∧ x ∈ H (sp.ts p + 2 * sp.Δ) ∧
          tr.awake x (sp.ts p + sp.Δ) ∧ tr.JoinedAt x (sp.ts p + sp.Δ)}.ncard →
      ∀ y t j, sp.ts p + 2 * sp.Δ ≤ t → ReadyAt tr H (catchUp sp) y t →
        (∀ d, sp.ts p ≤ d → d ≤ sp.ts p + 2 * sp.Δ → tr.awake y d ∧ tr.JoinedAt y d) →
        CutAfter tr j t → Anc (tr.HonestBlocksAt H) P (readAfter tr y j t)

end Consensus.Goldilocks.Regimes.Growing

end
