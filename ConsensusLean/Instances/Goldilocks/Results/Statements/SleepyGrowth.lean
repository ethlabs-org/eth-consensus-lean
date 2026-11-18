module
public import ConsensusLean.Instances.Goldilocks.Results.Spec.SleepyGrowth
public import ConsensusLean.Instances.Goldilocks.Results.Spec.CanonicalTrace
public import ConsensusLean.Instances.Goldilocks.AsChainShape
public import ConsensusLean.Spec.Shape.Run
public import ConsensusLean.Spec.Problem.Regimes
public import ConsensusLean.Spec.Problem.Network
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Premises

@[expose] public section

/-! # Sleepy strict growth (R.2) under growing faults, at a committee

* `Regimes.Growing.IncludeSleepy`, `Regimes.Growing.GrowSleepy`: the node rows.
* `Obligations.Growing.SleepyGrowFinite`: the finite growth row of the engine at every vote
  binding, on the canonical growing trace (`Results/Spec/CanonicalTrace`), through a bound `b` with
  `t + (4k + 6)Δ ≤ b ≤ horizon`.

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

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Shape
open Consensus.Model (pubOf)

/-- **R.2, growth, of the engine through a finite horizon.** At every vote binding `S`, for a
valid engine run with no observed hash collision, `t ≥ 0`, `k ≥ 1` and
`t + (4k + 6)Δ ≤ b ≤ horizon`: under synchrony through `b`, the sleepy budget on `[0, b]`
(threshold `1/2`, the node's catch-up `18Δ`, look-ahead `5Δ`), committee sleepy participation of
the run's selection on `[0, b]` (threshold `θ ≥ 1/2`, look-back `η`, catch-up `c` with
`8Δ ≤ c + 1`, look-ahead `W ≥ 5Δ`), and one proposer ready at its slot start and honest through its
hold in every window of `k` slots up to `t + (4k + 6)Δ` on the canonical growing trace: some
proposal released at `τ > t` by a proposer ready at `τ` and honest through its hold is in every
ready read at `t + (4k + 6)Δ`, in no ready read at `t`, and each ready read at `t` is an ancestor
of each ready read at `t + (4k + 6)Δ`. Nothing is claimed beyond the horizon. -/
def SleepyGrowFinite : Prop :=
  ∀ (S : Setup) {V : Type} [Fintype V] [DecidableEq V] (E : Env V)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V),
    rho.ExecutionValid → ¬ rho.HashCollision →
    ∀ (t b : Time) (k : Nat), 0 ≤ t → 1 ≤ k →
    t + (4 * k + 6) * (S.params (pubOf E) hn).Δ ≤ b → b ≤ rho.horizon →
    rho.log.SyncUntil rho.point b →
    rho.point.SleepyOn (1 / 2) (Regimes.catchUp (S.params (pubOf E) hn))
      (5 * (S.params (pubOf E) hn).Δ) 0 b →
    ∀ (θ : ℚ) (η c W : Time), 1 / 2 ≤ θ → 8 * (S.params (pubOf E) hn).Δ ≤ c + 1 →
    5 * (S.params (pubOf E) hn).Δ ≤ W →
    rho.point.CommitteeSleepyOn
      ((shapeProgress (goldilocks S) V).toExternal.selected rho.point.env
        ((shapeProgress (goldilocks S) V).toExternal.ext ⟨E, rho⟩)) θ η c W 0 b →
    Regimes.Growing.ProposerRecurrence (simTraceAt S rho hn) (honestKeysAt S rho)
      (runProposer S rho hn) (Regimes.catchUp (S.params (pubOf E) hn)) k
      (Regimes.Growing.hold (S.params (pubOf E) hn)) 0
      (t + (4 * k + 6) * (S.params (pubOf E) hn).Δ) →
    ∃ τ P, t < τ ∧
      Regimes.Growing.ReadyProposalAt (simTraceAt S rho hn) (honestKeysAt S rho)
        (Regimes.catchUp (S.params (pubOf E) hn)) τ
        (Regimes.Growing.hold (S.params (pubOf E) hn)) P ∧
      (∀ y j, Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho)
          (Regimes.catchUp (S.params (pubOf E) hn)) y
          (t + (4 * k + 6) * (S.params (pubOf E) hn).Δ) →
        Regimes.CutAfter (simTraceAt S rho hn) j (t + (4 * k + 6) * (S.params (pubOf E) hn).Δ) →
        Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho)) P
          (Regimes.readAfter (simTraceAt S rho hn) y j
            (t + (4 * k + 6) * (S.params (pubOf E) hn).Δ))) ∧
      (∀ x jx, Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho)
          (Regimes.catchUp (S.params (pubOf E) hn)) x t →
        Regimes.CutAfter (simTraceAt S rho hn) jx t →
        ¬ Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho)) P
          (Regimes.readAfter (simTraceAt S rho hn) x jx t)) ∧
      ∀ x jx y j, Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho)
          (Regimes.catchUp (S.params (pubOf E) hn)) x t →
        Regimes.CutAfter (simTraceAt S rho hn) jx t →
        Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho)
          (Regimes.catchUp (S.params (pubOf E) hn)) y
          (t + (4 * k + 6) * (S.params (pubOf E) hn).Δ) →
        Regimes.CutAfter (simTraceAt S rho hn) j (t + (4 * k + 6) * (S.params (pubOf E) hn).Δ) →
        Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho))
          (Regimes.readAfter (simTraceAt S rho hn) x jx t)
          (Regimes.readAfter (simTraceAt S rho hn) y j
            (t + (4 * k + 6) * (S.params (pubOf E) hn).Δ))

end Consensus.Goldilocks.Obligations.Growing

end
