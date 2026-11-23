module
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.SleepyGrowth.Main
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
@[expose] public section

/-! # The committee rows of R.2 at the full committee

Kind (s), a specialisation (CONTRIBUTING "Statements"): at the full committee
`K = AC.CommitteeDict.full` with `committeeSize = n`, the committee rows `IncludeSleepy` and
`GrowSleepy` (`Results/Statements/SleepyGrowth`) give the population rows over the default start,
stated here as `PopulationIncludeSleepy` and `PopulationGrowSleepy`. The full committee's start is
the default start (`AC.committeeStart_full`), its committee facts hold at the population size
(`CommitteeFacts.of_full`), and its committee support follows from `Sleepy`
(`sleepyBoundsFrom_of_sleepyRunAt`, `CommitteeBoundsFrom.of_full` at each consumption time).

* `includeSleepy_full`, `growSleepy_full`: new ⇒ old at `K = full`;
* `populationIncludeSleepy`, `populationGrowSleepy`: the population rows, proved. -/

namespace Consensus.Goldilocks.Regimes.Growing.Test

open AC (ACParams ReplayOrder Payload)

/-- R.2 inclusion under growing faults at population-sized committees, over the default start. -/
def PopulationIncludeSleepy : Prop :=
  ∀ (sp : ACParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n) (ΔF : Time),
    sp.committeeSize = sp.n →
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → Compose.NoCollRun dg tr →
    tr.SleepyRunAt H ΔF (ahead sp) →
    ∀ τ P, ReadyProposalAt tr H (catchUp sp) τ (hold sp) P →
      ∀ y t j, τ + 6 * sp.Δ ≤ t → ReadyAt tr H (catchUp sp) y t → CutAfter tr j t →
        Anc (tr.HonestBlocksAt H) P (readAfter tr y j t)

/-- R.2 growth under growing faults at population-sized committees, over the default start. -/
def PopulationGrowSleepy : Prop :=
  ∀ (sp : ACParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n) (ΔF : Time) (k : Nat),
    sp.committeeSize = sp.n →
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr → Compose.NoCollRun dg tr →
    tr.SleepyRunAt H ΔF (ahead sp) → 1 ≤ k →
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

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- The default start is the full committee's start. -/
theorem run_full (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) :
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot (AC.CommitteeDict.full sp.n)) := by
  rw [AC.committeeStart_full]
  exact hrun

/-- Under `Sleepy`, the full committee has committee support. -/
theorem committeeSleepy_full (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hsl : tr.SleepyRunAt H ΔF (ahead sp)) :
    CommitteeSleepy tr H (AC.CommitteeDict.full sp.n) := by
  have hK := fun d => Compose.Growing.CommitteeBoundsFrom.of_full hrun
    (sleepyBoundsFrom_of_sleepyRunAt hrun.antitone hsl d)
  exact ⟨fun s d h1 h6 => (hK d).slotK s d (Nat.zero_le s) h1 le_rfl h6,
    fun s d h0 h2 => (hK d).twoK s d (Nat.zero_le s) h0 le_rfl h2⟩

/-- **New ⇒ old at `K = full`: inclusion.** -/
theorem includeSleepy_full (h : IncludeSleepy) : PopulationIncludeSleepy :=
  fun sp ro dg H tr proposer ΔF hstock hrun hnc hsl =>
    h sp ro dg H tr proposer ΔF _ (run_full hrun) hnc
      (Compose.Growing.CommitteeFacts.of_full hrun hnc hstock) hsl (committeeSleepy_full hrun hsl)

/-- **New ⇒ old at `K = full`: growth.** -/
theorem growSleepy_full (h : GrowSleepy) : PopulationGrowSleepy :=
  fun sp ro dg H tr proposer ΔF k hstock hrun hnc hsl =>
    h sp ro dg H tr proposer ΔF k _ (run_full hrun) hnc
      (Compose.Growing.CommitteeFacts.of_full hrun hnc hstock) hsl (committeeSleepy_full hrun hsl)

/-- The population inclusion row, from the committee row. -/
theorem populationIncludeSleepy : PopulationIncludeSleepy := includeSleepy_full include_sleepy

/-- The population growth row, from the committee row. -/
theorem populationGrowSleepy : PopulationGrowSleepy := growSleepy_full grow_sleepy

end Consensus.Goldilocks.Regimes.Growing.Test

end
