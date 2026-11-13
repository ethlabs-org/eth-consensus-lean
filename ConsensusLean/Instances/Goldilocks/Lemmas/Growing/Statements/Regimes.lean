module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Const

public section

/-! # The growing-fault regime and service rows imply the static rows

At `H := fun _ => H₀` every statement of `Statements/Regimes/Growing` and
`Statements/Compose/Growing/Service` is at least its static counterpart: the run, the blocks held
while honest and `SleepyRunAt` (at every look-ahead) are the static ones
(`Lemmas/Growing/Run/Const`), and every honesty test at a time is `· ∈ H₀`. So the growing-fault
statements weaken no static statement. -/

namespace Consensus.Goldilocks

open SA (SAParams ReplayOrder Payload)

namespace Regimes

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Set (Fin sp.n)}

theorem Growing.readyAt_const {c : Time} {y : Fin sp.n} {t : Time} :
    Growing.ReadyAt tr (fun _ => H) c y t ↔
      _root_.Consensus.Goldilocks.Regimes.ReadyAt tr H c y t :=
  Iff.rfl

theorem Growing.readyProposalAt_const {c τ h : Time} {P : SA.Blk sp.n (List (FG.Att sp.n))} :
    Growing.ReadyProposalAt tr (fun _ => H) c τ h P ↔
      _root_.Consensus.Goldilocks.Regimes.ReadyProposalAt tr H c τ P :=
  ⟨fun ⟨p, kP, hr, _, hP, ht⟩ => ⟨p, kP, hr, hP, ht⟩,
    fun ⟨p, kP, hr, hP, ht⟩ => ⟨p, kP, hr, hr.1, hP, ht⟩⟩

theorem Growing.proposerRecurrence_const {proposer : Nat → Fin sp.n} {c : Time} {k : Nat}
    {h a b : Time} :
    Growing.ProposerRecurrence tr (fun _ => H) proposer c k h a b ↔
      _root_.Consensus.Goldilocks.Regimes.ProposerRecurrence tr H proposer c k a b := by
  constructor
  · intro hr s₀ ha hb
    obtain ⟨s, h1, h2, h3, -⟩ := hr s₀ ha hb
    exact ⟨s, h1, h2, h3⟩
  · intro hr s₀ ha hb
    obtain ⟨s, h1, h2, h3⟩ := hr s₀ ha hb
    exact ⟨s, h1, h2, h3, h3.1⟩

end Regimes

open Regimes

/-- The growing-fault R.1 implies the static R.1. -/
theorem sleepySafe_of_growing (h : Regimes.Growing.SleepySafe) : SleepySafe := by
  intro sp ro dg H tr proposer ΔF hstock hrun hnc hsl
  have hg := h sp ro dg (fun _ => H) tr proposer ΔF hstock
    (Growing.GoldilocksRun.const_iff.mpr hrun) hnc ((RunTrace.sleepyRunAt_const tr _).mpr hsl)
  rw [RunTrace.honestBlocksAt_const] at hg
  exact ⟨fun y hy z hz i j t t' => hg.1 y z i j t t' hy hz, hg.2⟩

/-- The growing-fault R.2 inclusion implies the static one. -/
theorem includeSleepy_of_growing (h : Regimes.Growing.IncludeSleepy) : IncludeSleepy := by
  intro sp ro dg H tr proposer ΔF hstock hrun hnc hsl τ P hP y t j ht hy hj
  have hg := h sp ro dg (fun _ => H) tr proposer ΔF hstock
    (Growing.GoldilocksRun.const_iff.mpr hrun) hnc ((RunTrace.sleepyRunAt_const tr _).mpr hsl) τ P
    (Growing.readyProposalAt_const.mpr hP) y t j ht hy hj
  rwa [RunTrace.honestBlocksAt_const] at hg

/-- The growing-fault R.2 growth implies the static one. -/
theorem growSleepy_of_growing (h : Regimes.Growing.GrowSleepy) : GrowSleepy := by
  intro sp ro dg H tr proposer ΔF k hstock hrun hnc hsl hk D t ht hr
  obtain ⟨τ, P, hτ, hP, h1, h2, h3⟩ := h sp ro dg (fun _ => H) tr proposer ΔF k hstock
    (Growing.GoldilocksRun.const_iff.mpr hrun) hnc ((RunTrace.sleepyRunAt_const tr _).mpr hsl) hk
    t ht (Growing.proposerRecurrence_const.mpr hr)
  rw [RunTrace.honestBlocksAt_const] at h1 h2 h3
  exact ⟨τ, P, hτ, Growing.readyProposalAt_const.mp hP, h1, h2, h3⟩

/-- The growing-fault R.8 `nested` implies the static one. -/
theorem outputsNested_of_growing (h : Regimes.Growing.OutputsNested) : OutputsNested :=
  fun sp ro dg H tr proposer hrun y hy i =>
    h sp ro dg (fun _ => H) tr proposer (Growing.GoldilocksRun.const_iff.mpr hrun) y i hy

/-- The growing-fault R.8 `finalMonotone` implies the static one. -/
theorem finalizedMonotone_of_growing (h : Regimes.Growing.FinalizedMonotone) : FinalizedMonotone :=
  fun sp ro dg H tr proposer hrun y hy i j hij =>
    h sp ro dg (fun _ => H) tr proposer (Growing.GoldilocksRun.const_iff.mpr hrun) y i j hij hy

/-- The growing-fault R.8 `outputValid` implies the static one. -/
theorem outputsValid_of_growing (h : Regimes.Growing.OutputsValid) : OutputsValid :=
  fun sp ro dg H tr proposer hrun y hy i =>
    h sp ro dg (fun _ => H) tr proposer (Growing.GoldilocksRun.const_iff.mpr hrun) y i hy

/-- The growing-fault R.7 `finalAccountable` implies the static one. -/
theorem finalAccountable_of_growing (h : Regimes.Growing.FinalAccountable) : FinalAccountable := by
  intro sp ro dg H tr proposer hrun hnc y hy z hz i j hc
  exact h sp ro dg (fun _ => H) tr proposer (Growing.GoldilocksRun.const_iff.mpr hrun) hnc y z i j
    hy hz (by rwa [RunTrace.honestBlocksAt_const])

/-- The growing-fault R.7 `nonFraming` implies the static one. -/
theorem nonFraming_of_growing (h : Regimes.Growing.NonFraming) : NonFraming :=
  fun sp ro dg H tr proposer hrun v hv k k' a b ha hb =>
    h sp ro dg (fun _ => H) tr proposer (Growing.GoldilocksRun.const_iff.mpr hrun) v k k' a b ha hb
      hv

/-- The growing-fault R.7 finalized safety implies the static one. -/
theorem finalizedSafe_of_growing (h : Regimes.Growing.FinalizedSafe) : FinalizedSafe := by
  intro sp ro dg H tr proposer hrun hnc hf y hy z hz i j
  have hg := h sp ro dg (fun _ => H) tr proposer (Growing.GoldilocksRun.const_iff.mpr hrun) hnc y z
    i j hy hz hf
  rwa [RunTrace.honestBlocksAt_const] at hg

namespace Compose

/-- The growing-fault A1.6 implies the static one. -/
theorem headExtendsRecord_of_growing (h : Compose.Growing.HeadExtendsRecord) :
    HeadExtendsRecord := by
  intro sp ro proposer dg H tr ΔF hstock hrun hnc hsl y hy i hs R hR
  obtain ⟨h1, h2⟩ := h sp ro proposer dg (fun _ => H) tr ΔF hstock
    (Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun) hnc
    ((RunTrace.sleepyRunAt_const tr _).mpr hsl) y i hy hs R hR
  refine ⟨h1, fun i' hi' hk R' hR' => ?_⟩
  have hg := h2 i' hi' hy hk R' hR'
  rwa [RunTrace.honestBlocksAt_const] at hg

/-- The growing-fault A1.7 implies the static one. -/
theorem inclusion_of_growing (h : Compose.Growing.Inclusion) : Inclusion := by
  intro sp ro proposer dg H tr ΔF hstock hrun hnc hsl p hp k P s hP hs hj y hy i hc hjy hr hu
  have hg := h sp ro proposer dg (fun _ => H) tr ΔF hstock
    (Goldilocks.Growing.GoldilocksRun.const_iff.mpr hrun) hnc
    ((RunTrace.sleepyRunAt_const tr _).mpr hsl) p k P s hp hP hs hj y i hy hc hjy hr hu
  rwa [RunTrace.honestBlocksAt_const] at hg

end Compose

end Consensus.Goldilocks

end
