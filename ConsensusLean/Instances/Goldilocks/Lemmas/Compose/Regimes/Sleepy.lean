module
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction

public section

/-! # Goldilocks milestone Regimes: R.1, the agreement half

Under `Sleepy` (and `NoColl`), every confirmed read of an honest node, at the state before any cut
and at any time, is an honest block on the origin chain (`confirmed_read_on_chain` with the
Sleepy invariant), and blocks on the origin chain are compatible. So any two honest confirmed
reads are compatible (`sleepy_reads_compatible`), which is the agreement half of `SleepySafe`'s
`ReadySafeOn` (`sleepy_ready_agree`), for every window, without readiness or `Boundary`.

The monotone half of `ReadySafeOn` and `SleepySafePrefix` are open (see the report on
consensus-lean#17): the first needs the head support of A1.6 at a ready read point, the second the
Sleepy invariant under the prefix premises. -/

namespace Consensus.Goldilocks.Regimes

open SA (SAParams ReplayOrder Payload)
open Compose

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time}

/-- **Agreement of the honest confirmed reads under `Sleepy`**: any two confirmed reads of honest
nodes, at any cuts and at any times, are compatible (inside the honest blocks). -/
theorem sleepy_reads_compatible (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) :
    ∀ y ∈ H, ∀ z ∈ H, ∀ i j t t',
      Compatible (tr.HonestBlocks H) (readAfter tr y i t) (readAfter tr z j t') := by
  intro y hy z hz i j t t'
  have hinv := sleepy_invariant hrun hnc hsl
  obtain ⟨hB, hc⟩ := confirmed_read_on_chain hinv hrun hnc hy i t
  obtain ⟨hB', hc'⟩ := confirmed_read_on_chain hinv hrun hnc hz j t'
  exact OnOriginChain.compatible hrun hnc hinv.origins_compatible hB hB' hc hc'

/-- **R.1, the agreement half of `ReadySafeOn`** under `Sleepy`, for every window and catch-up. -/
theorem sleepy_ready_agree (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) (c t₀ t₁ : Time) :
    ∀ y z i j t t', ReadPoint tr i t → ReadPoint tr j t' → Boundary tr y i → Boundary tr z j →
      t₀ ≤ t → t ≤ t₁ → t₀ ≤ t' → t' ≤ t₁ → ReadyAt tr H c y t → ReadyAt tr H c z t' →
      Compatible (tr.HonestBlocks H) (readAfter tr y i t) (readAfter tr z j t') :=
  fun y z i j t t' _ _ _ _ _ _ _ _ hy hz =>
    sleepy_reads_compatible hrun hnc hsl y hy.1 z hz.1 i j t t'

end Consensus.Goldilocks.Regimes

end
