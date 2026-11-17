module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Read

public section

/-! # Goldilocks Regimes: R.1's reads under `Sleepy`

Under `Sleepy` (and `NoColl`), every confirmed read of an honest node, at the state before any cut
and at any time, is an honest block on the origin chain (`confirmed_read_on_chain` with the
Sleepy invariant), and blocks on the origin chain are compatible. So any two honest confirmed
reads are compatible (`sleepy_reads_compatible`), R.1's agreement half; R.2's growth reads it.
The R.1 milestone statement is retired.

There is no node-level prefix row: the prefix claim is the generic
`CorrectProtocol.sleepySafe_prefix`. -/

namespace Consensus.Goldilocks.Regimes

open SA (SAParams ReplayOrder Payload)
open Compose

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **Agreement of the honest confirmed reads under `Sleepy`**: any two confirmed reads of honest
nodes, at any cuts and at any times, are compatible (inside the honest blocks). -/
theorem sleepy_reads_compatible (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) (hstock : sp.committeeSize = sp.n) :
    ∀ y ∈ H, ∀ z ∈ H, ∀ i j t t',
      Compatible (tr.HonestBlocks H) (readAfter tr y i t) (readAfter tr z j t') := by
  intro y hy z hz i j t t'
  have hinv := sleepy_invariant hrun hnc hsl hstock
  obtain ⟨hB, hc⟩ := confirmed_read_on_chain hinv hrun hnc hy i t
  obtain ⟨hB', hc'⟩ := confirmed_read_on_chain hinv hrun hnc hz j t'
  exact OnOriginChain.compatible hrun hnc hinv.origins_compatible hB hB' hc hc'

end Consensus.Goldilocks.Regimes

end
