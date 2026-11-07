module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.TransferFirst
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.TransferLater

public section

/-! # Goldilocks under `Sleepy` with growing faults: extending the vote frontier

`votes_below_succ_at`: `P_{s+1}` and `V_s` up to `b` give `V_{s+1}` up to `b`, by strong induction
on the cut of a slot-`(s+1)` vote of a node honest at it (the first bad vote), with the first and
later transfer steps. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **Extending the vote frontier under growing faults**. -/
theorem votes_below_succ_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBounds tr H b) {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b)
    (hV : VotesBelowUpTo tr H s b) : VotesBelowUpTo tr H (s + 1) b := by
  sorry

end Consensus.Goldilocks.Compose.Growing

end
