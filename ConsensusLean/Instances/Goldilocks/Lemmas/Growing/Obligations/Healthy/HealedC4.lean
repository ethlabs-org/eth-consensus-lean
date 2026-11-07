module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalPending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation

public section

/-! # C4 of the healed window under growing faults: no reorg of honest proposals

The growing form of `Obligations/HealedC4` and of the window-facing C4 wrappers of
`Obligations/HealedUpTo`, with each proposer honest through its own slot's `t_s + hold`:

* `proposesAt_of_honestProposalRun_at`: an honest proposal run is made operationally;
* `honest_proposal_below_next_upTo_at`, `honest_proposal_below_later_upTo_at`: under the finite
  reset premises and Catch(2Δ), an honest proposal of a post-drain slot `s` is an honest ancestor
  of the honest proposals of slots `s + 1` (with the service reserve `t_s + 6Δ ≤ b`) and
  `s' ≥ s + 2` (with `t_{s'} ≤ b`). -/

namespace Consensus.Goldilocks.Obligations.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- **An honest proposal run is made operationally**: its proposer proposes it at some cut. -/
theorem proposesAt_of_honestProposalRun_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {s : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.Growing.HonestProposalRun tr H proposer s P) :
    ∃ k, tr.ProposesAt (proposer s) k P := by
  sorry

/-- **No reorg two slots on, through the horizon**, under growing faults. -/
theorem honest_proposal_below_later_upTo_at
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ)) {s s' : Nat}
    {P P' : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.Growing.HonestProposalRun tr H proposer s P)
    (hR : Healing.drainTime sp a ≤ sp.ts s)
    (hP' : Healing.Growing.HonestProposalRun tr H proposer s' P') (hss : s + 2 ≤ s')
    (hb : sp.ts s' ≤ b) : Anc (tr.HonestBlocksAt H) P P' := by
  sorry

/-- **No reorg one slot on, through the horizon**, under growing faults, with the service reserve
`t_s + 6Δ ≤ b`. -/
theorem honest_proposal_below_next_upTo_at
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ)) {s : Nat}
    {P P' : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.Growing.HonestProposalRun tr H proposer s P)
    (hR : Healing.drainTime sp a ≤ sp.ts s)
    (hP' : Healing.Growing.HonestProposalRun tr H proposer (s + 1) P')
    (hTb : sp.ts s + 6 * sp.Δ ≤ b) : Anc (tr.HonestBlocksAt H) P P' := by
  sorry

end Consensus.Goldilocks.Obligations.Growing

end
