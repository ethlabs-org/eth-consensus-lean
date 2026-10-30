module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction

public section

/-! # Goldilocks under `Sleepy`: the honest batch at an update (open)

workbench#12 §4: when every honest slot-`s` vote names a block `P` of a joined updater's frame,
the honest slot-`s` votes reach the updater of slot `s`, held and resolved before `t_s + 2Δ`
(the update analogue of `honest_batch_carry`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **The honest slot-`s` batch reaches the joined updater of slot `s`**, held and resolved
before `t_s + 2Δ`, when every honest slot-`s` vote names the block `P` of the updater's frame
(workbench#12 §4: each is cast by `t_s + Δ` and forwarded, and `P` is relayed, to the updater,
awake and unrestarted since `t_s`; open). -/
theorem honest_batch_at_update {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {y : Fin sp.n} (hy : y ∈ H) {k₀ s : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC y k₀ s ℓ)
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hPt : P ∈ ℓ.frame.tree)
    (hall : ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s → e.msg.head = P.root) :
    ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s →
      e.msg ∈ (tr.projAC.state y k₀).pool s ∧
        SA.resolutionTime (tr.projAC.state y k₀) ℓ.frame e.msg <
          SA.ETime.of (sp.ts s + 2 * sp.Δ) := by
  sorry

end Consensus.Goldilocks.Compose

end
