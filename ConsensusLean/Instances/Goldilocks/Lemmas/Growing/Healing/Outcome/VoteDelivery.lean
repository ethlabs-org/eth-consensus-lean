module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.PrefixSteps

public section

/-! # A late delivery follows the receiver's vote

This is receiver-local event ordering; no service invariant or other node's
continued honesty is needed in the retained prefix.
-/

namespace Consensus.Goldilocks.Healing.Growing.Outcome

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {tr : GoldilocksTrace sp ro}

/-- An honest voter has not yet accepted a delivery at the late-vote tick. -/
theorem vote_before_late_delivery_at {H : Time → Set (Fin sp.n)}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {k i : Nat}
    (hy : y ∈ H (tr.time k)) {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y k ell e)
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hA : tr.AcceptAt y i W)
    (hik : i < k) (ht : tr.time i = sp.ts e.msg.slot + sp.Δ) : False := by
  have hc' : (tr.upTo (tr.time k)).projAC.CallAt y k ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc.1⟩
  exact Healing.vote_before_late_delivery (hrun.upTo (hrun.time_nonneg k)) (hnc.upTo _) hy
    ⟨hc', hc.2⟩ ((RunTrace.upTo_acceptAt tr).mpr ⟨hrun.time_mono hik.le, hA⟩) hik ht

end Consensus.Goldilocks.Healing.Growing.Outcome

end
