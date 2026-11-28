module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Prefix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.PrefixSteps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo

public section

/-! # The recipient's late-slot tick precedes block delivery

This is a local run fact, independent of reset or origin comparison. A growing
consumer reads it only on the recipient's own honest prefix.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp}

/-- The late-delivery ordering read on the recipient's honest observation prefix. -/
theorem vote_before_late_delivery_at
    {ini} {H : Time → Set (Fin sp.n)}
    (rc : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) {i : Nat} {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hA : tr.AcceptAt y i W) (hik : i < k) (ht : tr.time i = sp.ts e.msg.slot + sp.Δ) :
    False := by
  apply Healing.vote_before_late_delivery (rc.upTo (rc.time_nonneg k))
    (hnc.upTo _) hy (by rw [RunTrace.upTo_projAC]; exact AC.upTo_castAt.mpr ⟨le_rfl, hc⟩)
    ((RunTrace.upTo_acceptAt tr).mpr ⟨rc.time_mono hik.le, hA⟩) hik
  exact ht

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
