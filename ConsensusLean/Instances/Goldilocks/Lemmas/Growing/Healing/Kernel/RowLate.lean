module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Prefix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.PrefixSteps

public section

/-! # The recipient's late-slot tick precedes block delivery

This is a local run fact, independent of reset or origin comparison. A growing
consumer reads it only on the recipient's own honest prefix.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A block delivered at `t_m + Δ` cannot precede the recipient's slot-`m` vote. -/
theorem vote_before_late_delivery
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) {i : Nat} {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hA : tr.AcceptAt y i W) (hik : i < k) (ht : tr.time i = sp.ts e.msg.slot + sp.Δ) :
    False :=
  Healing.vote_before_late_delivery hrun hnc hy hc hA hik ht

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
