module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.RowSource
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.PrefixSteps

public section

/-! # Signing uniqueness before compromise -/

namespace Consensus.Goldilocks.Healing.Growing.Outcome

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {tr : GoldilocksTrace sp ro}

/-- Two signings before the same honest observation must be the same event. -/
theorem sign_unique_at {H : Time → Set (Fin sp.n)}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {v : Fin sp.n} {d d' : Nat} {t : Time} {att : FG.Att sp.n}
    (ht : 0 ≤ t) (hv : v ∈ H t) (hd : tr.time d ≤ t) (hd' : tr.time d' ≤ t)
    (hs : tr.SignAt v d att) (hs' : tr.SignAt v d' att) : d = d' :=
  Healing.sign_unique (hrun.upTo ht) hv ((RunTrace.upTo_signAt tr).mpr ⟨hd, hs⟩)
    ((RunTrace.upTo_signAt tr).mpr ⟨hd', hs'⟩)

end Consensus.Goldilocks.Healing.Growing.Outcome

end
