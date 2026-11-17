module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves

public section

/-! # The reset service as the generic service

A Goldilocks run's `ResetService` is `Generic.Service`, field for field (`ResetService.toService`).
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The reset service of a Goldilocks run is the generic service (`Generic.Service`), field for
field. -/
theorem ResetService.toService {g ΔF b : Time} (h : ResetService tr H g ΔF b) :
    Generic.Service tr H g ΔF b :=
  ⟨h.deltaF, h.message, h.block, h.relay, h.signedRow⟩

end Consensus.Goldilocks.Healing.Growing

end
