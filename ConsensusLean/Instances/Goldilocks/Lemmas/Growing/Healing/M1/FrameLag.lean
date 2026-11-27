module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves

public section

/-! # The reset service as the generic service

A Goldilocks run's `ResetService` is `Generic.Service`, field for field (`ResetService.toService`).
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}

/-- The reset service of a Goldilocks run is the generic service (`Generic.Service`), field for
field. -/
theorem ResetService.toService {g ΔF b hold : Time} (h : ResetService tr H g ΔF b hold) :
    Generic.Service tr H g ΔF b hold :=
  ⟨h.deltaF, h.message, h.block, h.relay, h.signedRow, h.hold_le⟩

end Consensus.Goldilocks.Healing.Growing

end
