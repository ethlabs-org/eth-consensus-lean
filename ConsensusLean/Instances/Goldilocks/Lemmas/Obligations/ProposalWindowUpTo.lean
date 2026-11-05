module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalSignedUpTo

public section

/-! # Goldilocks Obligations: an honest proposal in each window justifies, through a horizon

consensus-lean#137 (finite-horizon port). `window_justifies` and `window_justifies_healed` from
`HSSharedUpTo … b` and `HealedRecordsUpTo … b`. The guard `hwb`: every slot `s' < s₁ + g` of the
window has `t_{s'} ≤ b`, so the window proposal cut is by `b` (`rows_delivered_upTo`). The
exposure premise and the fin clause of the attestation supply are asked only at cuts by `b`. -/

namespace Consensus.Goldilocks.Obligations

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The cut of an honest proposal is at its slot time. -/
theorem proposesAt_time {p : Fin sp.n} {k : Nat} {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : tr.ProposesAt p k X) : tr.time k = sp.ts X.slot := by
  rw [hX.2.2, sp.slotTime_eq]; rfl

end Consensus.Goldilocks.Obligations

end
