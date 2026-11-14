module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves

public section

/-! # The held-attestation safety premise at independent honest observations

Attestations on blocks held by two readers, each observed while honest at its own time, with a
signer honest at a time after both observations, are not slashable (`held_atts_safe_at`). Each
signature is recovered at its own reader's horizon (`held_att_signed_at`) and both are charged
on the prefix up to the later time, rather than through a terminal honest cohort. This is the
safety premise of the static store-level crossing arguments (`Healing/HeldSafety`,
`Healing/M1/StoreCache`, `Healing/M1/FrameLagCore`) for the growing readers. The proof is the
generic `Generic.held_atts_safe_at_from` (`Lemmas/Generic/HealingLeaves`) at the Goldilocks run.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- **Held attestations at independently honest observations are not slashable.** Attestations
on blocks held by `y` (observed while honest at `u`) and by `x` (observed while honest at `t`),
with a signer honest at a time `d` after both observations, were signed by that signer's client
run on the prefix up to `d`, which client safety (G0.5) keeps free of slashable pairs. -/
theorem held_atts_safe_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y x : Fin sp.n} {m i : Nat} {u t d : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t) (hud : u ≤ d) (htd : t ≤ d)
    (a b : FG.Att sp.n) (ha : ∃ Y ∈ (tr.state y m).fg.tree, a ∈ Y.fgPayload)
    (hb : ∃ Y ∈ (tr.state x i).fg.tree, b ∈ Y.fgPayload) (hav : a.val ∈ H d) :
    ¬ FG.slashable a b :=
  Generic.held_atts_safe_at_from hrun.toLocalRun hu hytime hy ht hxtime hx hud htd a b ha hb hav

end Consensus.Goldilocks.Healing.Growing

end
