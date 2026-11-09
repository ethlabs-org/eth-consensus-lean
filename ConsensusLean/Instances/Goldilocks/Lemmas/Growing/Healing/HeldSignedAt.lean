module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows

public section

/-! # Signatures of held attestations at an honest observation

An attestation on a block held by a reader observed while honest at `t`, with a signer honest
at `t`, was signed by that signer before the reader's cut (`held_att_signed_at`): the block is
genesis (no attestations) or was accepted by the reader on its prefix up to `t`, and an honest
signer's attestation on an accepted block is unforgeable. Readers combine two such signatures
with client safety, at one observation or at a time after two. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- An attestation on a block held at an observation honest at `t`, with a signer honest at `t`,
was signed before the cut. -/
theorem held_att_signed_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) {a : FG.Att sp.n}
    (ha : ∃ Y ∈ (tr.state y i).fg.tree, a ∈ Y.fgPayload) (hav : a.val ∈ H t) :
    ∃ k < i, tr.SignAt a.val k a := by
  obtain ⟨X, hX, haX⟩ := ha
  have hXt : X ∈ ((tr.upTo t).state y i).fg.tree := by rw [Trace.upTo_state tr y hle]; exact hX
  rcases Healing.tree_accepted (hrun.upTo ht).toLocalRun hy hXt with rfl | ⟨k, hk, hacc⟩
  · cases haX
  · have hacc' := ((Trace.upTo_callAt tr).mp hacc).2
    obtain ⟨k', hk', hs'⟩ := hrun.toLocalRun.att_unforgeable y k a
      (hrun.antitone (hle k hk) hy) (Or.inr ⟨X, ⟨true, hacc'⟩, haX⟩)
      (hrun.antitone (hle k hk) hav)
    exact ⟨k', hk'.trans hk, hs'⟩

end Consensus.Goldilocks.Healing.Growing

end
