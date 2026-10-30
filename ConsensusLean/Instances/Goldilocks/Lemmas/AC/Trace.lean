module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Invariant

public section

/-! # Goldilocks AC traces: reachability and one node's life (F.1 (c), A0.7, A0.8)

The AC trace contract gives reachable states; and, over an SA trace, a joined node has been
awake with no restart since the previous slot, erased no recent vote at its restarts, and casts
one vote per slot. -/

namespace Consensus.Goldilocks

/-- The AC trace contract gives reachable states. -/
theorem localRun_reachable : LocalRunReachable := by
  sorry

end Consensus.Goldilocks

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- Every block of an honest node's frame passes `ac_valid_payload`: the initial frame holds
genesis, whose payload is empty, and a frame step adds only the block of an `on_block` call,
which passed the check (the input contract). -/
theorem frame_validPayload {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) :
    ∀ B ∈ ℓ.frame.tree, validPayload B := by
  sorry

/-- **F.1 (c), a joined node.** -/
theorem joined_awake : JoinedAwake sp := by
  sorry

/-- **A0.7, joining.** -/
theorem joined_keeps_votes : JoinedKeepsVotes sp := by
  sorry

/-- **A0.8.** -/
theorem one_vote_per_slot : OneVotePerSlot sp := by
  sorry

end Consensus.Goldilocks.SA

end
