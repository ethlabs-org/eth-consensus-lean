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
  have step : ∀ (Φ Φ' : Frm sp.n FGP) (t : Time) (c : (goldilocksSA sp FGP ro).Call),
      (goldilocksSA sp FGP ro).CallOK U Φ t c Φ' → (∀ B ∈ Φ.tree, validPayload B) →
      ∀ B ∈ Φ'.tree, validPayload B := by
    intro Φ Φ' t c hok hv X hX
    obtain ⟨-, hc⟩ := hok
    cases c with
    | block B =>
      obtain ⟨hs, hB, -⟩ := hc
      rw [hs.tree_eq] at hX
      rcases hX.1 with rfl | hX
      · exact hB
      · exact hv X hX
    | message m => exact hv X (hc.1 ▸ hX)
    | tick => exact hv X (hc ▸ hX)
    | proposal => exact hv X (hc ▸ hX)
    | toFG => exact hv X (hc ▸ hX)
    | restart => exact hv X (hc ▸ hX)
  induction i using Nat.strong_induction_on generalizing ℓ with
  | _ i ih =>
    rcases h.frameLaw y hy i ℓ hc with
      ⟨-, Φ₀, ⟨htree, -, -, -, hpay⟩, -, hok⟩ | ⟨j, ℓ', hj, hc', -, hok⟩
    · refine step Φ₀ _ _ _ hok fun B hB => ?_
      rw [htree, Set.mem_singleton_iff] at hB
      subst hB
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩ <;>
        simp [blockVotes, blockSupport, hpay] at hv
    · exact step _ _ _ _ hok (ih j hj hc')

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
