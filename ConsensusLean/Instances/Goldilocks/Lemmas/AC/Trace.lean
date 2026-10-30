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

/-- **Retention at one node.** A block that an honest node accepted is in the frame of each of its
later calls whose finalized tip it extends (inside `U`): the node's frames evolve by frame steps
inside `U` (G0.3 (frame)), so a block leaves only when `Φ.F` moves past it, and never returns. -/
theorem mem_tree_of_acceptAt {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) {k i : Nat}
    {B : Blk sp.n FGP} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hk : tr.AcceptAt y k B)
    (hki : k ≤ i) (hc : tr.CallAt y i ℓ) (hF : Anc U ℓ.frame.F B) : B ∈ ℓ.frame.tree := by
  sorry

/-- **Stamps of accepted blocks.** At an honest node's call, a block of the call's frame that the
node accepted before `T` (or genesis) has a stamp below `T` in the state before the call, when
every restart of the node up to the call was before `T`: the stamp of a block is written only
when the node accepts it (once: it enters the frame once) and by a restart's replay (A0.7). -/
theorem blockStamp_lt_of_acceptedBefore {FGP : Type} {ro : ReplayOrder sp FGP}
    {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) {B : Blk sp.n FGP}
    (hB : B ∈ ℓ.frame.tree) {T : Time} (hacc : AcceptedBefore tr y B T)
    (hrs : ∀ k ≤ i, tr.RestartAt y k → tr.time k < T) :
    (tr.state y i).blockStamp B.root < ETime.of T := by
  sorry

/-- **The state before a cut is initial or reachable.** The state of an honest node before cut `i`
is the initial state (no call yet), or reachable inside `U` with the frame and the time of its
last call before `i` (which is at or before the time of cut `i`). -/
theorem state_reachable {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    tr.state y i = SAState.initial sp.genesisRoot ∨
      ∃ Φ t, (goldilocksSA sp FGP ro).ReachableAt y U (tr.state y i) Φ t ∧ t ≤ tr.time i := by
  sorry

/-- The slot-`σ` pool of an honest node's state before any cut holds only slot-`σ` votes. -/
theorem state_pool_slot {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) (i σ : Nat) :
    ∀ v ∈ (tr.state y i).pool σ, v.slot = σ := by
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
