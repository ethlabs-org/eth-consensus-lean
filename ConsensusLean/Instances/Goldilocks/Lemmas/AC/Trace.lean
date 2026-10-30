module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Invariant

public section

/-! # Goldilocks AC traces: reachability and one node's life (F.1 (c), A0.7, A0.8)

The AC trace contract gives reachable states; and, over an SA trace, a joined node has been
awake with no restart since the previous slot, erased no recent vote at its restarts, and casts
one vote per slot. -/

namespace Consensus.Goldilocks

namespace ACTrace

variable {P : Params} {FGP : Type} {A : ACInterface P FGP} (tr : ACTrace A)

/-- Before any call of `y`, its state is its initial state. -/
theorem state_of_noCall {y : Fin P.n} {i : Nat} (h : tr.NoCallBetween y 0 i) :
    tr.state y i = tr.init y := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi : tr.state y (i + 1) = tr.state y i := by
      simp only [Trace.state]
      split_ifs with hc
      · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hc.2
        exact absurd ⟨hc.1, hℓ⟩ (h i (Nat.zero_le _) (Nat.lt_succ_self _) ℓ)
      · rfl
    rw [hi]
    exact ih fun k h0 hk ℓ => h k h0 (Nat.lt_succ_of_lt hk) ℓ

/-- After a call of `y` at `j` and no call of `y` in `(j, i)`, its state is that call's
post-state. -/
theorem state_of_lastCall {y : Fin P.n} {j i : Nat} {ℓ : ACLabel A} (hc : tr.CallAt y j ℓ)
    (hji : j < i) (h : tr.NoCallBetween y (j + 1) i) : tr.state y i = tr.post j := by
  induction i with
  | zero => omega
  | succ i ih =>
    simp only [Trace.state]
    by_cases hij : i = j
    · subst hij
      have : tr.node i = y ∧ tr.label i ≠ none := ⟨hc.1, by rw [hc.2]; exact Option.some_ne_none _⟩
      split_ifs
      rfl
    · split_ifs with hn
      · obtain ⟨ℓ', hℓ'⟩ := Option.ne_none_iff_exists'.mp hn.2
        exact absurd ⟨hn.1, hℓ'⟩ (h i (by omega) (Nat.lt_succ_self _) ℓ')
      · exact ih (by omega) fun k hk hk' ℓ' => h k hk (Nat.lt_succ_of_lt hk') ℓ'

/-- Before cut `i`, `y` made no call, or a last call at some `j < i`. -/
theorem noCall_or_lastCall (y : Fin P.n) (i : Nat) :
    tr.NoCallBetween y 0 i ∨
      ∃ j < i, ∃ ℓ, tr.CallAt y j ℓ ∧ tr.NoCallBetween y (j + 1) i := by
  induction i with
  | zero => exact Or.inl fun k _ hk => absurd hk (Nat.not_lt_zero k)
  | succ i ih =>
    by_cases hc : ∃ ℓ, tr.CallAt y i ℓ
    · obtain ⟨ℓ, hℓ⟩ := hc
      exact Or.inr ⟨i, Nat.lt_succ_self _, ℓ, hℓ, fun k hk hk' => absurd hk' (by omega)⟩
    · simp only [not_exists] at hc
      have ext : ∀ a, (∀ k, a ≤ k → k < i → ∀ ℓ, ¬ tr.CallAt y k ℓ) →
          ∀ k, a ≤ k → k < i + 1 → ∀ ℓ, ¬ tr.CallAt y k ℓ := by
        intro a ha k hak hk ℓ
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact ha k hak hk ℓ
        · exact hc ℓ
      rcases ih with h | ⟨j, hj, ℓ, hℓ, h⟩
      · exact Or.inl (ext 0 h)
      · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, ℓ, hℓ, ext (j + 1) h⟩

end ACTrace

/-- The AC trace contract gives reachable states. -/
theorem localRun_reachable : LocalRunReachable := by
  intro P FGP A H U tr h y hy i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro ℓ hc
    have hexec := h.exec i ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1] at hexec
    have hpost : tr.post i = (A.step y (tr.state y i) ℓ.frame (tr.time i) ℓ.call).1 := by
      rw [hexec]
    rcases h.frameLaw y hy i ℓ hc with ⟨hnone, Φ₀, hinit, hin, hok⟩ | ⟨j, ℓ', hj, hc', hnb, hok⟩
    · rw [hpost, tr.state_of_noCall hnone, h.init y hy]
      exact .step ℓ.call (.init Φ₀ hinit hin) (h.time_nonneg i) hok
    · rw [hpost, tr.state_of_lastCall hc' hj hnb]
      exact .step ℓ.call (ih j hj ℓ' hc') (h.time_mono (Nat.le_of_lt hj)) hok

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
  rcases tr.noCall_or_lastCall y i with hnone | ⟨j, hj, ℓ, hc, hnb⟩
  · exact Or.inl ((tr.state_of_noCall hnone).trans (h.init y hy))
  · rw [tr.state_of_lastCall hc hj hnb]
    exact Or.inr ⟨ℓ.frame, tr.time j, localRun_reachable _ _ _ _ _ tr h y hy j ℓ hc,
      h.time_mono (Nat.le_of_lt hj)⟩

/-- The slot-`σ` pool of an honest node's state before any cut holds only slot-`σ` votes. -/
theorem state_pool_slot {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) (i σ : Nat) :
    ∀ v ∈ (tr.state y i).pool σ, v.slot = σ := by
  sorry

/-- The blocks of an honest call's frame are not of a future slot: the initial frame holds
genesis, of slot `0`, and a frame step adds only the block of an `on_block` call, which is not of
a future slot (the input contract); calls are at nondecreasing times from `0`. -/
theorem frame_slot_le {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) :
    ∀ B ∈ ℓ.frame.tree, B.slot ≤ sp.slot (tr.time i) := by
  induction i using Nat.strong_induction_on generalizing ℓ with
  | _ i ih =>
    have step : ∀ (Φ : Frm sp.n FGP) (c : (goldilocksSA sp FGP ro).Call),
        (goldilocksSA sp FGP ro).CallOK U Φ (tr.time i) c ℓ.frame →
        (∀ B ∈ Φ.tree, B.slot ≤ sp.slot (tr.time i)) →
        ∀ B ∈ ℓ.frame.tree, B.slot ≤ sp.slot (tr.time i) := by
      intro Φ c hok hv X hX
      obtain ⟨-, hc'⟩ := hok
      cases c with
      | block B =>
        obtain ⟨hs, -, hB⟩ := hc'
        rw [hs.tree_eq] at hX
        rcases hX.1 with rfl | hX
        · exact hB
        · exact hv X hX
      | message m => exact hv X (hc'.1 ▸ hX)
      | tick => exact hv X (hc' ▸ hX)
      | proposal => exact hv X (hc' ▸ hX)
      | toFG => exact hv X (hc' ▸ hX)
      | restart => exact hv X (hc' ▸ hX)
    rcases h.frameLaw y hy i ℓ hc with
      ⟨-, Φ₀, ⟨htree, -, hslot, -, -⟩, -, hok⟩ | ⟨j, ℓ', hj, hc', -, hok⟩
    · refine step Φ₀ _ hok fun B hB => ?_
      rw [htree, Set.mem_singleton_iff] at hB
      subst hB
      rw [hslot]; exact Nat.zero_le _
    · refine step _ _ hok fun B hB => ?_
      exact le_trans (ih j hj hc' B hB)
        (slot_mono sp (h.time_nonneg j) (h.time_mono (Nat.le_of_lt hj)))

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
