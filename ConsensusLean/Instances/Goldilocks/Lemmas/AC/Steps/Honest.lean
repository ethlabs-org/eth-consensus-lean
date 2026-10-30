module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk

public section

/-! # Goldilocks SA: honest votes in a voter's merged view

Under the honest-object facts (unforgeable signatures) and one vote per slot (A0.8): every
vote of an honest validator in an honest voter's merged view was emitted by that validator's
node no later than the vote, so an honest validator is never an equivocator there; and an
honest vote's head is a block of the voter's frame, of a slot no later than the vote's. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}

private theorem mem_admitVote_pool {A : SAState sp.n} {t : Time} {v x : Vote sp.n} {σ : Nat}
    (h : x ∈ A.pool σ) : x ∈ (admitVote sp A t v).pool σ := by
  unfold admitVote
  split_ifs
  · exact h
  · exact h
  · simp only [Function.update_apply]
    split_ifs with he
    · subst he; exact List.mem_append_left _ h
    · exact h

private theorem optimistic_pool (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).pool = A.pool := by
  unfold optimisticConfirmation updateLatestConfirmed
  split
  · rfl
  · split_ifs <;> rfl

/-- The walk of a subtree of a well-formed frame ends in the frame's tree. -/
private theorem getHead_mem {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {T : Set (Blk sp.n FGP)}
    (hT : T ⊆ Φ.tree) (A : SAState sp.n) (t : Time) (V : View sp.n) (σ : Int) :
    getHead sp A Φ t T V σ ∈ Φ.tree := by
  have ha : getAnchor sp A Φ t ∈ Φ.tree := by
    unfold getAnchor
    cases hd : deepest Φ (liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}) with
    | none => exact hΦ.fcRoot_mem
    | some D =>
      rcases (deepest_mem hd).1 with h | h
      · exact h.1
      · exact (Set.mem_singleton_iff.1 h) ▸ hΦ.fcRoot_mem
  obtain h | h := eq_or_ne (getAnchor sp A Φ t) (getHead sp A Φ t T V σ)
  · exact h ▸ ha
  · exact (Anc.mem (C := getHead sp A Φ t T V σ) (anc_ghost hT _ ha) h).2

/-- A vote of an honest validator in an honest voter's merged view was emitted by its node at
a cut no later than the voter's call. -/
theorem honest_merged_vote (hrun : ACRun tr H U) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e) {σ : Nat}
    {v : Vote sp.n} (hv : v ∈ (mergedVoteView sp e.readPoint ℓ.frame σ).votes)
    (hvH : v.val ∈ H) : ∃ j ≤ i, ∃ e', VoteAt tr v.val j e' ∧ e'.msg = v := by
  rcases hv with hv | ⟨B, hB, -, hv⟩
  · have hv : v ∈ e.readPoint.poolAt ((σ : Int) - 1) := (List.mem_filter.1 hv).1
    simp only [SAState.poolAt] at hv
    split_ifs at hv
    · simp at hv
    have hpost : v ∈ (tr.state y (i + 1)).pool ((σ : Int) - 1).toNat := by
      rw [show tr.state y (i + 1) = tr.post i by simp [Trace.state, hc.1.1, hc.1.2],
        post_of_castAt hrun.localRun hy hc, optimistic_pool]
      exact mem_admitVote_pool hv
    obtain ⟨j, hj, h⟩ := hrun.honest.pool_vote y hy _ _ v hpost hvH
    exact ⟨j, Nat.lt_succ_iff.1 hj, h⟩
  · obtain ⟨j, hj, h⟩ := hrun.honest.carried_vote y hy i ℓ hc.1 B hB v hv hvH
    exact ⟨j, hj.le, h⟩

/-- An honest validator is not an equivocator in an honest voter's merged view. -/
theorem honest_not_equivocator (hrun : ACRun tr H U) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e) {σ : Nat}
    {w : Fin sp.n} (hw : w ∈ H) :
    w ∉ equivocators (mergedVoteView sp e.readPoint ℓ.frame σ).votes := by
  have hr := hrun.localRun
  rintro ⟨x, hx, x', hx', hne, rfl, hxx⟩
  obtain _ | s := σ
  · rcases hx with hx | ⟨B, hB, hBs, hv⟩
    · simpa [SAState.poolAt] using (List.mem_filter.1 hx).1
    · have := (frame_validPayload sp hr hy hc.1 B hB).1 x hv
      omega
  obtain ⟨j, -, e₁, hv₁, rfl⟩ := honest_merged_vote hrun hy hc hx hw
  obtain ⟨j', -, e₂, hv₂, rfl⟩ := honest_merged_vote hrun hy hc hx' (hxx ▸ hw)
  rw [hxx] at hv₂
  exact hne (congrArg Emission.msg (one_vote_per_slot sp _ _ _ _ _ hr _ (hxx ▸ hw) _ _ _ _ hv₁
    hv₂ ((merged_vote_slot hr hy hc _ hx).trans (merged_vote_slot hr hy hc _ hx').symm)).2)

/-- An honest vote's head is a block of its voter's frame, of a slot no later than the
vote's. -/
theorem honest_head (hrun : ACRun tr H U) {x : Fin sp.n} (hx : x ∈ H) {j : Nat}
    {e : Em sp FGP} (hv : VoteAt tr x j e) :
    ∃ Hd ∈ U, Hd.root = e.msg.head ∧ Hd.slot ≤ e.msg.slot := by
  have hr := hrun.localRun
  obtain ⟨ℓ, hc, he⟩ := hv
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
    rcases hr.frameLaw x hx j ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨k, ℓ', -, -, -, h⟩ <;> exact h.1
  obtain ⟨-, hs, -, hh⟩ := castAt_spec hr hx ⟨hc, he⟩
  refine ⟨_, hΦU ?_, hh.symm, (frame_slot_le sp hr hx hc _ ?_).trans hs.ge⟩ <;>
    exact getHead_mem hΦ (fun _ hB => hB.1.1) _ _ _ _

end Consensus.Goldilocks.SA

end
