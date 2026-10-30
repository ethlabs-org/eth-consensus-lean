module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission

public section

/-! # Goldilocks SA: what a result carries to a voter (A1.8 (c), (d))

For an update result `C` of an honest `X` in slot `s` with counted votes `CV`, and an honest
`y`'s slot-`(s+1)` vote with `Carry_y(s, ·, C)` and the writer-pool condition (d):
* the merged view's support is among its votes (support entries are votes of the block,
  `validPayload`);
* the validators of `CV` are supporters of `C` in `y`'s merged view: `y` holds each counted vote
  (two other votes of a validator would be in `X`'s pool by (d) and make it an equivocator
  there), received and resolved before the vote freeze (its head accepted before
  `t_s + 3Δ`, in `y`'s tree since it extends `C`), and none of them equivocates at `y` (by (d),
  again);
* the merged view's voters are participants at `X` (by (d));
* the counted validators are a strict majority of `X`'s participants (`get_confirmation`). -/

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

/-- Every vote of an honest voter's merged view of slot `s + 1` has slot `s`. -/
theorem merged_vote_slot (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) {s : Nat} :
    ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s := by
  rintro v (hv | ⟨B, hB, hBs, hv⟩)
  · have hv : v ∈ e.readPoint.poolAt ((s + 1 : Nat) - 1 : Int) := (List.mem_filter.1 hv).1
    simp only [SAState.poolAt] at hv
    split_ifs at hv with hneg
    · simp at hv
    have hpost : v ∈ (tr.post i).pool s := by
      rw [post_of_castAt hr hy hc, optimistic_pool]
      exact mem_admitVote_pool (by simpa using hv)
    refine state_pool_slot sp hr hy (i + 1) s v ?_
    rw [Trace.state]
    split_ifs with h
    · exact hpost
    · exact absurd ⟨hc.1.1, by simp [hc.1.2]⟩ h
  · have := (frame_validPayload sp hr hy hc.1 B hB).1 v hv
    omega

/-- The support of an honest voter's merged view is among its votes. -/
theorem merged_support_subset (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (σ : Nat) :
    (mergedVoteView sp e.readPoint ℓ.frame σ).support ⊆
      (mergedVoteView sp e.readPoint ℓ.frame σ).votes := by
  rintro v (hv | ⟨B, hB, hBs, hv, -⟩)
  · exact Or.inl (List.mem_of_mem_filter hv)
  · exact Or.inr ⟨B, hB, hBs, (frame_validPayload sp hr hy hc.1 B hB).2 v hv⟩

/-- The validators counted for an update result are a strict majority of the update's
participants. -/
theorem result_majority {X : Fin sp.n} {i₀ s : Nat} {C : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hres : ResultAt tr X i₀ s C CV) :
    (voters {v | v ∈ (tr.state X i₀).pool s}).ncard < 2 * {w | ∃ v ∈ CV, v.val = w}.ncard := by
  obtain ⟨ℓ, -, hC, rfl⟩ := hres
  have hmaj := ((deepest_mem hC).1).2.2
  refine lt_of_lt_of_le hmaj (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard ?_))
  rintro w ⟨hw, x, ⟨hx, hres⟩, hval, -, hanc⟩
  exact ⟨x, ⟨hx, hval ▸ hw, hres, hanc⟩, hval⟩

/-- Under the writer-pool condition (d), the voters of `y`'s merged view are participants at
`X`. -/
theorem merged_voters_subset (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) {s : Nat} {P : List (Vote sp.n)}
    (hd : ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ P ∨ v.val ∈ equivocators {w | w ∈ P}) :
    voters (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes ⊆ voters {v | v ∈ P} := by
  rintro w ⟨v, hv, rfl⟩
  rcases hd v hv (merged_vote_slot hr hy hc v hv) with h | ⟨x, hx, -, -, -, hxv, -⟩
  · exact ⟨v, h, rfl⟩
  · exact ⟨x, hx, hxv⟩

/-- **A carried vote is a supporter.** A slot-`s` vote that an honest voter of slot `s + 1`
holds, received before the vote freeze `t_s + 3Δ`, whose head (of slot at most `s`) extends a
block `C` of the voter's tree and was accepted by the voter before the freeze, and whose
validator does not equivocate in the voter's merged view, makes that validator a supporter of
`C` there (the head is still in the voter's tree, and the vote is resolved before the freeze:
the voter is joined, so its restarts were before `t_s`). -/
theorem carried_supporter (hrun : ACRun tr H U) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e) {s : Nat}
    (hs : e.msg.slot = s + 1) {C : Blk sp.n FGP} (hC : C ∈ ℓ.frame.tree) {v : Vote sp.n}
    (hvs : v.slot = s) (hheld : HeldBefore e.readPoint v (sp.ts s + 3 * sp.Δ))
    (hhead : ∃ Hv ∈ U, Hv.root = v.head ∧ Hv.slot ≤ s ∧ Anc U C Hv ∧
      AcceptedBefore tr y Hv (sp.ts s + 3 * sp.Δ))
    (hneq : v.val ∉ equivocators (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes) :
    v.val ∈ supporters ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s C := by
  sorry

/-- The validators counted for an update result are supporters of it in an honest voter's
merged view of the next slot (A1.8 (a), (c), (d)). -/
theorem result_supporters (hrun : ACRun tr H U) {X y : Fin sp.n} (hX : X ∈ H) (hy : y ∈ H)
    {i₀ i s : Nat} {C : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hres : ResultAt tr X i₀ s C CV)
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1) (hcarry : CarryAt tr U y i e s CV)
    (hviab : ViableAtVote ℓ e (s + 1) C)
    (hd : ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s}) :
    {w | ∃ v ∈ CV, v.val = w} ⊆
      supporters ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s C := by
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨ℓX, ⟨hcX, -, -, -⟩, -, rfl⟩ := hres
  obtain ⟨hΦX, hΦXU⟩ : FrameOK ℓX.frame ∧ ℓX.frame.tree ⊆ U := by
    rcases hr.frameLaw X hX i₀ ℓX hcX with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
      exact h.1
  have hCt : C ∈ ℓ.frame.tree := by
    obtain ⟨hΦ, -⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
      rcases hr.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
        exact h.1
    rcases hviab with h | h
    · exact h.1.1
    · exact mem_of_anc h hΦ.fcRoot_mem
  -- a validator that is not an equivocator at `X` has at most one vote in `y`'s merged view
  have hone : ∀ w ∉ equivocators {x | x ∈ (tr.state X i₀).pool s}, ∀ v₁ v₂,
      v₁ ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes →
      v₂ ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes →
      v₁.val = w → v₂.val = w → v₁ = v₂ := by
    intro w hw v₁ v₂ h₁ h₂ hv₁ hv₂
    by_contra hne
    rcases hd v₁ h₁ (merged_vote_slot hr hy hc v₁ h₁) with h₁' | h₁'
    · rcases hd v₂ h₂ (merged_vote_slot hr hy hc v₂ h₂) with h₂' | h₂'
      · exact hw ⟨v₁, h₁', v₂, h₂', hne, hv₁, hv₂⟩
      · exact hw (hv₂ ▸ h₂')
    · exact hw (hv₁ ▸ h₁')
  rintro w ⟨v, ⟨hvp, hvw, hvres, hvanc⟩, rfl⟩
  have hvs : v.slot = s := state_pool_slot sp hr hX i₀ s v hvp
  -- the head is the block of `X`'s tree that the vote resolves on, of slot at most `s`
  obtain ⟨Hd, hHd, hHdr, hHds⟩ : ∃ Hd ∈ ℓX.frame.tree, Hd.root = v.head ∧ Hd.slot ≤ v.slot := by
    unfold resolutionTime at hvres
    split at hvres
    · exact absurd hvres (by simp [ETime.of])
    · rename_i Hd hl
      obtain ⟨hHd, hHdr⟩ := lookup_eq_some hl
      split_ifs at hvres with hlt
      · exact absurd hvres (by simp [ETime.of])
      · exact ⟨Hd, hHd, hHdr, by omega⟩
  have hCHd : Anc U C Hd := by
    obtain ⟨R, hR, hRr, hCR⟩ := hvanc
    have : R = Hd := hΦXU hR |> fun h => hU.1 h (hΦXU hHd) (hRr.trans hHdr.symm)
    subst this
    exact Anc.mono hΦXU hCR
  -- `y` holds `v` itself: two other votes of its validator would make it an equivocator at `X`
  have hheld : HeldBefore e.readPoint v (sp.ts s + 3 * sp.Δ) := by
    rcases hcarry.holds v ⟨hvp, hvw, hvres, hvanc⟩ with h | ⟨v₁, v₂, h12, h1, -, hv₁, hv₂, hs₁, hs₂,
      hh₁, hh₂⟩
    · exact h
    · exfalso
      have hm : ∀ u, u.slot = s → HeldBefore e.readPoint u (sp.ts s + 3 * sp.Δ) →
          u ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes := by
        intro u hus hu
        refine Or.inl (List.mem_filter.2 ⟨?_, ?_⟩)
        · simp only [SAState.poolAt, show ¬ (((s + 1 : Nat) : Int) - 1 < 0) by omega, ite_false]
          simpa [hus] using hu.1
        · simpa [freeze] using hu.2
      exact h12 (hone _ hvw v₁ v₂ (hm v₁ hs₁ hh₁) (hm v₂ hs₂ hh₂) hv₁ hv₂)
  obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads v ⟨hvp, hvw, hvres, hvanc⟩
  have hHvd : Hv = Hd := hU.1 hHv (hΦXU hHd) (hHvr.trans hHdr.symm)
  subst hHvd
  refine carried_supporter hrun hy hc hs hCt hvs hheld
    ⟨Hv, hHv, hHvr, hvs ▸ hHds, hCHd, hacc Hv Relation.ReflTransGen.refl⟩ fun hq => ?_
  obtain ⟨x, hx, x', hx', hne, hxv, hx'v⟩ := hq
  exact hne (hone _ hvw x x' hx hx' hxv hx'v)

end Consensus.Goldilocks.SA

end
