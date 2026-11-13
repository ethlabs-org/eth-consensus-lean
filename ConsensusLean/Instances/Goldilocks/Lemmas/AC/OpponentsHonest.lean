module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.UnlockViewOpponents

public section

/-! # Goldilocks SA: the opponents of a block are outside the validators that do not oppose it

The static half of the drain link. Let `Hn` be a
set of validators (the honest ones). If no validator of `Hn` equivocates in the votes of a view,
and every slot-`s` support vote of a validator of `Hn` has heads in the tree that are compatible
with `B`, then the opponents of `B` lie outside `Hn` (`opponents_subset_compl`). With
`2 · |Hnᶜ| < committeeSize`, `unlock` keeps `B` against the view of a call
(`unlockTarget_unlockView_held_of_honest_slot`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {Φ : Frm sp.n FGP} {t : Time}

/-- **The opponents of `B` are not in `Hn`** when no validator of `Hn` equivocates in
`V.votes` and every slot-`s` support vote of `Hn` has only heads compatible with `B`. -/
theorem opponents_subset_compl {V : View sp.n} {s : Int} {B : Blk sp.n FGP}
    {Hn : Set (Fin sp.n)}
    (hne : ∀ x ∈ V.votes, ∀ y ∈ V.votes, x.val ∈ Hn → y.val = x.val → x = y)
    (hcompat : ∀ x ∈ V.support, x.val ∈ Hn → (x.slot : Int) = s →
      ∀ H ∈ Φ.tree, H.root = x.head → Compatible Φ.tree H B) :
    opponents sp Φ V s B ⊆ Hnᶜ := by
  rintro i (⟨x, hx, y, hy, hxy, rfl, hyi⟩ | ⟨x, hx, rfl, hs, H, hH, hr, hc⟩) hi
  · exact hxy (hne x hx y hy hi hyi)
  · exact hc (hcompat x hx hi hs H hH hr)

/-! ## Per-slot non-equivocation

`opponents_subset_compl` asks that a validator of `Hn` have at most one vote in the view, of any
slot. An honest validator votes once per slot, and `heldVotes A A' Φ` holds the votes of every
pool and every block of the tree, so for an honest `Hn` that premise fails on the held votes as
soon as one of its validators has held votes of two slots. The view that `unlock` reads holds
only slot-`(slot(t) − 1)` votes (`unlockView_votes_slot`: the pools hold votes of their own slot,
and a block's votes are of the slot before it), so `hne` of
`unlockTarget_unlockView_held_of_honest_slot` asks only that a validator of `Hn` have at most one
held vote of slot `slot(t) − 1`. -/

/-- The votes of a pool view of slot `σ` are of slot `σ` when every pool holds votes of its own
slot. -/
theorem voteViewList_votes_slot {A : SAState sp.n} {σ : Int} {cutoff : ETime}
    (hp : ∀ τ, ∀ v ∈ A.pool τ, v.slot = τ) :
    ∀ v ∈ (View.ofLists (voteViewList A Φ σ cutoff)).votes, (v.slot : Int) = σ := by
  intro v hv
  simp only [voteViewList, View.ofLists, Set.mem_ofPred_eq, List.mem_filter,
    decide_eq_true_eq] at hv
  have h := hv.1
  unfold SAState.poolAt at h
  split_ifs at h with hσ
  · exact absurd h List.not_mem_nil
  · rw [hp _ v h]; omega

/-- The votes of the merged view of slot `s` are of slot `s − 1` when every pool holds votes of
its own slot and every block of the tree has a valid payload. -/
theorem mergedVoteView_votes_slot {A : SAState sp.n} (s : Nat)
    (hp : ∀ τ, ∀ v ∈ A.pool τ, v.slot = τ) (hpay : ∀ C ∈ Φ.tree, validPayload C) :
    ∀ v ∈ (mergedVoteView sp A Φ s).votes, (v.slot : Int) = (s : Int) - 1 := by
  rintro v (hv | ⟨C, hC, hCs, hv⟩)
  · exact voteViewList_votes_slot hp v hv
  · have := (hpay C hC).1 v hv
    omega

/-- **The view of a call holds only slot-`(slot(t) − 1)` votes** when the pools before and
after the call hold votes of their own slot and every block of `Φ.tree` has a valid payload. -/
theorem unlockView_votes_slot {ro : ReplayOrder sp FGP} (self : Fin sp.n) {A : SAState sp.n}
    (c : (goldilocksSA sp FGP ro).Call) (hpre : ∀ τ, ∀ v ∈ A.pool τ, v.slot = τ)
    (hpost : ∀ τ, ∀ v ∈ ((goldilocksSA sp FGP ro).step self A Φ t c).1.pool τ, v.slot = τ)
    (hpay : ∀ C ∈ Φ.tree, validPayload C) :
    ∀ v ∈ (unlockView A Φ t c).votes, (v.slot : Int) = (sp.slot t : Int) - 1 := by
  cases c with
  | tick => rw [unlockView_tick]; exact mergedVoteView_votes_slot _ hpre hpay
  | proposal => rw [unlockView_proposal]; exact voteViewList_votes_slot hpre
  | toFG => rw [unlockView_toFG]; exact mergedVoteView_votes_slot _ hpre hpay
  | restart => rw [unlockView_restart]; exact mergedVoteView_votes_slot _ hpre hpay
  | message m =>
    rw [unlockView_message]
    exact mergedVoteView_votes_slot _
      (fun τ x hx => hpost τ x ((grows_tryVote (sp := sp) self _ Φ t).mem hx)) hpay
  | block C =>
    rw [unlockView_block]
    exact mergedVoteView_votes_slot _
      (fun τ x hx => hpost τ x ((grows_tryVote (sp := sp) self _ Φ t).mem hx)) hpay

/-- **`unlock` keeps `B` when `Hn` does not oppose it, per-slot form.** For a call `c` from `A`
to `A'` whose pools hold votes of their own slot, with a frame whose blocks have valid payloads:
if no validator of `Hn` has two held votes of slot `slot(t) − 1`, every held slot-`s` vote of `Hn`
has only heads compatible with `B`, and `2 · |Hnᶜ| < committeeSize`, then `unlockTarget` of the
call's view is `B`. -/
theorem unlockTarget_unlockView_held_of_honest_slot {ro : ReplayOrder sp FGP} (self : Fin sp.n)
    {A A' : SAState sp.n} (c : (goldilocksSA sp FGP ro).Call)
    (hA' : ((goldilocksSA sp FGP ro).step self A Φ t c).1 = A') (hΦ : FrameOK Φ) (s : Int)
    {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) {Hn : Set (Fin sp.n)}
    (hpre : ∀ τ, ∀ v ∈ A.pool τ, v.slot = τ) (hpost : ∀ τ, ∀ v ∈ A'.pool τ, v.slot = τ)
    (hpay : ∀ C ∈ Φ.tree, validPayload C)
    (hne : ∀ x ∈ heldVotes A A' Φ, ∀ y ∈ heldVotes A A' Φ, x.val ∈ Hn → y.val = x.val →
      x.slot = y.slot → (x.slot : Int) = (sp.slot t : Int) - 1 → x = y)
    (hcompat : ∀ x ∈ heldVotes A A' Φ, x.val ∈ Hn → (x.slot : Int) = s →
      ∀ H ∈ Φ.tree, H.root = x.head → Compatible Φ.tree H B)
    (hf : 2 * Hnᶜ.ncard < sp.committeeSize) :
    unlockTarget sp Φ (unlockView A Φ t c) s B = B := by
  subst hA'
  have hsub := unlockView_subset_post (S := heldVotes A
    ((goldilocksSA sp FGP ro).step self A Φ t c).1 Φ) self c
    (fun τ _ hv => mem_heldVotes.2 (Or.inl ⟨τ, hv⟩))
    (fun τ _ hv => mem_heldVotes.2 (Or.inr (Or.inl ⟨τ, hv⟩)))
    (fun C hC _ hv => mem_heldVotes.2 (Or.inr (Or.inr ⟨C, hC, hv⟩)))
  have hsl := unlockView_votes_slot self c hpre hpost hpay
  let W : Set (Vote sp.n) := {v | v ∈ heldVotes A ((goldilocksSA sp FGP ro).step self A Φ t
    c).1 Φ ∧ (v.slot : Int) = (sp.slot t : Int) - 1}
  have hW := opponents_subset_compl (Φ := Φ) (s := s) (B := B)
    (V := ⟨W, heldVotes A ((goldilocksSA sp FGP ro).step self A Φ t c).1 Φ⟩)
    (fun x hx y hy hxH hyx =>
      hne x hx.1 y hy.1 hxH hyx (by have := hx.2.trans hy.2.symm; omega) hx.2)
    hcompat
  exact unlockTarget_eq_self_of_subset hΦ _ s hB
    ((opponents_mono_view (W := ⟨W, _⟩) (fun v hv => ⟨hsub.1 hv, hsl v hv⟩) hsub.2 s B).trans
      hW) hf

end Consensus.Goldilocks.SA

end
