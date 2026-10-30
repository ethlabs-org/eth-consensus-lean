module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest

public section

/-! # Goldilocks SA: the locks at a voter after unlocking (A1.3)

The vote-transfer core needs every live lock block of the voter, after its unlocking, to be
compatible with the transferred block `B`.
* Unlocking against a view in which at least half of the committee have slot-`s` support votes
  whose heads extend `B` moves every lock of a slot below `s` to a block compatible with `B`:
  an ancestor that conflicts with `B` has all of them as opponents (`unlock_compatible`).
* At an honest slot-`(m+1)` vote whose slot-`m` honest votes all extend `B`, the remaining locks
  (of slot `m` or `m + 1`) are optimistic locks written before the vote (an update of slot `m`
  runs at `t_m + 6Δ`, after it), whose `3n/4` optimistic voters would include an honest
  validator voting for a block that conflicts with `B` (`f < n/2`) (`locks_compatible_next`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-- **Unlocking against support for `B`.** -/
theorem unlock_compatible {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {V : View sp.n} {s : Int}
    {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) {S : Set (Fin sp.n)}
    (hS : ∀ w ∈ S, ∃ x ∈ V.support, x.val = w ∧ (x.slot : Int) = s ∧ AncR Φ B x.head)
    (hn : sp.n ≤ 2 * S.ncard) (L : Set Lock) (t : Time) :
    ∀ l ∈ unlock sp L Φ t s V, (l.slot : Int) < s → ∀ X ∈ Φ.tree, X.root = l.block →
      Compatible Φ.tree X B := by
  rintro l' ⟨l, -, B₀, -, -, rfl⟩ hlt X hX hXr
  split_ifs at hlt hXr with h
  · simp only at hXr
    -- the unlock target is in the tree, so it is `X`
    unfold unlockTarget at hXr
    rcases hd : deepest Φ {B' | B' ∈ Φ.tree ∧ Φ.Anc B' B₀ ∧ 2 * (opponents sp Φ V s B').ncard <
        sp.n} with _ | T
    · rw [hd] at hXr
      have : X = Φ.F := hΦ.coherent.1 hX hΦ.rooted.1 hXr
      subst this
      exact (compatible_F hΦ hB).symm
    · rw [hd] at hXr
      obtain ⟨⟨hT, -, hopp⟩, -⟩ := deepest_mem hd
      have : X = T := hΦ.coherent.1 hX hT hXr
      subst this
      by_contra hnc
      -- every member of `S` opposes `X`
      have hSo : S ⊆ opponents sp Φ V s X := by
        intro w hw
        obtain ⟨x, hx, hxv, hxs, R, hR, hRr, hBR⟩ := hS w hw
        refine Or.inr ⟨x, hx, hxv, hxs, R, hR, hRr, ?_⟩
        rintro (hc | hc)
        · exact hnc (Or.inr (Relation.ReflTransGen.trans hBR hc))
        · exact hnc (anc_total hΦ.coherent hc hBR)
      have := Set.ncard_le_ncard hSo
      omega
  · exact absurd hlt h

variable {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
  {tr : SATrace sp FGP ro}

/-- **The locks at a next-transfer vote.** At an honest `y`'s slot-`(m+1)` vote: if every
honest slot-`m` vote extends `B`, at least half of the committee have slot-`m` support votes in
`y`'s merged view whose heads extend `B`, `f < n/2`, and every honest slot-`(m+1)` vote at an
earlier cut extends `B`, then every live lock block at the vote's read point is compatible with
`B`. -/
theorem locks_compatible_next (hrun : ACRun tr H U) {y : Fin sp.n} (hy : y ∈ H) {i m : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = m + 1) {B : Blk sp.n FGP} (hB : B ∈ ℓ.frame.tree)
    (hall : ∀ x ∈ H, ∀ j e', VoteAt tr x j e' → e'.msg.slot = m → VoteExtends U e'.msg B)
    {S : Set (Fin sp.n)}
    (hS : ∀ w ∈ S, ∃ x ∈ (mergedVoteView sp e.readPoint ℓ.frame (m + 1)).support,
      x.val = w ∧ x.slot = m ∧ AncR ℓ.frame B x.head)
    (hn : sp.n ≤ 2 * S.ncard) (hf : 2 * Hᶜ.ncard < sp.n)
    (hearlier : EarlierVotesExtend tr H U i (m + 1) B) :
    ∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L B := by
  sorry

end Consensus.Goldilocks.SA

end
