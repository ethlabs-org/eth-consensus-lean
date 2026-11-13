module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock

public section

/-! # Goldilocks SA: a fast lock of a later slot is compatible (A1.9, source slot after `s`)

A fast lock of a slot `s'` that an honest node writes at a cut before `i` needs at least half of
the committee as non-equivocating supporters of its block (the fast test of the update of `s'`),
or three quarters as optimistic voters (an optimistic confirmation); all of them are members of
the slot-`s'` committee `K` (P), so with `2|K(s') ∩ Hᶜ| < committeeSize` one of them is honest,
and its slot-`s'` vote was cast before the write. When every honest vote of slot `s'` before `i`
extends `B`, the lock's block is compatible with `B`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

/-- **A fast lock supported by votes that extend `B` is compatible with `B`.** -/
theorem fastLock_compatible_of_votes
    (hrun : ACRun proposer tr H U) (K : CommitteeDict sp.n) (hP : CommitteeP K tr H)
    {x : Fin sp.n} (hx : x ∈ H)
    {j i s' : Nat} (hji : j < i) {B B' : Blk sp.n FGP} {CV' : Set (Vote sp.n)}
    (hfl : FastLockAt tr x j s' B' CV') (hf : 2 * (K.committee s' ∩ Hᶜ).ncard < sp.committeeSize)
    (hvotes : ∀ z ∈ H, ∀ j' < i, ∀ e, VoteAt tr z j' e → e.msg.slot = s' → VoteExtends U e.msg B) :
    Compatible U B' B := by
  have hr := hrun.localRun
  have hU := hr.coherent
  rcases hfl with ⟨ℓ, C, ⟨hc, -⟩, -, hD, -⟩ | ⟨ℓ, A, hpt, hsl, hsel, -⟩
  · -- the fast test: an honest supporter's vote extends both blocks
    obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
      rcases hr.frameLaw x hx j ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨k, ℓ', -, -, -, h⟩ <;> exact h.1
    have hfast := (deepest_mem hD).1.2.2
    unfold FastTest confirmationScore at hfast
    dsimp only at hfast
    have hlt := Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le hf hfast)
    obtain ⟨u, ⟨-, v, ⟨hvp, -⟩, rfl, -, R, hR, hRr, hB'R⟩, hu⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard hlt
    have huH : v.val ∈ H := by
      by_contra h
      exact hu ⟨hP.1 x hx j s' v hvp, h⟩
    obtain ⟨j', hj', e, hve, rfl⟩ := hrun.honest.pool_vote x hx j s' _ hvp huH
    obtain ⟨Hd, hHd, hHdr, hBHd⟩ := hvotes _ huH j' (hj'.trans hji) e hve
      (state_pool_slot sp hr hx j s' _ hvp)
    obtain rfl : R = Hd := hU.1 (hΦU hR) hHd (hRr.trans hHdr.symm)
    exact anc_total hU (Anc.mono hΦU hB'R) hBHd
  · -- an optimistic confirmation: three quarters of the committee, one of them honest
    obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
      rcases hr.frameLaw x hx j ℓ hpt.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨k, ℓ', -, -, -, h⟩ <;> exact h.1
    unfold optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    have h34 := (deepest_mem hsel).1.2.1
    rw [hsl] at h34
    refine origin_compatible hU hΦU K h34
      (fun u ⟨v, hv, hvu, _⟩ => hvu ▸ hP.2 x hx j ℓ A hpt s' v hv) hf fun v hv hvH => ?_
    obtain ⟨hvs, j', hj', e, hve, rfl⟩ := optimisticPoint_pool_vote hrun hx hpt hv hvH
    exact hvotes _ hvH j' (lt_of_le_of_lt hj' hji) e hve hvs

end Consensus.Goldilocks.SA

end
