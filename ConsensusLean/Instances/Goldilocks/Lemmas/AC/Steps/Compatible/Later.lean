module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock

public section

/-! # Goldilocks SA: a fast lock of a later slot is compatible (A1.9, source slot after `s`)

A fast lock of a slot `s'` that an honest node writes at a cut before `i` needs at least half of
the committee as non-equivocating supporters of its block (the fast test of the update of `s'`),
or three quarters as optimistic voters (an optimistic confirmation); with `f < n/2` one of them
is honest, and its slot-`s'` vote was cast before the write. When every honest vote of slot `s'`
before `i` extends `B`, the lock's block is compatible with `B`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

/-- **A fast lock supported by votes that extend `B` is compatible with `B`.** -/
theorem fastLock_compatible_of_votes (hrun : ACRun proposer tr H U) {x : Fin sp.n} (hx : x ∈ H)
    {j i s' : Nat} (hji : j < i) {B B' : Blk sp.n FGP} {CV' : Set (Vote sp.n)}
    (hfl : FastLockAt tr x j s' B' CV') (hf : 2 * Hᶜ.ncard < sp.n)
    (hvotes : ∀ z ∈ H, ∀ j' < i, ∀ e, VoteAt tr z j' e → e.msg.slot = s' → VoteExtends U e.msg B) :
    Compatible U B' B := by
  sorry

end Consensus.Goldilocks.SA

end
