module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission

public section

/-! # Goldilocks SA: honest votes in a voter's merged view

Under the honest-object facts (unforgeable signatures) and one vote per slot (A0.8): every
vote of an honest validator in an honest voter's merged view was emitted by that validator's
node no later than the vote, so an honest validator is never an equivocator there; and an
honest vote's head is a block of the voter's frame, of a slot no later than the vote's. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}

/-- A vote of an honest validator in an honest voter's merged view was emitted by its node at
a cut no later than the voter's call. -/
theorem honest_merged_vote (hrun : ACRun tr H U) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e) {σ : Nat}
    {v : Vote sp.n} (hv : v ∈ (mergedVoteView sp e.readPoint ℓ.frame σ).votes)
    (hvH : v.val ∈ H) : ∃ j ≤ i, ∃ e', VoteAt tr v.val j e' ∧ e'.msg = v := by
  sorry

/-- An honest validator is not an equivocator in an honest voter's merged view. -/
theorem honest_not_equivocator (hrun : ACRun tr H U) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e) {σ : Nat}
    {w : Fin sp.n} (hw : w ∈ H) :
    w ∉ equivocators (mergedVoteView sp e.readPoint ℓ.frame σ).votes := by
  sorry

/-- An honest vote's head is a block of its voter's frame, of a slot no later than the
vote's. -/
theorem honest_head (hrun : ACRun tr H U) {x : Fin sp.n} (hx : x ∈ H) {j : Nat}
    {e : Em sp FGP} (hv : VoteAt tr x j e) :
    ∃ Hd ∈ U, Hd.root = e.msg.head ∧ Hd.slot ≤ e.msg.slot := by
  sorry

end Consensus.Goldilocks.SA

end
