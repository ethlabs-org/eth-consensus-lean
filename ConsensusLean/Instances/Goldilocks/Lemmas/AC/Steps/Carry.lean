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

/-- The support of an honest voter's merged view is among its votes. -/
theorem merged_support_subset (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (σ : Nat) :
    (mergedVoteView sp e.readPoint ℓ.frame σ).support ⊆
      (mergedVoteView sp e.readPoint ℓ.frame σ).votes := by
  sorry

/-- The validators counted for an update result are a strict majority of the update's
participants. -/
theorem result_majority (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {X : Fin sp.n}
    (hX : X ∈ H) {i₀ s : Nat} {C : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hres : ResultAt tr X i₀ s C CV) :
    (voters {v | v ∈ (tr.state X i₀).pool s}).ncard < 2 * {w | ∃ v ∈ CV, v.val = w}.ncard := by
  sorry

/-- Under the writer-pool condition (d), the voters of `y`'s merged view are participants at
`X`. -/
theorem merged_voters_subset (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) {s : Nat} {P : List (Vote sp.n)}
    (hd : ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ P ∨ v.val ∈ equivocators {w | w ∈ P}) :
    voters (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes ⊆ voters {v | v ∈ P} := by
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
  sorry

end Consensus.Goldilocks.SA

end
