module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer

public section

/-! # Goldilocks Healing: H.2 (i), the votes of a slot with an honest proposal and `Geo`

workbench `h2-open-items.md` §§1, 4, 6, by induction on the cut of the first honest slot-`p`
vote not on `P`: the voter's anchor is below `P` (`Duty(P)`'s first clause, §6 with §6.1,
`h2_duty_anchor`, open); then the voter's walk reaches the proposer's path (§6, second clause),
the retained heads give equal scores and majority eligibility on it (§1), `Geo` aligns the
low-parent eligibility arm, and the persist/reflect comparison (§4) makes the vote `P`
(`h2_votes_of_duty`, open). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g t₀ : Time}

/-- **§6 `Duty(P)`, first clause, with §6.1**: at every honest vote of slot `p`, the anchor of the
voter's walk after its unlocking is an ancestor of `P` (every surviving lock is an ancestor of
its clean raw origin, of a label below `p`, which §3 puts below `parent(P)`; a slot-`p`
optimistic lock before the first vote not on `P` has the honest supporter `P`). -/
theorem h2_duty_anchor (hI : InclusionRun tr H U g t₀) {p : Nat} {P : Blk sp.n FGP}
    (hpH : sp.toParams.proposer p ∈ H) (hP : HonestProposal tr (sp.toParams.proposer p) p P)
    (hp : t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ)) :
    ∀ x ∈ H, ∀ i ℓ e, CastAt tr x i ℓ e → e.msg.slot = p → (∀ y ∈ H, ∀ j e', VoteAt tr y j e' →
      e'.msg.slot = p → j < i → e'.msg.head = P.root) →
      Anc U (getAnchor sp e.readPoint ℓ.frame (tr.time i)) P := by
  sorry

/-- **§§1, 4, with §6's second clause**: with every honest slot-`p` voter's anchor below `P` up to
the first vote not on `P`, `Geo(P)` makes every honest vote of slot `p` the proposal (the
reader's walk reaches the proposer's path, §6; on it the retained heads give equal scores and
majority eligibility, §1; `Geo` aligns the low-parent arm; persistence and reflection along the
path, §4). -/
theorem h2_votes_of_duty (hI : InclusionRun tr H U g t₀) {p : Nat} {P : Blk sp.n FGP}
    (hpH : sp.toParams.proposer p ∈ H) (hP : HonestProposal tr (sp.toParams.proposer p) p P)
    (hp : t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ)) (hgeo : Geo tr H p P)
    (hduty : ∀ x ∈ H, ∀ i ℓ e, CastAt tr x i ℓ e → e.msg.slot = p →
      (∀ y ∈ H, ∀ j e', VoteAt tr y j e' → e'.msg.slot = p → j < i → e'.msg.head = P.root) →
      Anc U (getAnchor sp e.readPoint ℓ.frame (tr.time i)) P) :
    ∀ i, ∀ x ∈ H, ∀ ℓ e, CastAt tr x i ℓ e → e.msg.slot = p →
      (∀ y ∈ H, ∀ j e', VoteAt tr y j e' → e'.msg.slot = p → j < i → e'.msg.head = P.root) →
      e.msg.head = P.root := by
  sorry

/-- **H.2 (i), §§1, 4, 6**: for an honest proposal `P` of slot `p` at `t_p ≥ t₀ + 2Θ + 8Δ` with
the locks settled from `t_{p−1}`, `Geo(P)` makes every honest vote of slot `p` the proposal (by
induction on the cut of the first vote not on `P`). -/
theorem h2_proposal_votes (hI : InclusionRun tr H U g t₀) {p : Nat} {P : Blk sp.n FGP}
    (hpH : sp.toParams.proposer p ∈ H) (hP : HonestProposal tr (sp.toParams.proposer p) p P)
    (hp : t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ)) (hgeo : Geo tr H p P) :
    ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root := by
  have hstep := h2_votes_of_duty hI hpH hP hp hset hgeo (h2_duty_anchor hI hpH hP hp hset)
  suffices h : ∀ j, ∀ x ∈ H, ∀ e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root from
    fun x hx j e hv hs => h j x hx e hv hs
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro x hx e ⟨ℓ, hc, he⟩ hs
    exact hstep j x hx ℓ e ⟨hc, he⟩ hs fun y hy j' e' hv hs' hj => ih j' hj y hy e' hv hs'

end Consensus.Goldilocks.SA

end
