module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer

public section

/-! # Goldilocks Healing: H.2 (i), the votes of a slot with an honest proposal and `Geo`

workbench `h2-open-items.md` §§1, 4, 6: with the locks settled before the proposal, the proposer's
and every voter's walks share the reached suffix (`Duty(P)`, §6, from the raw-origin transfer
§6.1); on it the retained heads give equal scores and majority eligibility (§1), `Geo` aligns the
low-parent eligibility arm, and the persist/reflect walk comparison (§4) makes every honest vote
of slot `p` the proposal `P`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g t₀ : Time}

/-- **H.2 (i), §§1, 4, 6**: for an honest proposal `P` of slot `p` at `t_p ≥ t₀ + 2Θ + 8Δ` with
the locks settled from `t_{p−1}`, `Geo(P)` makes every honest vote of slot `p` the proposal. -/
theorem h2_proposal_votes (hI : InclusionRun tr H U g t₀) {p : Nat} {P : Blk sp.n FGP}
    (hpH : sp.toParams.proposer p ∈ H) (hP : HonestProposal tr (sp.toParams.proposer p) p P)
    (hp : t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ)) (hgeo : Geo tr H p P) :
    ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root := by
  sorry

end Consensus.Goldilocks.SA

end
