module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer

public section

/-! # Goldilocks Healing: H.2 (ii), persistent inclusion after a unanimous honest proposal

workbench `h2-open-items.md` §7: the unanimous batch of slot `p` propagates to every later honest
vote and proposal (§7.1); every surviving lock image compares with `P` (§7.2); the first test at
`t_p + 6Δ` leaves a record extending `P` or `P ⪯ Φ.F` (§7.3), which every later step keeps
(§7.4); and the full-tree walk extends `P` at every read (§7.5), so `P ⪯ ac_confirmed`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g t₀ : Time}

/-- **H.2 (ii), §7**: for an honest proposal `P` of slot `p` at `t_p ≥ t₀ + 2Θ + 8Δ` with the
locks settled from `t_{p−1}`, if every honest vote of slot `p` is `P`, then at every call of an
honest node from `t_p + 6Δ` on (at `t_p + 6Δ` itself, from its tick there on),
`P ⪯ ac_confirmed` after the call. -/
theorem h2_proposal_confirmed (hI : InclusionRun tr H U g t₀) {p : Nat} {P : Blk sp.n FGP}
    (hpH : sp.toParams.proposer p ∈ H) (hP : HonestProposal tr (sp.toParams.proposer p) p P)
    (hp : t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ))
    (hunan : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root) :
    ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
      (tr.time j = sp.ts p + 6 * sp.Δ →
        ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
      Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j)) := by
  sorry

end Consensus.Goldilocks.SA

end
