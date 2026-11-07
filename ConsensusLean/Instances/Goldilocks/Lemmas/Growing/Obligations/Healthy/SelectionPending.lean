module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation

public section

/-! # Pending growing proposal-passes interface

`Healing.Growing.ResetPremisesUpTo.reset_proposal_passes_at`, the growing form of the static
`reset_proposal_passes`, whose home is the growing kernel's selection module. It sits apart from
`OperationalPending` so that the operational report lemmas, which the selection cone imports, do
not import it.

Each theorem here is an open `sorry`; this module is deleted when the home module lands. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- A post-drain proposal call of a node honest at it extends every high origin before its slot. -/
theorem reset_proposal_passes_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i))
    (hR : drainTime sp a ≤ sp.ts u) {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) :
    ∀ O, (∃ x r l, HighOrigin tr H g x r l O ∧ tr.time r < sp.ts u) →
      Anc (tr.HonestBlocksAt H) O d.head := by
  sorry

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
