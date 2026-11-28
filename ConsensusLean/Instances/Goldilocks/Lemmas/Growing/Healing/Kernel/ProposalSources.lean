module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Healing.Proposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Healing.OriginLabel
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.ProposalReceipt
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.Viability
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Walk
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore

public section

/-! # Stored high-lock compatibility for post-drain proposals -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
variable {hold : Time}

/-- Post-drain live high locks are compatible with each bounded high origin. -/
theorem ResetPremisesUpTo.proposal_stored_locks_compatible_old_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i))
    (hR : drainTime sp a ≤ sp.ts u) {ell : ACLabel (goldilocksNode sp)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {x : Fin sp.n} {q j : Nat} {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x q j O) (hqb : tr.time q ≤ b) :
    AC.HighLocksCompatible (tr.HonestBlocksAt H) (tr.projAC.state p i)
      (tr.time i) (u - 1) O := by
  exact ProposalImpl.proposal_stored_locks_compatible_old_at hp hpH hR hci hcall hti hib ho hqb

end Consensus.Goldilocks.Healing.Growing

end
