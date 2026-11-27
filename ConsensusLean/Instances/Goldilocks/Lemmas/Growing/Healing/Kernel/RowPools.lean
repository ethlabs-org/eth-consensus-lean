module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Prefix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.PrefixSteps

public section

/-! # Pool changes within the signer's slot-start tick

These transition facts have no run or honesty assumptions.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

variable {FGP : Type} {sp : AC.ACParams}

theorem admit_pool_mem {A : AC.ACState sp.n} {t : Time} {m w : AC.Vote sp.n} {s : Nat}
    (h : w ∈ (AC.admitVote sp A t m).pool s) : w ∈ A.pool s ∨ w = m :=
  Healing.admit_pool_mem h

theorem receipt_pool_mem {A : AC.ACState sp.n} {t : Time} {B : AC.Blk sp.n FGP}
    {w : AC.Vote sp.n} {s : Nat} (h : w ∈ (AC.blockReceipt sp A t B).pool s) :
    w ∈ A.pool s ∨ w ∈ AC.declaredHeadVotes B :=
  Healing.receipt_pool_mem h

/-- At a slot start, a nondelivery call takes only own votes or votes from its input block. -/
theorem step_pool_new (self : Fin sp.n) (A : AC.ACState sp.n) (Φ : AC.Frm sp.n FGP)
    {t : Time} (ht : t = sp.ts (sp.slot t)) (hΔ : 0 < sp.Δ) (c : (AC.goldilocksAC sp FGP).Call)
    (hm : ∀ m, c ≠ .message m) (hc : c ≠ .restart) {w : AC.Vote sp.n} {s : Nat}
    (h : w ∈ ((AC.goldilocksAC sp FGP).step self A Φ t c).1.pool s) :
    w ∈ A.pool s ∨ w.val = self ∨ ∃ B, c = .block B ∧ w ∈ AC.declaredHeadVotes B :=
  Healing.step_pool_new self A Φ ht hΔ c hm hc h

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
