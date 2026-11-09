module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Prefix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.PrefixSteps

public section

/-! # Pool changes within the signer's slot-start tick

These transition facts have no run or honesty assumptions.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

variable {FGP : Type} {sp : SA.SAParams} {ro : SA.ReplayOrder sp FGP}

theorem admit_pool_mem {A : SA.SAState sp.n} {t : Time} {m w : SA.Vote sp.n} {s : Nat}
    (h : w ∈ (SA.admitVote sp A t m).pool s) : w ∈ A.pool s ∨ w = m :=
  Healing.admit_pool_mem h

theorem receipt_pool_mem {A : SA.SAState sp.n} {t : Time} {B : SA.Blk sp.n FGP}
    {w : SA.Vote sp.n} {s : Nat} (h : w ∈ (SA.blockReceipt sp A t B).pool s) :
    w ∈ A.pool s ∨ w ∈ SA.blockVotes B :=
  Healing.receipt_pool_mem h

/-- At a slot start, a nondelivery call takes only own votes or votes from its input block. -/
theorem step_pool_new (self : Fin sp.n) (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP)
    {t : Time} (ht : t = sp.ts (sp.slot t)) (hΔ : 0 < sp.Δ) (c : (SA.goldilocksSA sp FGP ro).Call)
    (hm : ∀ m, c ≠ .message m) (hc : c ≠ .restart) {w : SA.Vote sp.n} {s : Nat}
    (h : w ∈ ((SA.goldilocksSA sp FGP ro).step self A Φ t c).1.pool s) :
    w ∈ A.pool s ∨ w.val = self ∨ ∃ B, c = .block B ∧ w ∈ SA.blockVotes B :=
  Healing.step_pool_new self A Φ ht hΔ c hm hc h

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
