module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.RowPools
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.PrefixSteps

public section

/-! # A slot-start signing follows only the signer's own current-slot votes

This local execution lemma has no reset or retention invariant. Consumers apply
it only to the signer's finite honest prefix.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- An optimistic write before a slot-start signing counts only the signer's own vote. -/
theorem slot_start_optimistic
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {v : Fin sp.n} (hv : v ∈ H) {d : Nat} {att : FG.Att sp.n}
    (hs : tr.SignAt v d att) {m : Nat} (hdt : tr.time d = sp.ts m)
    {r : Nat} (hrd : r < d) {D : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (hopt : SA.OptimisticLockAt tr.projAC v r m D CV) :
    sp.n = 1 ∧ ∃ j' ≤ r, ∃ e', SA.VoteAt tr.projAC v j' e' ∧ e'.msg.slot = m :=
  Healing.slot_start_optimistic hrun hnc hv hs hdt hrd hopt

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
