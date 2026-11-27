module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighInduction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.VoteReceipt
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.OldSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.VoteDomain
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts

public section

/-! # P-U shadow kernel: the retained-vote induction and R1

The stock healing kernel's R1 chain over the shadow run, read off the reset core
(`ResetPremisesUpTo'.toCore`):

* `ResetPremisesUpTo'.high_origin_held_at_vote_at'` and
  `KernelProof.high_origin_votes_of_domain_before_at'` (HighInduction, the vote domain an
  explicit input): the core versions of the stock lemmas.
* `ResetPremisesUpTo'.high_origin_votes_before_at'` (ResetFacts, R2): the deep quarantine arm
  plugs in the P-U vote domain (`held_target_vote_domain_before_of_quarantine_at'`); the cover
  arm is S2 of the high-source cover; stock proof.
* `ResetPremisesUpTo'.origins_compatible_at'` (ResetFacts, R1, through
  `ResetRunCore.origins_compatible_of_votes_at`) and
  `ProposalImpl.finalized_compatible_high_origin_at'` (Pivot/OldSources); stock proofs. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)
open Consensus.Goldilocks.Store

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
  {hold : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

⟩ := hB
  have hfs := finalitySpec_updateFinality (P := sp.toParams) (ACP := Payload sp.n)
  have hr := (Compose.Growing.reachable_at hrun ht hy hle).reachableWith
  have hh := (accepted_tree_with hfs hr).2.2.2 B hBt
  have hsub := Compose.Growing.tree_held_at ht hy hle
  have he : G = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload :=
    (Coherence.honestBlocksAt_coherent hrun hnc).1 hG (hsub (genesis_mem_with hfs hr)) hg
  rw [he]
  exact hh.mono hsub

end Consensus.Goldilocks.Healing.Growing

end
