module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.WindowAnchorsUpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealedC4
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Served

public section

/-! # Goldilocks Refinement: window coverage on the last anchor's post-store (#137)

consensus-lean#137. `coverage_of_window_anchors_upTo` concludes coverage in a holder state
`(tr.state y k).fg`. The final window reads the post-store `(tr.post k).fg` of the last anchor's
proposal cut. Here: coverage persists along an honest node's states (`coverage_mono`: the tree
grows, a held block's state is unique, a held root names its block), the post-store of a call is
the next state (`coverage_post_of_call`), the window fields from four honest anchors
(`finalWindow_fields_of_honest_anchors`), and the coverage on the last anchor's post-store
(`cacheCoverage_of_anchors_upTo`), the `coverage` input of `final_cache_acceptance`. -/

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- The proposer of an honest anchor is honest. -/
private theorem proposer_mem_of_honestProposalRun (hrun : GoldilocksRun proposer dg H tr)
    {s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.HonestProposalRun tr H proposer s P) : P.proposer ∈ H := by
  obtain ⟨k, hk⟩ := proposesAt_of_honestProposalRun hrun hP
  exact hk.2.1 ▸ hP.1

/-- **Window fields from four honest anchors**: proposal cuts with the proposals, the proposer's
acceptances, the post-store as the proposer's next state, and the chain (`window_anchors_chain_upTo`
guards). Not produced: `slots`, `ready`, `fresh`, `ordered`, `bounded`, `carrierProcessed`. -/
theorem finalWindow_fields_of_honest_anchors
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {s : Fin 4 → Nat}
    {P : Fin 4 → SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ∀ i, Healing.HonestProposalRun tr H proposer (s i) (P i)) (hs : StrictMono s)
    (hR : Healing.drainTime sp a ≤ sp.ts (s 0)) (hb : sp.ts (s 3) ≤ b)
    (hadj : s 3 = s 2 + 1 → sp.ts (s 2) + 6 * sp.Δ ≤ b) :
    ∃ cut : Fin 4 → Nat, (∀ i, tr.ProposesAt (P i).proposer (cut i) (P i)) ∧
      (∀ i, tr.AcceptAt (P i).proposer (cut i) (P i)) ∧
      (∀ i, P i ∈ (tr.post (cut i)).fg.tree) ∧
      (∀ i, tr.post (cut i) = tr.state (P i).proposer (cut i + 1)) ∧
      ∀ i j, i ≤ j → Anc (tr.HonestBlocks H) (P i) (P j) := by
  have hex : ∀ i, ∃ k, tr.ProposesAt (P i).proposer k (P i) := fun i => by
    obtain ⟨k, hk⟩ := proposesAt_of_honestProposalRun hp.run (hP i)
    exact ⟨k, hk.2.1 ▸ hk⟩
  choose cut hcut using hex
  have hacc := fun i => Healing.accept_of_proposesAt hp.run hp.noColl
    (proposer_mem_of_honestProposalRun hp.run (hP i)) (hcut i)
  refine ⟨cut, hcut, fun i => (hacc i).1, fun i => ?_, fun i => (hacc i).2.2,
    window_anchors_chain_upTo hp hc hP hs hR hb hadj⟩
  rw [(hacc i).2.2]
  exact (hacc i).2.1

end Consensus.Goldilocks.Refinement

end
