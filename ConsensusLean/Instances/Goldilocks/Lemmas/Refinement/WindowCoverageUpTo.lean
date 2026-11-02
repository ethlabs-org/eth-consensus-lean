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

/-- **Coverage persists** along an honest node's states: the tree grows, the state of a held block
is unique, and a held root names its block. -/
theorem coverage_mono (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {j i : Nat} (hji : j ≤ i)
    {A B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y j).fg.tree)
    (h : ∃ F, (tr.state y j).fg.blocks ((tr.state y j).fg.σ B.root).F = some F ∧
      Anc (tr.HonestBlocks H) A F) :
    ∃ F, (tr.state y i).fg.blocks ((tr.state y i).fg.σ B.root).F = some F ∧
      Anc (tr.HonestBlocks H) A F := by
  obtain ⟨F, hF, hAF⟩ := h
  have hT := (Compose.fg_grows hrun hy hji).1
  rw [Healing.σ_eq_honest hrun hnc hy hy (hT hB) hB]
  have hr := (Compose.fg_reachable hrun.toLocalRun hy j).blocks_root hF
  have hFt : F ∈ (tr.state y j).fg.tree := by
    change _ = _
    rw [hr, hF]
  have hFi : (tr.state y i).fg.blocks F.root = some F := hT hFt
  exact ⟨F, hr ▸ hFi, hAF⟩

/-- **The post-store of a call** carries the coverage of the caller's state before it. -/
theorem coverage_post_of_call (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ} (hc : tr.CallAt y k ℓ)
    {A B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y k).fg.tree)
    (h : ∃ F, (tr.state y k).fg.blocks ((tr.state y k).fg.σ B.root).F = some F ∧
      Anc (tr.HonestBlocks H) A F) :
    ∃ F, (tr.post k).fg.blocks ((tr.post k).fg.σ B.root).F = some F ∧
      Anc (tr.HonestBlocks H) A F := by
  rw [← tr.state_succ_of_call hc]
  exact coverage_mono hrun hnc hy (Nat.le_succ k) hB h

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

/-- **Coverage on the last anchor's post-store** (the `coverage` input of
`final_cache_acceptance`): at a proposal cut `k` of the last anchor, with the window advance and
service on `(tr.post k).fg`. -/
theorem cacheCoverage_of_anchors_upTo
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {s : Fin 4 → Nat}
    {P : Fin 4 → SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ∀ i, Healing.HonestProposalRun tr H proposer (s i) (P i)) (hs : StrictMono s)
    (hR : Healing.drainTime sp a ≤ sp.ts (s 0)) (hb : sp.ts (s 3) ≤ b)
    (hadj : s 3 = s 2 + 1 → sp.ts (s 2) + 6 * sp.Δ ≤ b) {k : Nat}
    (hk : tr.ProposesAt (P 3).proposer k (P 3))
    (hadv : Store.WindowAdvance (tr.post k).fg (P 0) (P 3))
    (hsv : Store.WindowService (tr.post k).fg (P 0) (P 3)) :
    ∃ F, (tr.post k).fg.blocks ((tr.post k).fg.σ (P 3).root).F = some F ∧
      Anc (tr.HonestBlocks H) (P 0) F := by
  have hy : (P 3).proposer ∈ H := proposer_mem_of_honestProposalRun hp.run (hP 3)
  obtain ⟨-, hB, he⟩ := Healing.accept_of_proposesAt hp.run hp.noColl hy hk
  rw [he] at hadv hsv ⊢
  exact coverage_of_window_anchors_upTo hp hc hP hs hR hb hadj hy hB hadv hsv

end Consensus.Goldilocks.Refinement

end
