module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.FoundationSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin

public section

/-! # Optimistic support counted at the writer's own cut -/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- A bounded optimistic source has a supporter honest through the source's observation. -/
theorem optimistic_supporter_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x : Fin sp.n} {r s : Nat} (hx : x ∈ H (tr.time r))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hop : SA.OptimisticLockAt tr.projAC x r s B CV) (hrb : tr.time r ≤ b) :
    B ∈ (tr.state x r).fg.tree ∧ ∃ z ∈ H (tr.time r), ∃ q ≤ r, ∃ e,
      SA.VoteAt tr.projAC z q e ∧ e.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hac.upTo (hp.run.time_nonneg r)
  obtain ⟨ell, A, hpt, hsl, hsel, _⟩ := hop
  have hpt' := (SA.upTo_optimisticPoint hp.run.time_mono).mpr ⟨le_rfl, hpt⟩
  have hU := (SA.frameIn_of_callAt hr.localRun hx hpt'.1).2
  unfold SA.optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  refine ⟨frame_tree_subset_at hp.run hp.noColl hx hpt.1 |>.2
    ((SA.deepest_mem hsel).1.1), ?_⟩
  have h34 := (SA.deepest_mem hsel).1.2.1
  obtain ⟨z, ⟨v, hv, rfl, R, hR, hRr, hBR⟩, hz⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (s := (H (tr.time r))ᶜ)
      (t := SA.optimisticVoters sp A ell.frame (sp.slot (tr.projAC.time r)) B)
      (by
        have hf := hp.faults (tr.time r) (hp.run.time_nonneg r) hrb
        have hn := Fin.pos x
        omega)
  obtain ⟨hvs, q, hqr, e, he, rfl⟩ :=
    SA.optimisticPoint_pool_vote hr hx hpt' hv (not_not.mp hz)
  exact ⟨_, not_not.mp hz, q, hqr, e, (SA.upTo_voteAt.mp he).2,
    hvs.trans hsl, R, hU hR, hRr, hBR.mono hU⟩

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
