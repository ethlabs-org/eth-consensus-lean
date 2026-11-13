module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC

public section

/-! # The votes of an own proposal are pooled before its block cut

In any Goldilocks run, the votes in the payload of an honest node's own proposal were in its pool
before its AC block cut: `own_proposal_payload_pooled_run`. It reads the node's tick, proposal
and block cuts and their cut laws only. Constant faults use it on the simulating trace
(`own_proposal_payload_pooled`), growing faults on the prefix through the proposal. -/

namespace Consensus.Goldilocks.Obligations.Growing

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Votes in an actual own-proposal payload were already pooled before its AC block cut. -/
theorem own_proposal_payload_pooled_run (hr : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {t : Time} {x : Nat}
    (hg : tr.GroupAt proposer dg y j t (.tick x))
    {d : DutyHead sp.n (List (FG.Att sp.n)) (SA.Payload sp.n)} {p : SA.Payload sp.n}
    (hd : (Node.acProposal
      (Node.tickStep proposer dg y (tr.state y j) t x .acTick).1 t).2.2 = some (d, p))
    (hprop : ∃ ℓp, tr.CallAt y (j + 1) (.ac ℓp) ∧ ℓp.call = .proposal)
    (hfg : ∃ B, tr.CallAt y (j + 2) (.fg (.block B true)))
    {m : SA.Vote sp.n} (hm : m ∈ p.1) :
    m ∈ (tr.state y (j + 3)).ac.pool m.slot := by
  have htick := hg.2.1 0 (by simp [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps,
    Node.tickStep, Node.acCall])
  have hct : tr.CallAt y j (Node.acCall y (tr.state y j) t .tick).2 := by
    exact ⟨by simpa using htick.1, by
      simpa [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps, Node.tickStep,
        Node.acCall] using htick.2.2.2.2⟩
  have hstate : (tr.state y (j + 1)).ac =
      (Node.tickStep proposer dg y (tr.state y j) t x .acTick).1.ac := by
    rw [tr.state_succ_of_call hct]
    have hl := hr.cutLaw y hy j _ hct
    have ht : tr.time j = t := by simpa using htick.2.1
    rw [ht] at hl
    exact (congrArg Prod.fst hl.2.1).symm
  have hp : ∃ σ, m ∈ (tr.state y (j + 1)).ac.pool σ := by
    rw [hstate]
    change (SA.acProposal sp _ _ t).2 = some (d, p) at hd
    unfold SA.acProposal at hd
    split_ifs at hd
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj hd)
    simp only [SA.voteViewList, List.mem_filter] at hm
    unfold SA.SAState.poolAt at hm
    split_ifs at hm
    · simp at hm
    · exact ⟨_, hm.1⟩
  obtain ⟨σ, hm⟩ := hp
  have hslot := (Compose.state_pool_cap hr (fun _ _ => rfl) hy (j + 1) σ).1 m
    (by simpa only [Compose.projAC_state hr.toLocalRun hy] using hm)
  obtain ⟨ℓp, hcp, hpc⟩ := hprop
  obtain ⟨B, hcb⟩ := hfg
  have hp := (hr.cutLaw y hy (j + 1) _ hcp).2.1
  rw [hpc] at hp
  have hpools : (tr.state y (j + 2)).ac.pool = (tr.state y (j + 1)).ac.pool := by
    have he := congrArg Prod.fst hp
    dsimp only [Prod.fst] at he
    rw [show j + 2 = (j + 1) + 1 by omega, tr.state_succ_of_call hcp, ← he]
    change (SA.acProposal _ _ _ _).1.pool = _
    unfold SA.acProposal
    split_ifs <;> rfl
  rw [show j + 3 = (j + 2) + 1 by omega, tr.state_succ_of_call hcb,
    (hr.cutLaw y hy (j + 2) _ hcb).2.2.1, hpools, hslot]
  exact hm

end Consensus.Goldilocks.Obligations.Growing

end
