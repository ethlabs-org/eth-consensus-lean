module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Pivot
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ViewAgree
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkEnd
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: the honest proposal and its payload

The run facts the suffix lemmas share with their callers: an honest node accepts its own proposal
(`proposal_accepted`), the honest proposal is the only honest block of its slot (`eq_of_slot`), and
the payload of a proposal is the proposer's view of the previous slot's pool (`payload_eq`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}

section Run

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time}

/-- **An honest node accepts its own proposal** (C0.3, under `NoColl`). -/
theorem proposal_accepted (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt p k P) : tr.AcceptAt p k P := by
  have h := hrun.toLocalRun
  obtain ⟨⟨⟨acc, hcall⟩, hpos⟩, -, -⟩ := hP
  rcases blockCall_cases h hp hcall with hg | ⟨j, x, rfl, hg, hpr, d, pay, hdp, hB, hacc, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  obtain ⟨cfg, hreach, hst, hstep⟩ := group_step h hp hg
  have hC03 := honest_block_accepted proposer dg p (requirements sp ro) hrun.genesis_root_ok cfg _
    (tr.time (j + 2)) x hreach hstep hpr d pay (by rw [hst]; exact hdp)
  simp only [hst] at hC03
  have key : NoCollOn dg (insert P (tr.state p j).fg.tree) →
      (tr.state p j).fg.blocks P.root = none ∧ ∃ fg', (tr.state p j).fg.onBlock P = some fg' := by
    rw [hB]
    exact hC03.2.2.2.2.2.2
  obtain ⟨-, fg', hon⟩ := key <| hnc.mono <| Set.insert_subset_iff.2
    ⟨Or.inr ⟨p, j + 2, acc, hcall⟩, tree_subset_run h hp j⟩
  obtain rfl : acc = true := hacc.2 ⟨fg', hon⟩
  exact hcall
/-- **The honest proposal is the only honest block of its slot.** -/
theorem eq_of_slot (hrun : GoldilocksRun proposer dg H tr)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : tr.ProposesAt p k P)
    {R : SA.Blk sp.n (List (FG.Att sp.n))} (hR : R ∈ tr.HonestBlocks H) (hRs : R.slot = P.slot) :
    R = P := by
  have h := hrun.toLocalRun
  obtain ⟨⟨⟨acc, hcB⟩, hpos⟩, hpp, htk⟩ := hP
  rcases blockCall_cases h hp hcB with hg | ⟨j, x, rfl, hg, hPr, d, pay, -, hB, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  have hpr : P.proposer = proposer P.slot := by
    rw [hpp, hB]
    exact hPr.2.2.symm
  have hs0 : 0 < P.slot := by rw [hB]; exact hPr.1
  obtain ⟨y, hy, i, hRt⟩ := hR
  rcases tree_cases h hy hRt with rfl | ⟨k', -, hk'⟩
  · simp [Params.genesisBlock] at hRs
    omega
  obtain ⟨-, hRpr, -⟩ := accept_facts h hy hk'
  have hRp : R.proposer = p := by rw [hRpr, hRs, ← hpr, hpp]
  obtain ⟨j', -, ⟨acc', hc'⟩, hpos'⟩ := hrun.block_unforgeable y hy k' R ⟨true, hk'⟩ (hRp ▸ hp)
  rw [hRp] at hc'
  rcases blockCall_cases h hp hc' with hg' | ⟨j₀, x', rfl, hg', hPr', d₀, pay₀, -, hB', -⟩
  · exact absurd (by simpa using (hg'.2.1 0 (List.length_pos_iff.2 hg'.1)).2.2.2.1) hpos'
  have ht' : tr.time (j₀ + 2) = sp.toParams.slotTime R.slot := by
    have hs : R.slot = sp.toParams.slotOf (tr.time (j₀ + 2)) := by rw [hB']; rfl
    exact hs ▸ hPr'.2.1
  have htt : tr.time (j₀ + 2) = tr.time (j + 2) := by rw [ht', htk, hRs]
  rw [htt] at hg'
  obtain rfl := hrun.tick_unique p hp j₀ j _ ⟨x', hg'⟩ ⟨x, hg⟩
  have := hc'.2.symm.trans hcB.2
  simp only [Option.some.injEq, Cut.fg.injEq, FGLabel.block.injEq] at this
  exact this.1
end Run

section Proposal

/-- The payload of a proposal is the proposer's view of the previous slot's pool. -/
theorem payload_eq {A : SA.SAState sp.n} {Φ : SA.Frm sp.n (List (FG.Att sp.n))}
    {t : Time} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (h : (SA.acProposal sp A Φ t).2 = some (d, pay)) :
    pay = SA.voteViewList A Φ ((sp.slot t : Int) - 1) ⊤ := by
  unfold SA.acProposal at h
  split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact h.2.symm
end Proposal

end Consensus.Goldilocks.Compose

end
