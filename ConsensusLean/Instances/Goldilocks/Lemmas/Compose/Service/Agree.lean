module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.SuffixBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ViewAgree
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkEnd
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.StopCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.VoterWalk
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.ProposalTick

public section

/-! # Goldilocks under `Sleepy`: the run's proposal data

`proposal_data`: the run's proposal of an honest block `P` of slot `s` by a joined proposer is
`ac_proposal`'s, at `t_s`, on the duty head `Q = P.parent`, with payload `pay`. -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n}

/-- **The run's proposal of `P` is `ac_proposal`'s** at `t_s`: on the duty head `Q = P.parent`,
with the payload `pay`. An own block is processed inside a tick (position `≠ 0`), so it is the
proposal step's (`blockCall_cases`), made by `Node.proposeBlock` from `ac_proposal`'s duty head and
payload at the cut after the tick's `ac_on_tick`. -/
theorem proposal_data {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp} {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) :
    ∃ i ℓp d pay, tr.projAC.CallAt p i ℓp ∧ ℓp.call = .proposal ∧
      (AC.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay) ∧
      tr.time i = sp.ts s ∧ P.parent = some d.head.root ∧ P.acPayload = pay := by
  have h := hrun.toLocalRun
  obtain ⟨⟨⟨acc, hcB⟩, hpos⟩, -, htk⟩ := hP
  rcases blockCall_cases h hp hcB with hg | ⟨j, x, fgDue, rfl, hg, hPr, d, pay, hr, hB, -, -, -, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  exact proposal_data_of_tick hg hPr hr hB (by rw [htk, sp.slotTime_eq, hPs]; rfl)
    (hrun.cutLaw p hp j) (projAC_state h hp (j + 1))

end Consensus.Goldilocks.Compose

end
