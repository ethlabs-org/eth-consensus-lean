module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Components

public section

/-! # Goldilocks: a block proposed in a tick is `ac_proposal`'s

`proposal_data_of_tick`: when node `p`'s tick at `t_s` proposes (`Node.Proposes`), `ac_proposal`
after the tick's `ac_on_tick` returns `(d, pay)` and `P` is the block `propose_block` makes from
them, the AC cut after the tick's first is a proposal call of `p` at `t_s` returning `(d, pay)`,
with `P.parent = d.head` and `P.acPayload = pay`. It reads the tick's group, the cut law at its
first cut and the AC projection's state after it; the run supplies these for an honest proposer
(`Service/Agree`'s `proposal_data`, `Service/SuffixWindow`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {tr : GoldilocksTrace sp ro}

/-- **A block proposed in a tick is `ac_proposal`'s** at `t_s`: from `p`'s tick group at `j` (at
the time `t_s` of cut `j + 2`) whose proposal step proposes `P`, made from the duty head `d.head`
and payload `pay` of `ac_proposal` after `ac_on_tick`, given the cut law of `p`'s cut `j` and the
AC projection's state of `p` at `j + 1`. -/
theorem proposal_data_of_tick {p : Fin sp.n} {j x s : Nat}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hg : tr.GroupAt proposer dg p j (tr.time (j + 2)) (.tick x))
    (hPr : Node.Proposes proposer p (tr.time (j + 2)))
    (hr : (Node.acProposal (Node.tickStep proposer dg p (tr.state p j) (tr.time (j + 2)) x
      .acTick).1 (tr.time (j + 2))).2.2 = some (d, pay))
    (hB : P = Node.mkBlock dg p (tr.state p j).fg (tr.time (j + 2)) x d.head pay)
    (hts : tr.time (j + 2) = sp.ts s)
    (hcut : ∀ c, tr.CallAt p j c → Node.CutStep p (tr.time j) (tr.state p j) c (tr.post j))
    (hproj : tr.projAC.state p (j + 1) = (tr.state p (j + 1)).ac) :
    ∃ i ℓp d pay, tr.projAC.CallAt p i ℓp ∧ ℓp.call = .proposal ∧
      (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay) ∧
      tr.time i = sp.ts s ∧ P.parent = some d.head.root ∧ P.acPayload = pay := by
  set t := tr.time (j + 2)
  set st := tr.state p j
  set st1 := (Node.tickStep proposer dg p st t x .acTick).1
  have hcuts : (Node.exec proposer dg p st t (.tick x)).2 =
      (Node.tickStep proposer dg p st t x .acTick).2 ++
      (Node.tickStep proposer dg p st1 t x .proposal).2 ++
      (Node.tickStep proposer dg p
        (Node.tickStep proposer dg p st1 t x .proposal).1 t x .fgUpdate).2 := by
    simp [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps, st1]
  have h0 : (Node.exec proposer dg p st t (.tick x)).2[0]? = some (Node.acCall p st t .tick).2 := by
    rw [hcuts]; simp [Node.tickStep]
  have h1 : (Node.exec proposer dg p st t (.tick x)).2[1]? = some (Node.acProposal st1 t).2.1 := by
    rw [hcuts]
    simp only [Node.tickStep, hPr, ↓reduceIte]
    split <;> simp [Node.acProposal, Node.acCall]
  obtain ⟨hk0, hc0⟩ := List.getElem?_eq_some_iff.1 h0
  obtain ⟨hk1, hc1⟩ := List.getElem?_eq_some_iff.1 h1
  obtain ⟨hn0, ht0, -, -, hl0⟩ := hg.2.1 0 hk0
  obtain ⟨hn1, ht1, -, -, hl1⟩ := hg.2.1 1 hk1
  rw [hc0] at hl0
  rw [hc1] at hl1
  simp only [Nat.add_zero] at hn0 ht0 hl0
  have hcall0 : tr.CallAt p j (Node.acCall p st t .tick).2 := ⟨hn0, hl0⟩
  have hst1 : (tr.state p (j + 1)).ac = st1.ac := by
    rw [tr.state_succ_of_call hcall0]
    obtain ⟨-, hstep, -, -⟩ := hcut _ hcall0
    rw [ht0] at hstep
    exact (congrArg Prod.fst hstep).symm
  refine ⟨j + 1, ⟨.proposal, Node.frame st1, []⟩, d, pay, projAC_callAt.2 ⟨hn1, hl1⟩, rfl, ?_,
    ht1.trans hts, by rw [hB]; rfl, by rw [hB]; rfl⟩
  rw [hproj, hst1, show tr.time (j + 1) = t from ht1]
  exact hr

end Consensus.Goldilocks.Compose

end
