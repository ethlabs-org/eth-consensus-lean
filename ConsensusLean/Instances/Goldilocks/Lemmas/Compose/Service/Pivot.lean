module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch

public section

/-! # Goldilocks under `Sleepy`: the pivot of an honest proposal (open)

workbench#12 §2.1, §2.2: for the honest proposal `P` of slot `s`, made from `ac_proposal`'s duty
head `Q = P.parent`, a block `D` on the proposal walk (between its start and `Q`) such that every
honest slot-`s` voter's walk passes a block `X` of the path from `D` through `Q` to `P`: `X` is
`P`, or between `D` and `Q` in the proposer's tree. `D` is the deepest of genesis, the regular
origins of labels at most `s − 2` and the optimistic origins of labels at most `s − 1`; a voter
whose anchor is at or below `D` passes `D` (S2 for regular origins, the three-quarter count for an
optimistic origin of label `s − 1`); a voter whose anchor is a current-slot optimistic lock is on
`P`'s chain above `D` (the first vote not `P`), and passes its anchor. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **The pivot** (workbench#12 §2.1, §2.2; open). -/
theorem pivot {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root) :
    ∃ D, ℓp.frame.Anc d.start D ∧ ℓp.frame.Anc D d.head ∧
      ∀ y ∈ H, ∀ j ℓy e, SA.CastAt tr.projAC y j ℓy e → e.msg.slot = s →
        ∃ X, (X = P ∨ (ℓp.frame.Anc D X ∧ ℓp.frame.Anc X d.head)) ∧
          ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X ∧
          ℓy.frame.Anc X (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
            (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s))
            (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)) := by
  sorry

end Consensus.Goldilocks.Compose

end
