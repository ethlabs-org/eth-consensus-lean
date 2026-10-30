module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch

public section

/-! # Goldilocks under `Sleepy`: the suffix of the proposal walk (open)

workbench#12 §3: on the proposal walk from the pivot `D` to `Q = P.parent`, at every block at or
above a voter's anchor, the proposer's best child is the voter's best child. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **The suffix** (workbench#12 §3; open): at every block `X` from the pivot `D` to `Q` (in the
proposer's tree) at or above the voter's anchor, the proposer's best child is the voter's best
child. Only the winner is compared: in reachable runs (sa-fg-model 7f7e660) a voter-eligible
competitor need not be proposer-eligible (the frame moves between the proposal read and the vote,
e.g. `Σ.F` rises to `X` when the node accepts `P`, and every child of `X` becomes eligible), and
competitor scores differ between the views; below the voter's anchor the proposer's best child can
be outside the voter's viable tree. The model finds the voter's winner score strictly above every
competitor's in all of these cases. -/
theorem suffix_agree {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root)
    {D : SA.Blk sp.n (List (FG.Att sp.n))} (hsD : ℓp.frame.Anc d.start D)
    (hDQ : ℓp.frame.Anc D d.head)
    (hviab : ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s) :
    ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head →
      Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X →
      X ≠ d.head →
      ∀ C, SA.IsBest sp (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
          {B | B ∈ ℓp.frame.viableTree ℓp.frame.tree ∧ B.parent = some X.root ∧
            SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay)
              ((s : Int) - 1) B} C →
        SA.IsBest sp (SA.goldfishScore sp ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s)
            ((s : Int) - 1))
          {B | B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) ∧
            B.parent = some X.root ∧ SA.goldfishEligible sp ℓy.frame (tr.time j)
              (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B} C := by
  sorry

end Consensus.Goldilocks.Compose

end
