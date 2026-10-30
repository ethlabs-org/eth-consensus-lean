module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ViewAgree
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC

public section

/-! # Goldilocks under `Sleepy`: the proposal's view and a voter's merged view agree (open)

workbench#12 §3, first paragraph: for the honest proposal `P` of slot `s` (made from
`ac_proposal`'s duty head `Q = P.parent` and payload `pay`) and an honest voter of slot `s`, the
proposal's view and the voter's merged view have the same equivocators and voters, and the same
supporters for every block of both trees (`view_agree`, with the Sleepy relay: a block the voter
stamped before the vote freeze reaches the proposer by `t_s`, and `P`'s support heads reach the
voter by its vote); and `Q` is below slot `s`. Used by `suffix_agree` (`Service/Suffix`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
  (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
  {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
  (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
  {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
  {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
  (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
  (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root)
  {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
  {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
  (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s)

include hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ hy hcy hes

/-- **The views agree**: the proposal's view and the voter's merged view have the same
equivocators and voters, and the same supporters for every block of both trees. -/
theorem proposal_views_agree :
    SA.equivocators (SA.View.ofLists pay).votes =
        SA.equivocators (SA.mergedVoteView sp e.readPoint ℓy.frame s).votes ∧
      SA.voters (SA.View.ofLists pay).votes =
        SA.voters (SA.mergedVoteView sp e.readPoint ℓy.frame s).votes ∧
      ∀ X ∈ ℓp.frame.tree, X ∈ ℓy.frame.tree →
        SA.supporters ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1) X =
          SA.supporters ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)
            X := by
  sorry

omit hy hcy hes in
/-- The duty head of the proposal is below slot `s` (`P`, of slot `s`, is its child). -/
theorem proposal_head_slot_lt : d.head.slot < s := by
  sorry

end Consensus.Goldilocks.Compose

end
