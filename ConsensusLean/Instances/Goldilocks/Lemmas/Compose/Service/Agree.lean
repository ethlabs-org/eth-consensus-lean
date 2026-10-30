module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch

public section

/-! # Goldilocks under `Sleepy`: the honest slot-`s` votes are the honest proposal (open)

workbench#12 (`sleepy-proposal-adoption.md`, f42c0ad) §2–§3, over the Sleepy invariant: for the
honest proposal `P` of slot `s` by a joined proposer, every honest slot-`s` vote is `P`. The
voter walks pass the pivot `D_s` (the deepest of genesis, the regular origins of labels at most
`s − 2` and the optimistic origins of labels at most `s − 1`) by S2 (`vote_extends`); the
proposal walk reaches it, and the later regular result of label `s − 1`, by the honest batch
(§2.1, §2.2; `vote_extends_of_batch` is the voter-side analogue); on the suffix from `D_s` the
proposal view (`P`'s payload) and each voter's merged view have the same participants,
equivocators and support, so both walks follow the same path to `P.parent`, where `P` is the only
eligible child (§3). The honest slot-`s` batch then reaches the joined updater of slot `s`,
resolved before `t_s + 2Δ` (§4, `honest_batch_at_update` in `Service/Batch`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **Every honest slot-`s` vote is the honest proposal `P` of slot `s`** (workbench#12 §2–§3;
open). -/
theorem honest_votes_eq_proposal {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) :
    ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s → e.msg.head = P.root := by
  sorry

end Consensus.Goldilocks.Compose

end
