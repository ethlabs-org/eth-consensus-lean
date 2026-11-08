module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.TransferFirst
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.TransferLater

public section

/-! # Goldilocks under `Sleepy` with growing faults: extending the vote frontier

`votes_below_succ_at`: `P_{s+1}` and `V_s` up to `b` give `V_{s+1}` up to `b`, by strong induction
on the cut of a slot-`(s+1)` vote of a node honest at it (the first bad vote), with the first and
later transfer steps. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **Extending the vote frontier under growing faults**: the first slot-`(s+1)` vote (of a node
honest at it) at a time `≤ b` that fails to extend an origin within `b` of label `j ≤ s` does not
exist. For `j < s` the later step applies, with `V_s` for every slot-`s` vote (cast before the
vote's cut); for `j = s` the first step; both with the earlier slot-`(s+1)` votes from the
induction on the cut. -/
theorem votes_below_succ_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b)
    (hV : VotesBelowUpTo tr H s b) : VotesBelowUpTo tr H (s + 1) b := by
  have key : ∀ i, ∀ y e, HVoteAt tr H y i e → tr.time i ≤ b → e.msg.slot = s + 1 →
      ∀ C j, OriginWithin tr H C j b → j ≤ s →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg C := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro y e hv hib hs C j hC hj
      obtain ⟨hy, ℓ, hc⟩ := hVoteAt_iff.1 hv
      have hE : SA.EarlierVotesExtendAt tr.projAC H (tr.HonestBlocksAt H) i (s + 1) C :=
        fun x k hk hx e' hv' hs' => ih k hk x e' (hVoteAt_iff.2 ⟨hx, hv'⟩)
          ((hrun.time_mono hk.le).trans hib) hs' C j hC hj
      rcases hj.lt_or_eq with hj | rfl
      · have hti : sp.ts ((s + 1 : Nat) : Int) ≤ tr.time i := by
          have h := (castAt_spec_at hrun hnc hy ⟨hc.1, hc.2⟩).2.1
          rw [hs] at h
          change s + 1 = sp.slot (tr.time i) at h
          exact (SA.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).2 (by exact_mod_cast h.le)
        have hCU : C ∈ tr.HonestBlocksAt H := by
          obtain ⟨x, k, CV, hx, -, hO⟩ := originWithin_iff.1 hC
          exact upTo_subset hrun (hrun.time_nonneg k)
            (origin_mem_upTo hrun hnc (hrun.time_nonneg k) hx le_rfl hO)
        exact later_transfer_step_at hrun hnc hb hsync hB hP hy hc hs hib hCU
          (fun C' j' hC' hj' => originsBelowUpTo_iff.1 hP C j C' j' (by omega) (by omega) hC hC')
          (fun x k e' hv' hs' => votesBelowUpTo_iff.1 hV C j hC x k e' hv'
            ((vote_cut_lt hrun hnc hv' hs' hti).1.le.trans (hti.trans hib)) (by omega) hs'.le)
          hE
      · exact first_transfer_step_at hrun hnc hb hsync hB hP hy hc hs hib hC hE
  refine votesBelowUpTo_iff.2 fun C j hC y i e hv hib hj hm => ?_
  rcases Nat.lt_or_ge e.msg.slot (s + 1) with h | h
  · exact votesBelowUpTo_iff.1 hV C j hC y i e hv hib hj (by omega)
  · exact key i y e hv hib (by omega) C j hC (by omega)

end Consensus.Goldilocks.Compose.Growing

end
