module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockKeepInterval
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.OpponentsHonest
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace

public section

/-! # Goldilocks: a lock kept over an interval of cuts against honest votes

consensus-lean#135 (WI-15/16). `heldVotes_honest_unique`: at an AC cut `j` of an honest node `y`,
two votes held across the cut (`SA.heldVotes`) of one honest validator and one slot are equal
(each was emitted by its validator, `one_vote_per_slot`). `lock_keep_interval_cases_honest`:
`lock_keep_interval_cases_held` with the opponent premise at each cut replaced by the
compatibility of the honest held votes of slot `slot(t_j) − 1` with `B` and the fault bound
`2 · |Hᶜ| < n` (`SA.unlockTarget_unlockView_held_of_honest_slot`). Both assume `NoCollRun`, for
the AC projection of the run (`goldilocks_ac_projection`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **Honest held votes do not equivocate per slot.** At an AC cut `j` of an honest node `y`, two
votes of the same honest validator and the same slot among the votes held across the cut are
equal. -/
theorem heldVotes_honest_unique (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.CallAt y j (.ac ℓ)) {x x' : Vote sp.n}
    (hx : x ∈ SA.heldVotes (tr.state y j).ac (tr.state y (j + 1)).ac (Node.frame (tr.state y j)))
    (hx' : x' ∈
      SA.heldVotes (tr.state y j).ac (tr.state y (j + 1)).ac (Node.frame (tr.state y j)))
    (hxH : x.val ∈ H) (hval : x'.val = x.val) (hs : x.slot = x'.slot) : x = x' := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hcA : tr.projAC.CallAt y j ℓ := projAC_callAt.2 hc
  have hfr : ℓ.frame = Node.frame (tr.state y j) := (hrun.cutLaw y hy j _ hc).1
  have hem : ∀ v ∈ SA.heldVotes (tr.state y j).ac (tr.state y (j + 1)).ac
      (Node.frame (tr.state y j)), v.val ∈ H →
      ∃ k e, SA.VoteAt tr.projAC v.val k e ∧ e.msg = v := by
    intro v hv hvH
    rcases SA.mem_heldVotes.1 hv with ⟨τ, hv⟩ | ⟨τ, hv⟩ | ⟨C, hC, hv⟩
    · rw [← projAC_state hrun.toLocalRun hy] at hv
      obtain ⟨k, -, e, he, hm⟩ := hrun'.honest.pool_vote y hy j τ v hv hvH
      exact ⟨k, e, he, hm⟩
    · rw [← projAC_state hrun.toLocalRun hy] at hv
      obtain ⟨k, -, e, he, hm⟩ := hrun'.honest.pool_vote y hy (j + 1) τ v hv hvH
      exact ⟨k, e, he, hm⟩
    · rw [← hfr] at hC
      have hvB : v ∈ SA.blockVotes C :=
        hv.elim id fun h => (SA.frame_validPayload sp hr hy hcA C hC).2 v h
      obtain ⟨k, -, e, he, hm⟩ := hrun'.honest.carried_vote y hy j ℓ hcA C hC v hvB hvH
      exact ⟨k, e, he, hm⟩
  obtain ⟨k, e, he, rfl⟩ := hem x hx hxH
  obtain ⟨k', e', he', rfl⟩ := hem x' hx' (hval ▸ hxH)
  rw [hval] at he'
  exact congrArg (fun e : SA.Em sp (List (FG.Att sp.n)) => e.msg)
    (SA.one_vote_per_slot sp _ ro H _ _ hr _ hxH k k' e e' he he' hs).2

/-- **A lock kept over `[i, k]` against honest votes.** `lock_keep_interval_cases_held` with
the opponent premise at each cut `j` replaced by: every held vote of slot `slot(t_j) − 1` of an
honest validator has only heads (in the frame's tree) compatible with `B`; and
`2 · |Hᶜ| < n`. -/
theorem lock_keep_interval_cases_honest (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) {i k : Nat} (hik : i ≤ k)
    {l : SA.Lock} (hl : l ∈ (tr.state y i).ac.locks)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBr : B.root = l.block)
    (hf : 2 * Hᶜ.ncard < sp.n)
    (hstep : ∀ j, i ≤ j → j < k → sp.slot (tr.time j) ≤ l.slot + sp.k ∧
      B ∈ (tr.state y j).fg.toFrame.tree ∧
      (((tr.state y j).fg.Contest ∧ ∃ Y ∈ (tr.state y j).fg.tree,
        (tr.state y j).fg.Anc (tr.state y j).fg.F Y ∧
        (tr.state y j).fg.hmax ≤ ((tr.state y j).fg.σ Y.root).h ∧
        (tr.state y j).fg.toFrame.Anc B Y) ∨
      ((tr.state y j).fg.hmax = (tr.state y j).fg.hj + 1 ∧ ¬ (tr.state y j).fg.Contest ∧
        (tr.state y j).fg.Anc (tr.state y j).fg.F (tr.state y j).fg.J ∧
        (tr.state y j).fg.Anc (tr.state y j).fg.J B ∧ ∃ Y ∈ (tr.state y j).fg.tree,
        (tr.state y j).fg.Anc (tr.state y j).fg.J Y ∧ (tr.state y j).fg.IsViable Y ∧
        (tr.state y j).fg.toFrame.Anc B Y) ∨
      ((tr.state y j).fg.hmax ≠ (tr.state y j).fg.hj + 1 ∧
        ∃ Y ∈ (tr.state y j).fg.toFrame.viableHeads, (tr.state y j).fg.toFrame.Anc B Y)) ∧
      ((sp.slot (tr.time j) : Int) - 1 ≤ l.slot ∨
        ∀ x ∈ SA.heldVotes (tr.state y j).ac (tr.state y (j + 1)).ac
          (Node.frame (tr.state y j)), x.val ∈ H →
          (x.slot : Int) = (sp.slot (tr.time j) : Int) - 1 →
          ∀ Hd ∈ (Node.frame (tr.state y j)).tree, Hd.root = x.head →
            Compatible (Node.frame (tr.state y j)).tree Hd B)) :
    l ∈ (tr.state y k).ac.locks :=
  lock_keep_interval_cases_view hrun hy hik hl hBr fun j h1 h2 => by
    obtain ⟨hk, hB, hc, hu⟩ := hstep j h1 h2
    refine ⟨hk, hB, hc, fun ℓ hcall => hu.imp_right fun hcompat => ?_⟩
    obtain ⟨hfr, hst, -, -⟩ := hrun.cutLaw y hy j _ hcall
    rw [hfr] at hst
    have hA' : ((SA.goldilocksSA sp (List (FG.Att sp.n)) ro).step y (tr.state y j).ac
        (Node.frame (tr.state y j)) (tr.time j) ℓ.call).1 = (tr.state y (j + 1)).ac := by
      rw [tr.state_succ_of_call hcall, hst]
    have hpool : ∀ m τ, ∀ v ∈ (tr.state y m).ac.pool τ, v.slot = τ := fun m τ v hv => by
      rw [← projAC_state hrun.toLocalRun hy] at hv
      exact (state_pool_cap hrun hy m τ).1 v hv
    have hpay : ∀ C ∈ (Node.frame (tr.state y j)).tree, SA.validPayload C := by
      have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
      rw [← hfr]
      exact SA.frame_validPayload sp hr hy (projAC_callAt.2 hcall)
    exact SA.unlockTarget_unlockView_held_of_honest_slot y ℓ.call hA'
      (frameOK_state hrun.toLocalRun hy j) _ hB (hpool j) (hpool (j + 1)) hpay
      (fun x hx x' hx' hxH hval hs => heldVotes_honest_unique hrun hnc hy hcall hx hx' hxH hval hs)
      hcompat hf

end Consensus.Goldilocks.Compose

end
