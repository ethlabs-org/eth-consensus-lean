module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockKeepInterval
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.OpponentsHonest
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace

public section

/-! # Goldilocks: a lock kept over an interval of cuts against honest votes

consensus-lean#135 (WI-15/16). `heldVotes_honest_unique`: at an AC cut `j` of an honest node `y`,
two votes held across the cut (`SA.heldVotes`) of one honest validator and one slot are equal
(each was emitted by its validator, `one_vote_per_slot`). With the fault bound `2 · |Hᶜ| < n`
this keeps the unlock target (`SA.unlockTarget_unlockView_held_of_honest_slot`). It assumes
`NoCollRun`, for the AC projection of the run (`goldilocks_ac_projection`). -/

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

end Consensus.Goldilocks.Compose

end
