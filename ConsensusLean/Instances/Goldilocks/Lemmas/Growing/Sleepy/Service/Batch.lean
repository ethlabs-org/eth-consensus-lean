module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch

public section

/-! # Goldilocks under `Sleepy` with growing faults: the honest batch at an update

The growing-fault form of `Compose/Service/Batch`, at the update of slot `s` (at `t_s + 6Δ`) of a
node honest then. Both lemmas are the static ones on the prefix through the update; the batch is
the slot-`s` votes of the validators honest at their vote and still honest at the update (the
voters `VotersAt s (t_s + 6Δ)` of the update's count):

* `update_restarts_at`: the updater's restarts up to its update are at or before `t_s`;
* `honest_batch_at_update_at`: when every honest slot-`s` vote names a block `P` of the update's
  frame, each such vote is in the updater's pool, resolved before `t_s + 2Δ`. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- The restarts of a node honest at its update of slot `s` (joined), up to the update, are at or
before `t_s`. -/
theorem update_restarts_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {k₀ s : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hy : y ∈ H (tr.time k₀)) (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) :
    ∀ k ≤ k₀, tr.projAC.RestartAt y k → tr.time k ≤ sp.ts s := by
  intro k hk hrk
  have hd := hrun.time_nonneg k₀
  exact Compose.update_restarts (acRun_upTo hrun hnc hd).localRun hy
    ((sa_updateAt_upTo hrun.time_mono).2 ⟨le_rfl, hu⟩) k hk
    ((ac_restartAt_upTo tr.projAC).2 ⟨hrun.time_mono hk, hrk⟩)

/-- **The honest batch at an update**: at the update of slot `s` of a node honest then, through
`b`, when every slot-`s` vote of a node honest at its vote names `P ∈ Φ`, every such vote of a
validator still honest at the update is in the updater's pool, resolved before `t_s + 2Δ`. -/
theorem honest_batch_at_update_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b) {y : Fin sp.n}
    {k₀ s : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} (hy : y ∈ H (tr.time k₀))
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) (hb : tr.time k₀ ≤ b)
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hPt : P ∈ ℓ.frame.tree)
    (hall : ∀ x j e, HVoteAt tr H x j e → e.msg.slot = s → e.msg.head = P.root) :
    ∀ x j e, HVoteAt tr H x j e → x ∈ H (tr.time k₀) → e.msg.slot = s →
      e.msg ∈ (tr.projAC.state y k₀).pool s ∧
        SA.resolutionTime (tr.projAC.state y k₀) ℓ.frame e.msg <
          SA.ETime.of (sp.ts s + 2 * sp.Δ) := by
  intro x j e hv hxd hes
  have hΔ := sp.toParams.hΔ
  have hd := hrun.time_nonneg k₀
  have ht : tr.time k₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
  obtain ⟨hx, ℓx, hcx, hex⟩ := hVoteAt_iff.1 hv
  have hjt : tr.time j ≤ tr.time k₀ := by
    have h := (cast_head_fcRoot_at hrun hnc hx ⟨hcx, hex⟩).2
    rw [hes] at h
    linarith
  have hsvc := (SleepyServiceBefore.upTo hrun hsync hd).ac
  have hu' : SA.UpdateAt (tr.upTo (tr.time k₀)).projAC y k₀ s ℓ := by
    rw [RunTrace.upTo_projAC]
    exact (sa_updateAt_upTo hrun.time_mono).2 ⟨le_rfl, hu⟩
  have hall' : ∀ x ∈ H (tr.time k₀), ∀ j e, SA.VoteAt (tr.upTo (tr.time k₀)).projAC x j e →
      e.msg.slot = s → e.msg.head = P.root := by
    intro x hx j e hv hs
    rw [RunTrace.upTo_projAC] at hv
    obtain ⟨hjd, hv⟩ := sa_voteAt_upTo.1 hv
    exact hall x j e (hVoteAt_iff.2 ⟨hrun.antitone hjd hx, hv⟩) hs
  have hv' : SA.VoteAt (tr.upTo (tr.time k₀)).projAC x j e := by
    rw [RunTrace.upTo_projAC]
    exact sa_voteAt_upTo.2 ⟨hjt, ℓx, hcx, hex⟩
  have h := Compose.honest_batch_at_update_before (hrun.upTo hd) (hnc.upTo _) hsvc hy hu'
    (le_min hb le_rfl) hPt hall' x hxd j e hv' hes
  rwa [RunTrace.upTo_projAC, projAC_upTo_state hrun le_rfl] at h

/-- **An honest vote at an update**: at the update of slot `s` of a node honest then, through `b`,
a slot-`s` vote of a node honest at its vote and still honest at the update, whose head `Q` (a
block held while honest) is above the update's `Σ.F`, is in the pool, resolved before
`t_s + 2Δ`, with `Q` in the frame (the static `honest_vote_at_update_before` on the prefix through
the update). -/
theorem honest_vote_at_update_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b) {y : Fin sp.n}
    {k₀ s : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} (hy : y ∈ H (tr.time k₀))
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) (hb : tr.time k₀ ≤ b)
    {Q : SA.Blk sp.n (List (FG.Att sp.n))} (hQU : Q ∈ tr.HonestBlocksAt H)
    (hFQ : Anc (tr.HonestBlocksAt H) ℓ.frame.F Q) {x : Fin sp.n} {j : Nat}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : HVoteAt tr H x j e) (hxd : x ∈ H (tr.time k₀))
    (hes : e.msg.slot = s) (hhead : e.msg.head = Q.root) :
    Q ∈ ℓ.frame.tree ∧ e.msg ∈ (tr.projAC.state y k₀).pool s ∧
      SA.resolutionTime (tr.projAC.state y k₀) ℓ.frame e.msg <
        SA.ETime.of (sp.ts s + 2 * sp.Δ) := by
  have hΔ := sp.toParams.hΔ
  have hd := hrun.time_nonneg k₀
  have ht : tr.time k₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
  have hU := honestBlocksAt_coherent hrun hnc
  obtain ⟨hx, ℓx, hcx, hex⟩ := hVoteAt_iff.1 hv
  obtain ⟨⟨Hd, hHd, hHdr, -⟩, htj⟩ := cast_head_fcRoot_at hrun hnc hx ⟨hcx, hex⟩
  have hjt : tr.time j ≤ tr.time k₀ := by rw [hes] at htj; linarith
  -- the head is in the voter's tree at its vote, so a block of the prefix's honest blocks
  have hHdQ : Hd = Q := hU.1 ((frameIn_at hrun hnc hx hcx).2 hHd) hQU (hHdr.trans hhead)
  have hQU' : Q ∈ (tr.upTo (tr.time k₀)).HonestBlocks (H (tr.time k₀)) := by
    refine ⟨x, hxd, j, ?_⟩
    rw [Trace.upTo_state tr x fun k hk => (hrun.time_mono hk.le).trans hjt]
    rw [frame_of_projAC_at hrun hx hcx] at hHd
    exact hHdQ ▸ hHd.1
  have hFQ' := RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hQU' hFQ
  have hsvc := (SleepyServiceBefore.upTo hrun hsync hd).ac
  rw [RunTrace.upTo_projAC] at hsvc
  have h := Compose.honest_vote_at_update_before (acRun_upTo hrun hnc hd) hsvc (le_min hb le_rfl)
    hy ((sa_updateAt_upTo hrun.time_mono).2 ⟨le_rfl, hu⟩) hQU' hFQ' hxd
    (sa_voteAt_upTo.2 ⟨hjt, ℓx, hcx, hex⟩) hes hhead
  rwa [projAC_upTo_state hrun le_rfl] at h

end Consensus.Goldilocks.Compose.Growing

end
