module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.TransferLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.VoteFrame
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Optimistic
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC

public section

/-! # Goldilocks under `Sleepy` with growing faults: the first transfer step

`first_transfer_step_at`: at a slot-`(s+1)` vote of a node honest at its cut `i ≤ b`, an origin
within `b` of label `s` that the earlier slot-`(s+1)` votes of nodes honest at them extend is
extended by the vote (`vote_frame_at`, `vote_locks_compatible_at`, and the transfer of a result or
an optimistic selection, counted at the voter's cut). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **First transfer under growing faults**: an origin `C` within `b` of label `s` has a supporter
(`honest_supporter_at`), so it is in the vote's viable voter tree or below `fc_root`
(`vote_frame_at`); below `fc_root` the vote extends `C`, otherwise a result transfers (the writer
honest at its update, the voter at its vote) and an optimistic selection transfers with
`2 f_{t_i} < n` counted at the voter's cut. -/
theorem first_transfer_step_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBounds tr H b) {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b) {y : Fin sp.n}
    {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) {C : SA.Blk sp.n (List (FG.Att sp.n))} (hC : OriginWithin tr H C s b)
    (hE : SA.EarlierVotesExtendAt tr.projAC H (tr.HonestBlocksAt H) i (s + 1) C) :
    SA.VoteExtends (tr.HonestBlocksAt H) e.msg C := by
  have hd := hrun.time_nonneg i
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hf := hB.two (tr.time i) hd hib
  have hCU : C ∈ tr.HonestBlocksAt H := by
    obtain ⟨x, k, CV, hx, -, hO⟩ := originWithin_iff.1 hC
    exact upTo_subset hrun (hrun.time_nonneg k)
      (origin_mem_upTo hrun hnc (hrun.time_nonneg k) hx le_rfl hO)
  have hCc : ∀ C' j, OriginWithin tr H C' j b → j ≤ s → Compatible (tr.HonestBlocksAt H) C C' :=
    fun C' j hC' hj => originsBelowUpTo_iff.1 hP C s C' j (by omega) (by omega) hC hC'
  obtain ⟨x', k', e', hv', -, hs', hext'⟩ := honest_supporter_at hrun hnc hsync hB hC
  have hvf := vote_frame_at hrun hnc hb hsync hB hP hy hc hs hib hCU hCc
    ⟨x', k', e', hv', hs', hext'⟩
  have hlocks := vote_locks_compatible_at hrun hnc hB hy hc hs hib hCc hE
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hy hc.1
  rcases hvf with hv | hCf
  swap
  · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := cast_head_fcRoot_at hrun hnc hy hc
    exact ⟨Hd, hΦU hHd, hHdr, hCf.trans (Anc.mono hΦU hfHd)⟩
  have hF : Anc (tr.HonestBlocksAt H) ℓ.frame.F C := Anc.mono hΦU (hΦ.rooted.2 C hv.1.1)
  obtain ⟨x, i₀, CV, hx, hi₀, hR | hO⟩ := originWithin_iff.1 hC
  · exact SA.Growing.result_transfer hrun' hx hR hy hc hs
      (result_carry_at hrun hnc hsync hx hR hy hc hs hib hF) (Or.inl hv) hlocks
      (result_writer_pool_at hrun hnc hsync hx hR hi₀ hy hc hs)
  · exact SA.Growing.optimistic_transfer_stored hrun' hx hO .refl hf hy hc hs
      (optimistic_carry_at hrun hnc hsync hx hO hy hc hs hib hF) (Or.inl hv) hE

end Consensus.Goldilocks.Compose.Growing

end
