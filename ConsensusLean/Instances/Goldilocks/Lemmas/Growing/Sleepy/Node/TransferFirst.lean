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
within `b` of label `s`, compatible with every member of the healed family of label at most `s`,
that the earlier slot-`(s+1)` votes of nodes honest at them extend, is extended by the vote. The
frozen witness at the vote (S3) is a premise, supplied from the origin's honest supporter
(`vote_frame_at` from genesis); the live locks compare through their writes
(`vote_locks_compatible_at`); a result or an optimistic selection transfers, counted at the
voter's cut. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **First transfer under growing faults**: an origin `C` within `b` of label `s ≥ σ₀` (its
slot count and service available) has a supporter (`honest_supporter_at`), so it is in the vote's
viable voter tree or below `fc_root` (`hframe`); below `fc_root` the vote extends `C`, otherwise a
result transfers (the writer honest at its update, the voter at its vote) and an optimistic
selection transfers with `2 f_{t_i} < n` counted at the voter's cut. -/
theorem first_transfer_step_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b) {σ₀ : Nat}
    (hB : SleepyBoundsFrom tr H σ₀ b) {g : Time} {rL rO s : Nat} (hs₀ : σ₀ ≤ s)
    (hsa : a + κ ≤ sp.ts s) {y : Fin sp.n}
    {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b)
    (hlive : ∀ l ∈ SA.liveLocks sp e.readPoint.locks ℓ.frame (tr.time i), l.slot ≤ s →
      rL ≤ l.slot)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hC : OriginWithin tr H C s b)
    (hCc : ∀ C' j, HealedOrigin tr H g rL rO C' j b → j ≤ s →
      Compatible (tr.HonestBlocksAt H) C C')
    (hframe : (∃ x k e', HVoteAt tr H x k e' ∧ e'.msg.slot = s ∧
        SA.VoteExtends (tr.HonestBlocksAt H) e'.msg C) →
      C ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
        Anc (tr.HonestBlocksAt H) C ℓ.frame.fcRoot)
    (hE : SA.EarlierVotesExtendAt tr.projAC H (tr.HonestBlocksAt H) i (s + 1) C) :
    SA.VoteExtends (tr.HonestBlocksAt H) e.msg C := by
  have hd := hrun.time_nonneg i
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hf := hB.two (tr.time i) hd hib
  have ha : a ≤ sp.ts s := (le_add_of_nonneg_right hsync.kappa).trans hsa
  obtain ⟨x', k', e', hv', -, hs', hext'⟩ := honest_supporter_at hrun hnc hsync hB hs₀ ha hC
  have hvf := hframe ⟨x', k', e', hv', hs', hext'⟩
  have hlocks := vote_locks_compatible_at hrun hnc hB hy hc hs hib hlive hCc hE
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hy hc.1
  rcases hvf with hv | hCf
  swap
  · obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, -⟩ := cast_head_fcRoot_at hrun hnc hy hc
    exact ⟨Hd, hΦU hHd, hHdr, hCf.trans (Anc.mono hΦU hfHd)⟩
  have hF : Anc (tr.HonestBlocksAt H) ℓ.frame.F C := Anc.mono hΦU (hΦ.rooted.2 C hv.1.1)
  obtain ⟨x, i₀, CV, hx, hi₀, hR | hO⟩ := originWithin_iff.1 hC
  · exact SA.Growing.result_transfer hrun' hx hR hy hc hs
      (result_carry_at hrun hnc hsync hsa hx hR hy hc hs hib hF) (Or.inl hv) hlocks
      (result_writer_pool_at hrun hnc hsync ha hx hR hi₀ hy hc hs)
  · exact SA.Growing.optimistic_transfer_stored hrun' hx hO .refl hf hy hc hs
      (optimistic_carry_at hrun hnc hsync hsa hx hO hy hc hs hib hF) (Or.inl hv) hE

end Consensus.Goldilocks.Compose.Growing

end
