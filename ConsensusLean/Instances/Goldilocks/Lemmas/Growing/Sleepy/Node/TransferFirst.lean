module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.TransferLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.VoteFrame
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Run

public section

/-! # Goldilocks under `Sleepy` with growing faults: the first transfer step

`first_transfer_step_at`: at a slot-`(s+1)` vote of a node honest at its cut `i ≤ b`, an origin
within `b` of label `s` that the earlier slot-`(s+1)` votes of nodes honest at them extend is
extended by the vote (`vote_frame_at`, `vote_locks_compatible_at`, and the transfer of a result or
an optimistic selection, counted at the voter's cut).

The transfer and carry results it consumes from other layers are stated here, with their agreed
names (suffix `_stub`) and shapes, until those modules are on this branch:
`SA.Growing.result_transfer_stub`, `SA.Growing.optimistic_transfer_stored_stub` (the growing AC
transfers), `goldilocks_ac_projection_stub` (the growing AC projection), and
`result_carry_at_stub`, `optimistic_carry_at_stub`, `result_writer_pool_at_stub` (the node
transport). -/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {proposer : Nat → Fin sp.n}

/-- The growing result transfer (`SA.Growing.result_transfer`); stand-in. -/
theorem result_transfer_stub (hrun : ACRun proposer tr H U)
    {s : Nat} {X y : Fin sp.n} {i₀ i : Nat} {C : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hX : X ∈ H (tr.time i₀)) (hres : ResultAt tr X i₀ s C CV)
    (hy : y ∈ H (tr.time i)) (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hcarry : CarryAt tr U y i e s CV) (hviab : ViableAtVote ℓ e (s + 1) C)
    (hlocks : ∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L C)
    (hd : ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s}) :
    VoteExtends U e.msg C := by
  sorry

/-- The growing optimistic transfer (`SA.Growing.optimistic_transfer_stored`); stand-in. -/
theorem optimistic_transfer_stored_stub (hrun : ACRun proposer tr H U) {s : Nat}
    {x y : Fin sp.n} {i₀ i : Nat} {B D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hx : x ∈ H (tr.time i₀)) (hopt : OptimisticLockAt tr x i₀ s D CV) (hBD : Anc U B D)
    (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n)
    (hy : y ∈ H (tr.time i)) (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hcarry : CarryAt tr U y i e s CV) (hviab : ViableAtVote ℓ e (s + 1) B)
    (hearlier : EarlierVotesExtendAt tr H U i (s + 1) B) : VoteExtends U e.msg B := by
  sorry

end Consensus.Goldilocks.SA.Growing

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- The growing AC projection (`Compose.Growing.goldilocks_ac_projection`); stand-in. -/
theorem goldilocks_ac_projection_stub : GoldilocksACProjection := by
  sorry

/-- The node transport's result carry (`result_carry_at`); stand-in. -/
theorem result_carry_at_stub (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b) {X : Fin sp.n}
    {i₀ s : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hX : X ∈ H (tr.time i₀)) (hR : SA.ResultAt tr.projAC X i₀ s C CV) {y : Fin sp.n} {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) (hF : Anc (tr.HonestBlocksAt H) ℓ.frame.F C) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s CV := by
  sorry

/-- The node transport's optimistic carry (`optimistic_carry_at`); stand-in. -/
theorem optimistic_carry_at_stub (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b) {X : Fin sp.n}
    {i₀ s : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hX : X ∈ H (tr.time i₀)) (hO : SA.OptimisticLockAt tr.projAC X i₀ s C CV) {y : Fin sp.n}
    {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) (hF : Anc (tr.HonestBlocksAt H) ℓ.frame.F C) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e s CV := by
  sorry

/-- The node transport's writer pool (`result_writer_pool_at`); stand-in. -/
theorem result_writer_pool_at_stub (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b) {X : Fin sp.n}
    {i₀ s : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hX : X ∈ H (tr.time i₀)) (hR : SA.ResultAt tr.projAC X i₀ s C CV) (hi₀ : tr.time i₀ ≤ b)
    {y : Fin sp.n} {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time i))
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1) :
    ∀ v ∈ (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.projAC.state X i₀).pool s ∨
        v.val ∈ SA.equivocators {w | w ∈ (tr.projAC.state X i₀).pool s} := by
  sorry

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
  have hrun' := goldilocks_ac_projection_stub sp ro dg H tr proposer hrun hnc
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
  · exact SA.Growing.result_transfer_stub hrun' hx hR hy hc hs
      (result_carry_at_stub hrun hnc hsync hx hR hy hc hs hib hF) (Or.inl hv) hlocks
      (result_writer_pool_at_stub hrun hnc hsync hx hR hi₀ hy hc hs)
  · exact SA.Growing.optimistic_transfer_stored_stub hrun' hx hO .refl hf hy hc hs
      (optimistic_carry_at_stub hrun hnc hsync hx hO hy hc hs hib hF) (Or.inl hv) hE

end Consensus.Goldilocks.Compose.Growing

end
