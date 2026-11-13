module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.LiftFrame
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Growing
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # Goldilocks under `Sleepy` with growing faults: the live locks at a vote

`vote_locks_compatible_at`: at a slot-`(s+1)` vote of a node honest at its cut `i ≤ b`, every live
lock block is compatible with a block `B` that is compatible with every member of the healed
family within `b` of label at most `s` and that the earlier slot-`(s+1)` votes of nodes honest at
them extend, when the live locks of slot at most `s` have labels from the lock floor on. A lock of
slot at most `s` sits below the holder's own lock write of its slot (`lock_write_at`), a family
member; one of slot `s + 1` is optimistic, and its check at a cut `c ≤ i` is counted with
`2 f < n` at that cut (`hB.two`). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **The live locks at a slot-`(s+1)` vote are compatible with `B`** under growing faults. -/
theorem vote_locks_compatible_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} {σ₀ : Nat} (hB : SleepyBoundsFrom tr H σ₀ b)
    {g : Time} {rL rO s : Nat} {y : Fin sp.n}
    {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b)
    (hlive : ∀ l ∈ SA.liveLocks sp e.readPoint.locks ℓ.frame (tr.time i), l.slot ≤ s →
      rL ≤ l.slot)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C j, HealedOrigin tr H g rL rO C j b → j ≤ s → Compatible (tr.HonestBlocksAt H) B C)
    (hE : SA.EarlierVotesExtendAt tr.projAC H (tr.HonestBlocksAt H) i (s + 1) B) :
    ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocksAt H) L B := by
  have hd := hrun.time_nonneg i
  have hm := hrun.time_mono
  have hsub := upTo_subset hrun hd
  have hU := honestBlocksAt_coherent hrun hnc
  have hrun' := acRun_upTo hrun hnc hd
  have hr := hrun'.localRun
  have hcT : SA.CastAt (tr.projAC.upTo (tr.time i)) y i ℓ e := sa_castAt_upTo.mpr ⟨le_rfl, hc⟩
  have hf := hB.two (tr.time i) hd hib
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hy hc.1
  have hsi : e.msg.slot = sp.slot (tr.time i) := (castAt_spec_at hrun hnc hy hc).2.1
  -- compatibility with `B` passes to ancestors
  have down : ∀ {X Y}, Anc (tr.HonestBlocksAt H) X Y → Compatible (tr.HonestBlocksAt H) Y B →
      Compatible (tr.HonestBlocksAt H) X B := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact SA.anc_total hU hXY h
  rintro L ⟨hL, l, hlm, hlL⟩
  have hlab := hlive l hlm
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, hlive, rfl⟩ := hlm
  have hLe : L = ℓ.frame.viableAncestor B₀ :=
    hU.1 (hΦU hL) (hΦU (SA.viableAncestor_anc hΦ hB₀).1) hlL.symm
  subst hLe
  refine down (Anc.mono hΦU (SA.anc_viableAncestor _ B₀)) ?_
  rcases le_or_gt l₀.slot s with hle | hlt
  · -- a lock of slot at most `s` sits below a stored lock, below the holder's own lock write of
    -- its slot, a family member
    obtain ⟨l₁, hl₁, hsl₁, B₁, hB₁, hB₁r, B₀', hB₀', hB₀'r, hA⟩ :=
      SA.readPoint_locks_below_stored hr hy hcT
        (show 0 < sp.slot (tr.time i) by omega) l₀ hl₀
        (show l₀.slot ≠ sp.slot (tr.time i) by omega)
    obtain rfl : B₀' = B₀ := hΦ.coherent.1 hB₀' hB₀ (hB₀'r.trans hB₀r.symm)
    rw [projAC_upTo_state hrun le_rfl, projAC_state_at hrun hy] at hl₁
    obtain ⟨L₁, hL₁, hL₁r, D, hD, hL₁D⟩ :=
      lock_write_at hrun hnc hd (fun _ hk => hm hk.le) hy l₁ hl₁
    have hDm : HealedOrigin tr H g rL rO D l₁.slot b :=
      HealedOrigin.of_lock (by rw [← hsl₁]; exact hlab hle) (hD.mono hib)
    obtain rfl : L₁ = B₁ := hU.1 (mem_honestBlocksAt hrun hy hL₁) (hΦU hB₁)
      (hL₁r.trans hB₁r.symm)
    exact down ((Anc.mono hΦU hA).trans hL₁D) (hBc D l₁.slot hDm (by omega)).symm
  · -- a lock of slot `s + 1` or later is optimistic, counted at the vote's cut, over earlier
    -- slot-`(s+1)` votes of nodes honest at them
    obtain ⟨Φ', A, D, -, hΦ'U, -, h34, hpool, -, L₀, hL₀, hL₀r, hL₀D⟩ :=
      SA.lock_origin_readPoint hrun' hy hcT l₀ hl₀ (by rw [hs]; push_cast; omega)
    obtain rfl : L₀ = B₀ := hU.1 (hsub hL₀) (hΦU hB₀) (hL₀r.trans hB₀r.symm)
    refine down (Anc.mono hsub hL₀D)
      (SA.origin_compatible hU (hΦ'U.trans hsub) h34
        (by simpa only [hrun'.stock] using hf) fun v hv hvH => ?_)
    obtain ⟨hvs, j, hj, e', hvote, rfl⟩ := hpool v hv hvH
    obtain ⟨hjd, hvote⟩ := sa_voteAt_upTo.mp hvote
    have hvj : e'.msg.val ∈ H (tr.time j) := hrun.antitone hjd hvH
    obtain ⟨ℓ', hcj⟩ := id hvote
    have hsj : e'.msg.slot = sp.slot (tr.time j) := (castAt_spec_at hrun hnc hvj hcj).2.1
    have : sp.slot (tr.time j) ≤ sp.slot (tr.time i) :=
      SA.slot_mono sp (hrun.time_nonneg j) (hm hj.le)
    exact hE _ j hj hvj e' hvote (by omega)

end Consensus.Goldilocks.Compose.Growing

end
