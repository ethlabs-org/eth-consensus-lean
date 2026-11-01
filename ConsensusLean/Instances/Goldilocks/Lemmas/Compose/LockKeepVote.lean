module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockKeepHonest
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.HeadLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPointLocks

public section

/-! # Goldilocks: honest votes that read a lock keep it

consensus-lean#135 (WI-15/16), r14 s1 L1.2. `heldVote_compatible_of_cast`: at an AC cut `j` of
an honest node `y`, a held vote of an honest validator whose casting read a live lock block (or
`fc_root`) `C ⪰ B` compatible with every live lock block of its read point has only heads (in
`y`'s frame) compatible with `B` (`SA.castAt_head_anc`, then coherence of the honest blocks).
`lock_keep_interval_cases_locked`: `lock_keep_interval_cases_honest` with its compatibility
premise replaced by that read-point premise for each honest held vote of slot `slot(t_j) − 1`.
The premise is the inter-node part of L1.2 (that every honest voter of the slot reads such a
`C`); it is not proved here. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The read-point premise at a vote `x` and a block `B`: every casting of `x` by its validator
reads a live lock block or `fc_root` `C` that extends `B` and is compatible with every live lock
block of the read point. -/
abbrev ReadsLockAbove (tr : GoldilocksTrace sp ro) (x : Vote sp.n)
    (B : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∀ k (ℓ' : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)) e,
    SA.CastAt tr.projAC x.val k ℓ' e → e.msg = x →
    ∃ C ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ'.frame (tr.time k) ∪ {ℓ'.frame.fcRoot},
      (∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ'.frame (tr.time k),
        Compatible ℓ'.frame.tree L C) ∧ ℓ'.frame.Anc B C

/-- **A held honest vote that read a lock above `B` is compatible with `B`.** -/
theorem heldVote_compatible_of_cast (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.CallAt y j (.ac ℓ))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (Node.frame (tr.state y j)).tree)
    {x : Vote sp.n}
    (hx : x ∈ SA.heldVotes (tr.state y j).ac (tr.state y (j + 1)).ac (Node.frame (tr.state y j)))
    (hxH : x.val ∈ H) (hread : ReadsLockAbove tr x B) :
    ∀ Hd ∈ (Node.frame (tr.state y j)).tree, Hd.root = x.head →
      Compatible (Node.frame (tr.state y j)).tree Hd B := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hU := hr.coherent
  have hcA : tr.projAC.CallAt y j ℓ := projAC_callAt.2 hc
  have hfr : ℓ.frame = Node.frame (tr.state y j) := (hrun.cutLaw y hy j _ hc).1
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rcases hr.frameLaw y hy j ℓ hcA with ⟨-, Φ₀, -, -, h⟩ | ⟨j', ℓ', -, -, -, h⟩ <;> exact h.1
  rw [hfr] at hΦ hΦU
  obtain ⟨k, e, ⟨ℓ', hc', he'⟩, rfl⟩ : ∃ k e, SA.VoteAt tr.projAC x.val k e ∧ e.msg = x := by
    rcases SA.mem_heldVotes.1 hx with ⟨τ, hv⟩ | ⟨τ, hv⟩ | ⟨C, hC, hv⟩
    · rw [← projAC_state hrun.toLocalRun hy] at hv
      obtain ⟨k, -, e, he, hm⟩ := hrun'.honest.pool_vote y hy j τ x hv hxH
      exact ⟨k, e, he, hm⟩
    · rw [← projAC_state hrun.toLocalRun hy] at hv
      obtain ⟨k, -, e, he, hm⟩ := hrun'.honest.pool_vote y hy (j + 1) τ x hv hxH
      exact ⟨k, e, he, hm⟩
    · rw [← hfr] at hC
      have hvB : x ∈ SA.blockVotes C :=
        hv.elim id fun h => (SA.frame_validPayload sp hr hy hcA C hC).2 x h
      obtain ⟨k, -, e, he, hm⟩ := hrun'.honest.carried_vote y hy j ℓ hcA C hC x hvB hxH
      exact ⟨k, e, he, hm⟩
  have hcast : SA.CastAt tr.projAC e.msg.val k ℓ' e := ⟨hc', he'⟩
  obtain ⟨C, hC, hcomp, hBC⟩ := hread k ℓ' e hcast rfl
  obtain ⟨Hd₀, hHd₀, hHd₀r, hBHd₀⟩ := SA.castAt_head_anc hr hxH hcast hC hcomp hBC
  have hΦ'U : ℓ'.frame.tree ⊆ tr.HonestBlocks H := by
    rcases hr.frameLaw _ hxH k ℓ' hc' with ⟨-, Φ₀, -, -, h⟩ | ⟨j', ℓ'', -, -, -, h⟩ <;>
      exact h.1.2
  intro Hd hHd hHdr
  obtain rfl : Hd = Hd₀ := hU.1 (hΦU hHd) (hΦ'U hHd₀) (hHdr.trans hHd₀r.symm)
  exact Or.inr (SA.anc_tree_of_anc_U hU hΦ hΦU hB (Anc.mono hΦ'U hBHd₀) hHd)

/-- **A lock kept over `[i, k]` against honest votes that read a lock above it.**
`lock_keep_interval_cases_honest` with the compatibility premise at each cut `j` replaced by:
every held vote of slot `slot(t_j) − 1` of an honest validator read, when cast, a live lock
block or `fc_root` above `B` compatible with every live lock block of its read point. -/
theorem lock_keep_interval_cases_locked (hrun : GoldilocksRun proposer dg H tr)
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
          (x.slot : Int) = (sp.slot (tr.time j) : Int) - 1 → ReadsLockAbove tr x B)) :
    l ∈ (tr.state y k).ac.locks :=
  lock_keep_interval_cases_view hrun hy hik hl hBr fun j h1 h2 => by
    obtain ⟨hk, hB, hc, hu⟩ := hstep j h1 h2
    refine ⟨hk, hB, hc, fun ℓ hcall => hu.imp_right fun hread => ?_⟩
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
      (fun x hx hxH hs => heldVote_compatible_of_cast hrun hnc hy hcall hB hx hxH
        (hread x hx hxH hs)) hf

/-- **The read-point premise from a read live lock.** `ReadsLockAbove tr x B` holds for an
honest `x` when every casting of `x` reads a live lock block or `fc_root` that extends `B`: the
compatibility with every live lock block of the read point is `SA.castAt_compatible_of_live`. -/
theorem readsLockAbove_of_live (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {x : Vote sp.n} (hxH : x.val ∈ H) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hlive : ∀ k (ℓ' : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)) e,
      SA.CastAt tr.projAC x.val k ℓ' e → e.msg = x →
      ∃ C ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ'.frame (tr.time k) ∪ {ℓ'.frame.fcRoot},
        ℓ'.frame.Anc B C) :
    ReadsLockAbove tr x B := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  intro k ℓ' e hc hm
  obtain ⟨C, hC, hBC⟩ := hlive k ℓ' e hc hm
  exact ⟨C, hC, SA.castAt_compatible_of_live hr hxH hc hC, hBC⟩

end Consensus.Goldilocks.Compose

end
