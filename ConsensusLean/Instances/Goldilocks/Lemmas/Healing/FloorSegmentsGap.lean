module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.FloorSegments
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockFloorGaps
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Batch

public section

/-! # Goldilocks: lock-floor segments at spacing `k`

consensus-lean#137. `lock_floor_unanimous` needs `p_{m+1} + 1 ≤ p_m + k`; `UnanimousWithin T (4kΔ)`
allows `p_{m+1} = p_m + k`. At that spacing the lock of slot `p_m` expires at the start of slot
`p_{m+1} + 1`, and the fresh lock of slot `p_{m+1}` is written only at `t_{p_{m+1}+1} + 2Δ`: the
honest votes of slot `p_{m+1} + 1` do not read a floor lock.

`unanimous_next_votes_extend_healthy`: under `HealthyBase`, the honest votes of the slot after a
unanimous slot `u` on `P` extend `P` when, at each of them, the frame's `F` is below `P` and `P` is
viable (the transfer A1.3 with the unanimous batch). `lock_floor_unanimous_le` takes spacing
`p (m+1) ≤ p m + k` and, for exact spacing, these votes extending `B₀` (`hnext`). It concludes
the floor at the start of each segment, the floor of slot `p m` at each cut of segment `m` where
its lock is live, and `UnlockKeeps` of `B₀` at every cut. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g : Time}

/-- **The votes after a unanimous slot extend its block** (under `HealthyBase`). Slot `u` is
unanimous for `P` with `ḡ + 4Δ ≤ t_u`; at every honest slot-`(u+1)` vote, `F ⪯ P` and `P` is
viable at the vote (`hviab`). Then every honest slot-`(u+1)` vote extends `P`. -/
theorem unanimous_next_votes_extend_healthy
    (hS : SA.HealthyBase tr.projAC H (tr.HonestBlocks H) proposer g)
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ tr.HonestBlocks H)
    (hun : Unanimous tr H u P) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hviab : ∀ y ∈ H, ∀ j ℓ e, SA.CastAt tr.projAC y j ℓ e → e.msg.slot = u + 1 →
      Anc (tr.HonestBlocks H) ℓ.frame.F P ∧ SA.ViableAtVote ℓ e (u + 1) P) :
    ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → e.msg.slot = u + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg P := by
  have hprev : ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → e.msg.slot = u →
      SA.VoteExtends (tr.HonestBlocks H) e.msg P :=
    fun y hy j e hv hs => ⟨P, hP, (hun y hy j e hv hs).symm, .refl⟩
  have all : ∀ j y, y ∈ H → ∀ e, SA.VoteAt tr.projAC y j e → e.msg.slot = u + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg P := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro y hy e hv hs
      obtain ⟨ell, hcast⟩ := hv
      obtain ⟨hFP, hvi⟩ := hviab y hy j ell e hcast hs
      have hsl := (SA.castAt_spec hS.run.localRun hy hcast).2.1
      have hT : SA.gbar g ≤ sp.ts ((sp.slot (tr.projAC.time j) : Int) - 1) := by
        rw [← hsl, hs]
        simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
        linarith [sp.toParams.hΔ]
      apply SA.next_vote_extends_before hS.run hy hcast hs ?_
        (SA.honest_voters_half hS hgu)
        (SA.healthy_carry_votes hS hgu hprev hy hcast hs hFP)
        (hS.faultBound (hS.run.localRun.time_nonneg j) hT)
        (hS.syncAC (by linarith [sp.toParams.hΔ]) (tr.projAC.time j)) hvi
      intro z hz q hq v hv hvs
      rcases hvs with hvs | hvs
      · exact hprev z hz q v hv hvs
      · exact ih q hq z hz v hv hvs
  exact fun y hy j e hv hs => all j y hy e hv hs

/-- **The floor over segments of unanimous updates, spacing up to `k`.** The premises of
`lock_floor_unanimous` with `p (m+1) ≤ p m + k` (`hsp`), without the no-expiry part of `hcut`,
and with `hnext`: at exact spacing `p (m+1) = p m + k`, every honest vote of slot `p (m+1) + 1`
extends `B₀` (from `unanimous_next_votes_extend_healthy` and `B₀ ⪯ Ps (m+1)`). Conclusion: every
honest `x` has the floor of slot `p m` at `i m`; at each cut `j ∈ [i 0, i M)`, in its segment
`m`, `x` has the floor of slot `p m` while that lock is live (`slot(t_j) ≤ p m + k`), and
`unlock` keeps `B₀`. A cut of segment `m` without the floor has `slot(t_j) = p m + k + 1` and
`t_j ≤ t_{p (m+1)} + 6Δ`: it lies within `2Δ` after the start of slot `p (m+1) + 1`. -/
theorem lock_floor_unanimous_le (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n)
    (hS : SA.HealthyBase tr.projAC H (tr.HonestBlocks H) proposer g)
    {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} (M : Nat) (hM : 0 < M) (i : Nat → Nat)
    (hi : ∀ m < M, i m ≤ i (m + 1)) (p : Nat → Nat) (Ps : Nat → SA.Blk sp.n (List (FG.Att sp.n)))
    (hsp : ∀ m < M, p (m + 1) ≤ p m + sp.k)
    (htime : ∀ m < M, ∀ c < i (m + 1), tr.time c ≤ sp.ts (p (m + 1)) + 6 * sp.Δ)
    (hbase0 : ∀ x ∈ H, Compose.FloorAt tr x (i 0) B₀ (p 0))
    (hp4 : ∀ m, m + 1 < M → SA.gbar g + 4 * sp.Δ ≤ sp.ts (p (m + 1)))
    (hun : ∀ m, m + 1 < M → Unanimous tr H (p (m + 1)) (Ps (m + 1)))
    (hPg : ∀ m, m + 1 < M → (Ps (m + 1)).root ≠ sp.genesisRoot)
    (htick : ∀ m, m + 1 < M → ∀ x ∈ H, ∃ k, ∃ ℓ : ACLabel (goldilocksNode sp ro),
      tr.projAC.CallAt x k ℓ ∧ ℓ.call = .tick ∧ tr.time k = sp.ts (p (m + 1)) + 6 * sp.Δ ∧
      i m ≤ k + 1 ∧ k + 1 ≤ i (m + 1) ∧ Ps (m + 1) ∈ ℓ.frame.tree ∧
      ℓ.frame.viableAncestor (Ps (m + 1)) = Ps (m + 1) ∧
      (∀ L ∈ SA.liveLockBlocks sp (tr.projAC.state x k).locks ℓ.frame (tr.time k),
        Compatible (tr.HonestBlocks H) L (Ps (m + 1))) ∧ ℓ.frame.Anc B₀ (Ps (m + 1)))
    (hcut : ∀ m < M, ∀ x ∈ H, ∀ j, i m ≤ j → j < i (m + 1) →
      B₀ ∈ (tr.state x j).fg.toFrame.tree ∧ Compose.FrameKeeps tr x j B₀)
    (hN : ∀ m < M, ∀ x ∈ H, B₀ ∈ (tr.state x (i (m + 1))).fg.toFrame.tree)
    (hnext : ∀ m < M, p (m + 1) = p m + sp.k → ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e →
      e.msg.slot = p (m + 1) + 1 → SA.VoteExtends (tr.HonestBlocks H) e.msg B₀)
    (hearly : Compose.EarlyVotes H tr (i 0) B₀) :
    (∀ m < M, ∀ x ∈ H, Compose.FloorAt tr x (i m) B₀ (p m)) ∧
    ∀ j, i 0 ≤ j → j < i M → ∀ x ∈ H, ∃ m < M, i m ≤ j ∧ j < i (m + 1) ∧
      (sp.slot (tr.time j) ≤ p m + sp.k → Compose.FloorAt tr x j B₀ (p m)) ∧
      Compose.UnlockKeeps tr x j B₀ := by
  have hk2 := sp.two_le_k
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  refine Compose.lock_floor_chain_gaps hrun hnc hf M hM i hi (fun m _ => p m) hbase0
    (fun m hm x hx => ?_) hcut hN (fun m hm x hx k hk hkN hgt e hv => ?_)
    (Compose.earlyVotesExt_of_earlyVotes hearly)
  · obtain ⟨k, ℓ, hc, hcall, htk, hmk, hki, hPt, hva, hlocks, hB0⟩ := htick m hm x hx
    refine ⟨k + 1, hmk, hki, floor_of_unanimous_update hrun hS (hp4 m hm) (hun m hm) hx hc
      hcall htk hPt (hPg m hm) hva hlocks hB0, fun c _ hc' => ?_⟩
    exact slot_le_of_update_time hrun (p := p (m + 1)) (by omega) (htime m (by omega)) c hc'
  · have hle := SA.slot_mono sp (hrun.time_nonneg k) (htime m hm k hkN)
    rw [slot_update_time] at hle
    obtain ⟨ℓ, hc, he⟩ := hv
    have hsl : e.msg.slot = sp.slot (tr.time k) := (SA.castAt_spec hr hx ⟨hc, he⟩).2.1
    have := hsp m hm
    exact hnext m hm (by omega) x hx k e ⟨ℓ, hc, he⟩ (by omega)

end Consensus.Goldilocks.Healing

end
