module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.FloorUpdate
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockFloorSegments

public section

/-! # Goldilocks: lock-floor segments from unanimous updates

consensus-lean#135, item N4. Segment `m` starts at the cut after an honest node's tick at
`t_{p_m} + 6Δ`, and its floor slot is `p_m` (`floor_of_unanimous_update`). The tick at
`t_q + 6Δ` lies in slot `q + 1` (`slot_update_time`). Segment `m` must keep its lock live up to
the update tick of slot `p_{m+1}`, which is in slot `p_{m+1} + 1`; a lock of slot `p_m` is live
there iff `p_{m+1} + 1 ≤ p_m + k`. So the spacing condition is `p_{m+1} − p_m ≤ k − 1`: the
consecutive form (`UnanimousFrom`, spacing 1) suffices as `k ≥ 2`; a spacing of exactly `k`
slots (a window `B = 4kΔ` of `UnanimousWithin`) is one slot short. At spacing `k` the lock of
slot `p_m` expires at slot `p_m + k + 1`, the honest votes of that slot are cast at its start,
and the lock of slot `p_{m+1}` is written only `2Δ` later. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g : Time}

/-- The update tick of slot `q`, at `t_q + 6Δ`, lies in slot `q + 1`. -/
theorem slot_update_time (q : Nat) : sp.slot (sp.ts q + 6 * sp.Δ) = q + 1 := by
  have hΔ := sp.toParams.hΔ
  have hts1 : sp.ts (q + 1 : Nat) = sp.ts q + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hts2 : sp.ts (q + 1 + 1 : Nat) = sp.ts (q + 1 : Nat) + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  exact SA.slot_of_mem sp (q + 1) (by rw [hts1]; linarith) (by rw [hts2, hts1]; linarith)

/-- **No expiry up to the next update tick.** If every cut before `b` is at most at the update
tick `t_q + 6Δ` and `q + 1 ≤ p + k`, a lock of slot `p` is live at every cut before `b`. -/
theorem slot_le_of_update_time (hrun : GoldilocksRun proposer dg H tr) {p q b : Nat}
    (hq : q + 1 ≤ p + sp.k) (htb : ∀ c < b, tr.time c ≤ sp.ts q + 6 * sp.Δ) :
    ∀ c < b, sp.slot (tr.time c) ≤ p + sp.k := by
  intro c hc
  have h := SA.slot_mono sp (hrun.time_nonneg c) (htb c hc)
  rw [slot_update_time] at h
  omega

/-- **The floor over segments of unanimous updates** (N4). Slots `p 0 < … ` with spacing
`p (m+1) + 1 ≤ p m + k` (`hsp`); every cut before `i (m+1)` is at most at the update tick
`t_{p (m+1)} + 6Δ` (`htime`). For `m + 1 < M`, slot `p (m+1)` is unanimous for `Ps (m+1) ⪰ B₀`
and every honest `x` has its update tick in `[i m, i (m+1))` with the premises of
`floor_of_unanimous_update` (`htick`). Segment `0` has its floor at `i 0` (`hbase0`); the frame
premises (`hcut`, `hN`) and the early votes (N5) stay premises. Conclusion: at every cut
`j ∈ [i 0, i M]` each honest `x` has the floor of slot `p m` of a segment `m ∋ j`. -/
theorem lock_floor_unanimous (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n)
    (hS : SA.HealthyBase tr.projAC H (tr.HonestBlocks H) proposer g)
    {B₀ : SA.Blk sp.n (List (FG.Att sp.n))} (M : Nat) (hM : 0 < M) (i : Nat → Nat)
    (hi : ∀ m < M, i m ≤ i (m + 1)) (p : Nat → Nat) (Ps : Nat → SA.Blk sp.n (List (FG.Att sp.n)))
    (hsp : ∀ m < M, p (m + 1) + 1 ≤ p m + sp.k)
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
    (hearly : Compose.EarlyVotes H tr (i 0) B₀) :
    ∀ j, i 0 ≤ j → j ≤ i M → ∀ x ∈ H, ∃ m < M, i m ≤ j ∧ j ≤ i (m + 1) ∧
      Compose.FloorAt tr x j B₀ (p m) ∧ (j < i (m + 1) → Compose.UnlockKeeps tr x j B₀) := by
  have hk2 := sp.two_le_k
  refine Compose.lock_floor_chain_carry hrun hnc hf M hM i hi (fun m _ => p m) hbase0
    (fun m hm x hx => ?_) (fun m hm x hx j hj hjN => ?_) hN hearly
  · obtain ⟨k, ℓ, hc, hcall, htk, hmk, hki, hPt, hva, hlocks, hB0⟩ := htick m hm x hx
    refine ⟨k + 1, hmk, hki, floor_of_unanimous_update hrun hS (hp4 m hm) (hun m hm) hx hc
      hcall htk hPt (hPg m hm) hva hlocks hB0, fun c _ hc' => ?_⟩
    exact slot_le_of_update_time hrun (p := p (m + 1)) (by omega) (htime m (by omega)) c hc'
  · exact ⟨slot_le_of_update_time hrun (hsp m hm) (htime m hm) j hjN, hcut m hm x hx j hj hjN⟩

end Consensus.Goldilocks.Healing

end
