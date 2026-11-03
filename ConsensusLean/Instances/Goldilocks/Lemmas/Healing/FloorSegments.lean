module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.FloorUpdate
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockFloorGlobal

public section

/-! # Goldilocks: lock-floor segments from unanimous updates

consensus-lean#135, item N4. Segment `m` starts at the cut after an honest node's tick at
`t_{p_m} + 6Δ`, and its floor slot is `p_m`. The tick at
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

end Consensus.Goldilocks.Healing

end
