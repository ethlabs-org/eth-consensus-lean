module
public import AvailableChainPCSAProofs.Proofs.Clean.CountTransport

public section

/-! C6 ClockLockRetention: concrete receipt and count support. -/
namespace AvailableChain.PCSA
variable {n : Nat}
private theorem release_head_congr (v w : GridCO.State n .root)
    (hb : v.blocks = w.blocks) (hd : v.headDomain = w.headDomain)
    (o : GridCO.Wire n .root) : GridCO.resolvedHead? v o = GridCO.resolvedHead? w o := by
  change ((GridCO.headTarget? o).bind fun r =>
    (Block.findByRoot? (v.headDomain.getD v.blocks) r).bind fun B =>
      if B ∈ v.blocks then some B else none) =
    ((GridCO.headTarget? o).bind fun r =>
      (Block.findByRoot? (w.headDomain.getD w.blocks) r).bind fun B =>
        if B ∈ w.blocks then some B else none)
  rw [hb, hd]
private theorem release_resolved_congr (v w : GridCO.State n .root)
    (hb : v.blocks = w.blocks) (hd : v.headDomain = w.headDomain)
    (hvs : v.voteStamp = w.voteStamp) (hbs : v.blockStamp = w.blockStamp)
    (ht : v.now = w.now) (o : GridCO.Wire n .root) (t : Time) :
    GridCO.resolvedBefore v o t = GridCO.resolvedBefore w o t := by
  delta GridCO.resolvedBefore
  rw [release_head_congr v w hb hd o]
  cases GridCO.resolvedHead? w o with
  | none => rfl
  | some B =>
    change (decide (B.slot ≤ (GridCO.headLabel? o).getD 0) &&
      decide (GridCO.stampVote v o < t) && decide (GridCO.stampBlock v B < t)) = _
    delta GridCO.stampVote GridCO.stampBlock
    rw [hvs, hbs, ht]
/-- The release count reads only cumulative resolution, HEADs, receipt stamps, and time. -/
theorem pcsa_release_count_congr (q : GridCO.Params) (v w : GridCO.State n .root)
    (hb : v.blocks = w.blocks) (hd : v.headDomain = w.headDomain) (hv : v.votes = w.votes)
    (hvs : v.voteStamp = w.voteStamp) (hbs : v.blockStamp = w.blockStamp)
    (ht : v.now = w.now) (s : Slot) (B : Block) :
    GridCO.releaseCount q v s B = GridCO.releaseCount q w s B := by
  have hraw : GridCO.votesAt v s = GridCO.votesAt w s := by
    delta GridCO.votesAt
    rw [hv]
  have hres : ((GridCO.votesAt v s).filter (fun o => GridCO.resolvedBefore v o
      (GridCO.releaseTime q s))) = (GridCO.votesAt w s).filter (fun o =>
        GridCO.resolvedBefore w o (GridCO.releaseTime q s)) := by
    rw [hraw]
    apply List.filter_congr
    intro o _
    exact release_resolved_congr v w hb hd hvs hbs ht o _
  delta GridCO.releaseCount
  dsimp only
  rw [hres, hraw]
  congr 1
  apply List.filter_congr
  intro i _
  congr 1
  apply List.any_congr rfl
  intro o
  rw [release_head_congr v w hb hd o]
/-- A clock's release count equals the count with only its time updated. -/
theorem pcsa_clock_release_count (p : Params) (st : State p.n) (t : Time) (s : Slot) (B : Block) :
    GridCO.releaseCount p.toParams.engine (actView (clock p st t)) s B =
      GridCO.releaseCount p.toParams.engine (actView { st with base := { st.base with now := t } })
        s B := by
  apply pcsa_release_count_congr
  · change (clock p st t).base.blocks.filter _ = st.base.blocks.filter _
    rw [pcsa_clock_blocks]
    apply List.filter_congr
    intro A _
    delta activeCompatible
    rw [pcsa_body_clock_fg]
  · change some ((clock p st t).base.headDomain.getD (clock p st t).base.blocks) =
      some (st.base.headDomain.getD st.base.blocks)
    rw [pcsa_clock_blocks, pcsa_clock_headDomain]
  · exact pcsa_clock_heads p st t
  · exact pcsa_clock_headStamps p st t
  · exact pcsa_clock_bodyStamps p st t
  · exact pcsa_clock_now p st t
end AvailableChain.PCSA

namespace AvailableChain.PCSA
/-- Live rows survive the pre-gate clock when the release count is below their level. -/
theorem pcsa_clockPre_keep_lock (p : Params) (st : State p.n) (t : Time)
    (row : Block × Nat × Time) (hr : row ∈ st.base.obligations) (ht : t < row.2.2)
    (hrelease : ∀ s, t = SA.releaseTime p.toParams s →
      GridCO.releaseCount p.toParams.engine (actView (clock p st t)) s row.1 < row.2.1) :
    row ∈ (clockPre p st t).base.obligations := by
  let st0 : State p.n := { st with base := GridCO.expire { st.base with now := t } t }
  let fs := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let st1 : State p.n := if 0 ≤ t - 3 * p.Δ && t == SA.freezeTime p.toParams fs then
    { onView (fun v => GridCO.freeze p.toParams.engine v fs) st0 with
      pcSnapshot := if (st0.pcSnapshot.find? (fun row => row.1 == fs)).isSome then
        st0.pcSnapshot else st0.pcSnapshot ++ [(fs, st0.pcs)] } else st0
  let es := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let st2 : State p.n := if 0 ≤ t - 2 * p.Δ && t == SA.earlyTime p.toParams es then
    onView (fun v => { v with early := v.early ++
      [(es, GridCO.earlyVotes p.toParams.engine v es)] }) st1 else st1
  let rs := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
  have hrow0 : row ∈ st0.base.obligations := List.mem_filter.mpr ⟨hr, decide_eq_true ht⟩
  have hrow1 : row ∈ st1.base.obligations := by
    dsimp only [st1]
    split <;> exact hrow0
  have hrow2 : row ∈ st2.base.obligations := by
    dsimp only [st2]
    split <;> exact hrow1
  have hcount : GridCO.releaseCount p.toParams.engine (actView st2) rs row.1 =
      GridCO.releaseCount p.toParams.engine (actView (clock p st t)) rs row.1 := by
    rw [pcsa_clock_release_count]
    apply pcsa_release_count_congr
    all_goals dsimp only [st2, st1]
    all_goals split <;> split <;> rfl
  change row ∈ (if 0 ≤ t - 5 * p.Δ && t == SA.releaseTime p.toParams rs then
    onView (fun v => SA.Root.release p.toParams v rs) st2 else st2).base.obligations
  split
  · rename_i hq
    apply List.mem_filter.mpr
    refine ⟨hrow2, decide_eq_true ?_⟩
    rw [hcount]
    exact hrelease rs (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hq).2)
  · exact hrow2
end AvailableChain.PCSA

end
