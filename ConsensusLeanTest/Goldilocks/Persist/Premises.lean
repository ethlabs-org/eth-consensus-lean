module
public import ConsensusLeanTest.Goldilocks.Runs.OneValidator.Run
@[expose] public section

/-! # The one-validator tick run: `Carry` at every slot, and `Sleepy`

Kind (a), joint satisfiability (CONTRIBUTING "Statements"), on the one-validator tick run of
`Goldilocks/Runs/OneValidator/Premises` (`n = 1`, `Δ = 1`, `t_s = 4s`, a tick at every time, no
restart):

* **`Carry`** (`carry_cv`, every slot): the vote of slot `s + 1` is cast in `ac_on_block` of
  the own block at `t_{s+1}`, when the validator has accepted `blk s` and its ancestors (at
  their slot starts) and holds `cv s` with a stamp before `t_s + 3Δ`. The stamp is traced
  through `AC.readPoint_pool` and `AC.pool_origin`: it is the time of the cut that sent or
  admitted `cv s`, and that cut is before the tick of `t_s + 2Δ`, whose pool already holds
  `cv s` (`readPoint_stamp`).
* `tickRun_sleepy`: `SleepyRun` (`Sync[0, ∞)` and `f < h_t` at every `t_s, t_s + Δ,
  t_s + 2Δ`).

With `n = 1` and `f = 0` this shows the premise consistent, not met with faults. -/

namespace Consensus.Goldilocks.Witness.One

open AC Node ChainFrame

/-! ## Chain facts of the honest blocks -/

/-- Every honest block of the run is a chain block. -/
theorem honest_onChain : OnChain ((tickRun N1 dg1).HonestBlocks Set.univ) := by
  rintro B ⟨y, -, i, hB⟩
  obtain rfl := eq_v0 rfl y
  obtain ⟨m, -, rfl⟩ := (mem_tree_iff (state_fgGood i).blocks).1 hB
  exact ⟨m, rfl⟩

/-- Two chain blocks are compatible inside the honest blocks. -/
theorem compatible_blk (a b : Nat) :
    Compatible ((tickRun N1 dg1).HonestBlocks Set.univ) (blk a) (blk b) :=
  (le_total a b).elim (fun h => Or.inl (anc_honest h)) (fun h => Or.inr (anc_honest h))

/-! ## The vote cuts -/

/-- The `ac_on_block` cut of the own block of slot `k + 1`, which casts `cv (k + 1)`. -/
theorem vote_label (k : Nat) : ∃ (fg' : Store sp1.toParams N1.Payload) (e : N1.Em),
    (tickRun N1 dg1).label (8 * (4 * (k + 1)) + 3) =
      some (.ac ⟨.block (blk (k + 1)), fg'.toFrame, [e]⟩) ∧ FGGood fg' (k + 1) ∧
    e.msg = cv (k + 1) ∧ e.readPoint.pool = (tickState N1 dg1 (4 * (k + 1))).ac.pool := by
  obtain ⟨fg', e, -, hfg', he, hm, hp⟩ := tickCuts_A k
  refine ⟨fg', e, ?_, hfg', hm, hp⟩
  rw [tickRun_label, show (8 * (4 * (k + 1)) + 3) / 8 = 4 * (k + 1) by omega,
    show (8 * (4 * (k + 1)) + 3) % 8 = 3 by omega, he]
  rfl

/-- The AC projection of the tick run is an AC run. -/
theorem acRun : AC.ACRun (fun _ => v0) (tickRun N1 dg1).projAC Set.univ
    ((tickRun N1 dg1).HonestBlocks Set.univ) :=
  Compose.goldilocks_ac_projection sp1 ro1 dg1 Set.univ (tickRun N1 dg1) (fun _ => v0)
    tickRun_goldilocksRun (dg1_noColl _)

theorem etime_of_lt {a b : Time} (h : a < b) : ETime.of a < ETime.of b :=
  WithBot.coe_lt_coe.2 (WithTop.coe_lt_coe.2 h)

/-- **The stamp of a held vote at a later vote.** At the vote of cut `i`, the vote `cv s` that
the read point holds was received before `t_s + 3Δ`: its stamp is the time of the cut that sent
or admitted it, before the tick of `t_s + 2Δ` (whose pool already holds it). -/
theorem readPoint_stamp {s i : Nat} {ℓ : ACLabel N1} {e : N1.Em}
    (hc : AC.CastAt (tickRun N1 dg1).projAC v0 i ℓ e) (hx : cv s ∈ e.readPoint.pool s) :
    e.readPoint.voteStamp (cv s) < ETime.of (sp1.ts s + 3 * sp1.Δ) := by
  have hr := acRun.localRun
  obtain ⟨hpool, hst⟩ := AC.readPoint_pool hr (Set.mem_univ v0) hc hx
  rw [← hst rfl]
  rcases AC.pool_origin hr (fun _ => AC.voteStart_initial _) (Set.mem_univ v0) (i + 1)
    (cv s) hpool with
    ⟨k, -, ⟨ℓ', hc', hk⟩, hstk, -⟩ | ⟨k, -, ℓ', hc', hrs, -⟩
  · rw [hstk]
    apply etime_of_lt
    suffices hlt : k < 8 * (4 * s + 2) by
      rw [time_eq, ts_nat]
      change (((k / 8 : Nat)) : Int) < 4 * (s : Int) + 3 * 1
      omega
    obtain ⟨-, -, hl⟩ := projAC_call hc'
    rcases hk with ⟨e', he', hm⟩ | ⟨-, hnot, -⟩
    · rcases emit_cases hl he' with ⟨rfl, hm', -⟩ | ⟨k', fg', rfl, -, -, -, hm', -⟩
      · have : s = 0 := by have := congrArg Vote.slot (hm'.symm.trans hm); exact this.symm
        omega
      · have : k' + 1 = s := congrArg Vote.slot (hm'.symm.trans hm)
        omega
    · by_contra hge
      apply hnot
      change cv s ∈ ((tickRun N1 dg1).projAC.state v0 k).pool s
      rw [projAC_state']
      refine tickRun_pool_mono (Nat.le_of_not_lt hge) s ?_
      rw [state_tick, (good_tick (4 * s + 2)).ac.pool s,
        ite_pos ⟨by omega, by unfold tip; omega⟩]
      exact List.mem_singleton_self _
  · exact absurd ⟨ℓ', Compose.projAC_callAt.1 hc', hrs⟩ (tickRun_no_restart v0 k)

/-- **`Carry(s, S, B)` holds on the tick run**, for every slot `s` and counted votes inside
`{cv s}`: at the vote of slot `s + 1` (cut `8·t_{s+1} + 3`) the validator is awake and joined,
has accepted `blk s` and its ancestors before `t_s + 3Δ`, and holds `cv s`, received before
`t_s + 3Δ`. -/
theorem carry_cv (s : Nat) {CV : Set (Vote sp1.n)} (hCV : ∀ v ∈ CV, v = cv s) :
    AC.Carry (tickRun N1 dg1).projAC Set.univ ((tickRun N1 dg1).HonestBlocks Set.univ) s CV := by
  rintro y - i e ⟨ℓ, hc, he⟩ hslot
  obtain ⟨rfl, -, hl⟩ := projAC_call hc
  have hcast : AC.CastAt (tickRun N1 dg1).projAC v0 i ℓ e := ⟨hc, he⟩
  rcases emit_cases hl he with ⟨-, hm, -⟩ | ⟨k, fg', -, -, -, -, hm, hp⟩
  · rw [hm] at hslot
    change 0 = s + 1 at hslot
    omega
  have hks : k = s := by
    rw [hm] at hslot
    change k + 1 = s + 1 at hslot
    omega
  subst hks
  have hx : cv k ∈ e.readPoint.pool k := by
    rw [hp, (good_tick (4 * (k + 1))).ac.pool k, tip_A, ite_pos ⟨by omega, le_rfl⟩]
    exact List.mem_singleton_self _
  refine ⟨?_, (AC.castAt_spec acRun.localRun (Set.mem_univ v0) hcast).2.2.1, ?_, ?_⟩
  · change (0 : Int) ≤ ((i / 8 : Nat) : Int)
    positivity
  · intro v hv
    obtain rfl := hCV v hv
    refine ⟨blk k, blk_mem_honest k, rfl, fun X hX => ?_⟩
    obtain ⟨a, ha, rfl, -⟩ := anc_blk_inv honest_onChain hX
    rcases a with _ | a
    · exact Or.inl blk_root_zero
    · obtain ⟨fg'', e'', hl'', -⟩ := vote_label a
      refine Or.inr ⟨8 * (4 * (a + 1)) + 3, ⟨_, Compose.projAC_callAt.2 ⟨rfl, hl''⟩, rfl⟩, ?_⟩
      rw [time_eq, ts_nat]
      change (((8 * (4 * (a + 1)) + 3) / 8 : Nat) : Int) < 4 * (k : Int) + 3 * 1
      omega
  · intro v hv
    obtain rfl := hCV v hv
    exact Or.inl ⟨hx, readPoint_stamp hcast hx⟩

/-- `f < h_t` at every time `t ≥ 0` (no faulty validator, the validator awake and joined). -/
theorem tickRun_faultBound {t : Time} (ht : 0 ≤ t) :
    (tickRun N1 dg1).FaultBound Set.univ t := by
  unfold RunTrace.FaultBound RunTrace.honestAwakeJoined
  have : {y | y ∈ (Set.univ : Set (Fin sp1.n)) ∧ (tickRun N1 dg1).awake y t ∧
      (tickRun N1 dg1).JoinedAt y t} = Set.univ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and, iff_true]
    exact ⟨ht, fun k hk => absurd hk (tickRun_no_restart _ k)⟩
  rw [this, Set.compl_univ, Set.ncard_empty, Set.ncard_univ]
  simp

/-! ## `Sleepy` on the tick run -/

/-- (a) **`Sleepy` holds on the tick run** (with `Δ_F = 1`): `Sync[0, ∞)` and `f < h_t` at every
`t_s`, `t_s + Δ` and `t_s + 2Δ`. -/
theorem tickRun_sleepy : (tickRun N1 dg1).SleepyRun Set.univ 1 := by
  refine ⟨tickRun_syncOn _ _ id (fun _ => le_rfl), fun s =>
    ⟨tickRun_faultBound ?_, tickRun_faultBound ?_, tickRun_faultBound ?_⟩⟩
  · change (0 : Int) ≤ 4 * (s : Int); positivity
  · change (0 : Int) ≤ 4 * (s : Int) + 1; positivity
  · change (0 : Int) ≤ 4 * (s : Int) + 2 * 1; positivity

end Consensus.Goldilocks.Witness.One

end
