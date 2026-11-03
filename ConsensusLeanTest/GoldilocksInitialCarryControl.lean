module
public import ConsensusLeanTest.GoldilocksInitialCarryPremises
@[expose] public section

/-! # The Initial-Carry run: the control with the full premises

Kind (control). The control run of `GoldilocksInitialCarryRun` (`ctl = true`) differs from the
rejection run in the deliveries `Da, Db → c` at `23` (and `c`'s attestation at `30`: its
`ac_to_fg` returns `B` there too): `c` accepts both at `23` (`control_c_accepts`). Now the
initial `Carry(6, CV, B)` holds (`control_carry`: every slot-7
voter `a, b, c` accepted the head chains `Da → B → G`, `Db → B → G`, `B → G` before
`t_6 + 3 = 27` and holds `f6, a6, b6` received before `27`); with `run_premisesExceptCarry true`
the full `PersistPremises` holds (`control_persistPremises`, by `persistPremises_iff_carry`), and
the proved `recent_source_next_vote` applies: every honest vote of slot `8` extends `B`
(`control_next_votes_extend`). In particular `c`, which votes `V` in the rejection run, votes `B`
in slots `7` and `8` (`control_c_votes_B`).

Finite horizon (as in stage 2): the run ends at `35`; `carryLater` at `s' = 8` is vacuous.

Duplication: this parallels `GoldilocksHalfCommitteeControl` (the stage-2 control for
`halfCommittee`), written for the new table and the dropped field `carry`. -/

namespace Consensus.Goldilocks.Test.HalfCommittee.Heads

open SA Fix ScheduleRun Compose
open Five (va vb vc vd vf H)

theorem accR_c : accR true vc 4 24 = true ∧ accR true vc 5 24 = true := by decide +kernel

/-- **`c` accepts `Da` and `Db` at `23` in the control.** -/
theorem control_c_accepts : AcceptedBefore (tr true).projAC vc (X.blk 4) 24 ∧
    AcceptedBefore (tr true).projAC vc (X.blk 5) 24 :=
  ⟨accR_spec (by decide) accR_c.1, accR_spec (by decide) accR_c.2⟩

theorem cvL_heads : ∀ v ∈ cvL, v.head ∈ allR := by decide

/-- **(iv) The initial `Carry(6, CV, B)` holds in the control.** -/
theorem control_carry : CarryHolds (tr true) H 6 CV := by
  intro y hy i e hv hs
  obtain ⟨r, hr, hn, call, M, ems, hc, em, hem, rfl, hchk, -⟩ := voteAt_row hv
  obtain ⟨hj, hheld, hacc, -⟩ := voteD_slot7 hchk hs
  refine carryAt_mk hy hv rfl CV (joined_row hr hj) fun v hvS => ?_
  exact ⟨cvL_heads v hvS, hn ▸ hacc rfl v hvS, heldD_spec (hheld v hvS)⟩

/-- **The full premises of `RecentSourceNextVote` in the control.** -/
theorem control_persistPremises :
    PersistPremises (tr true) H dg 1 va (i0 true) 6 8 Bk CV :=
  persistPremises_iff_carry.2 ⟨run_premisesExceptCarry true, control_carry⟩

/-- **The proved theorem applied**: in the control, every honest vote of slot `8` extends `B`. -/
theorem control_next_votes_extend : ∀ y ∈ H, ∀ k e, SA.VoteAt (tr true).projAC y k e →
    e.msg.slot = 8 → SA.VoteExtends ((tr true).HonestBlocks H) e.msg Bk := by
  obtain ⟨ℓ, htf, hsl⟩ := (source true).2.2
  exact recent_source_next_vote X.sp ro dg H (tr true) 1 va (i0 true) (i0 true + 1) 6 7 ℓ Bk CV
    proposer (run_goldilocksRun true) control_persistPremises htf hsl (by decide) (by decide)

/-- **`c` votes `B` in slots `7` and `8` in the control**; both votes extend `B` (the slot-8 one
by the theorem). -/
theorem control_c_votes_B :
    (∃ k e, SA.VoteAt (tr true).projAC vc k e ∧ e.msg = vt vc 7 1 ∧
      SA.VoteExtends ((tr true).HonestBlocks H) e.msg Bk) ∧
    ∃ k e, SA.VoteAt (tr true).projAC vc k e ∧ e.msg = vt vc 8 1 ∧
      SA.VoteExtends ((tr true).HonestBlocks H) e.msg Bk := by
  obtain ⟨k₇, em₇, hv₇, hm₇, -⟩ := voteRow_spec (checks_true true).2.2.1
  obtain ⟨k₈, em₈, hv₈, hm₈, -⟩ := voteRow_spec (checks_true true).2.2.2.1
  refine ⟨⟨k₇, em₇.interp, hv₇, hm₇, ?_⟩, k₈, em₈.interp, hv₈, hm₈, ?_⟩
  · refine ⟨Bk, blk_honest true (by decide), ?_, .refl⟩
    change (X.blk 1).root = em₇.vote.head
    rw [hm₇]; rfl
  · exact control_next_votes_extend vc (show vc ≠ vf by decide) k₈ _ hv₈
      (by change em₈.vote.slot = 8; rw [hm₈]; rfl)

end Consensus.Goldilocks.Test.HalfCommittee.Heads

end
