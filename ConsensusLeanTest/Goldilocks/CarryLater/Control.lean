module
public import ConsensusLeanTest.Goldilocks.CarryLater.Premises
@[expose] public section

/-! # The later-Carry run: the control with the full premises

Kind (control). The control run of `Goldilocks/CarryLater/Run` (`ctl = true`) differs from the
rejection run in the deliveries `Y → c` at `25` (with `Y` re-served to `a, b, d` there, which
`Sync` then asks for) and `c`'s attestation to `a, b, d` at `33` (its `ac_to_fg` returns `B`
too): `c` accepts `Y` at `25` (`control_c_accepts_Y`). Now `carryLater` holds
(`control_carryLater`): at every honest vote of slot `8`, the voter holds every honest slot-7
vote received before `t_7 + 3 = 31` and accepted its head chain `Y → B → G` before `31`; at
every honest vote of slot `9`, the same for the slot-8 votes before `t_8 + 3 = 35`. With
`run_premisesExceptCarryLater true` the full `PersistPremises` holds
(`control_persistPremises`, by `persistPremises_iff_carryLater`), and the proved
`recent_source_next_vote` applies: every honest vote of slot `8` extends `B`
(`control_next_votes_extend`). In particular `c`, which votes `W` in the rejection run, votes `Y`
in slots `8` and `9` (`control_c_votes_Y`).

Finite horizon: the run ends at `39`; both instances of `carryLater` (`s' = 7, 8`) are checked
at existing votes. -/

namespace Consensus.Goldilocks.Test.HalfCommittee.Later

open SA Fix ScheduleRun Compose
open Five (va vb vc vd vf H)

theorem accR_c : DataRun.accR (dataD true) vc 3 26 = true := by
  decide +kernel

/-- **`c` accepts `Y` at `25` in the control.** -/
theorem control_c_accepts_Y : AcceptedBefore (tr true).projAC vc (X.blk 3) 26 :=
  DataRun.accR_spec (runD true) (by decide) accR_c

/-- **(iv) `carryLater` holds in the control**: `Carry(7, S_7, B)` and `Carry(8, S_8, B)`. -/
theorem control_carryLater : CarryLaterHolds (tr true) H 6 8 :=
  fun s' h1 h2 => carry_of_checks rfl (by omega)

/-- **The full premises of `RecentSourceNextVote` in the control.** -/
theorem control_persistPremises :
    PersistPremises (tr true) H dg 1 va (i0 true) 6 8 Bk CV :=
  persistPremises_iff_carryLater.2 ⟨run_premisesExceptCarryLater true, control_carryLater⟩

/-- **The proved theorem applied**: in the control, every honest vote of slot `8` extends `B`. -/
theorem control_next_votes_extend : ∀ y ∈ H, ∀ k e, SA.VoteAt (tr true).projAC y k e →
    e.msg.slot = 8 → SA.VoteExtends ((tr true).HonestBlocks H) e.msg Bk := by
  obtain ⟨ℓ, htf, hsl⟩ := (source true).2.2
  exact recent_source_next_vote X.sp ro dg H (tr true) 1 va (i0 true) (i0 true + 1) 6 7 ℓ Bk CV
    proposer (run_goldilocksRun true) control_persistPremises htf hsl (by decide) (by decide)

/-- **`c` votes `Y` in slots `8` and `9` in the control**; both votes extend `B` (the slot-8 one
by the theorem, the slot-9 one by `Y`'s chain `Y → B → G`). -/
theorem control_c_votes_Y :
    (∃ k e, SA.VoteAt (tr true).projAC vc k e ∧ e.msg = vt vc 8 3 ∧
      SA.VoteExtends ((tr true).HonestBlocks H) e.msg Bk) ∧
    ∃ k e, SA.VoteAt (tr true).projAC vc k e ∧ e.msg = vt vc 9 3 ∧
      SA.VoteExtends ((tr true).HonestBlocks H) e.msg Bk := by
  obtain ⟨k₈, em₈, hv₈, hP₈⟩ := DataRun.voteAny_spec (runD true) (checks_true true).2.2.2.2.1
  obtain ⟨k₉, em₉, hv₉, hP₉⟩ := DataRun.voteAny_spec (runD true) (checks_true true).2.2.2.2.2.1
  have hm₈ : em₈.vote = vt vc 8 3 := of_decide_eq_true hP₈
  have hm₉ : em₉.vote = vt vc 9 3 := by
    simp only [cVote9, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hP₉
    obtain ⟨⟨h1, h2⟩, h3⟩ := hP₉
    cases hv : em₉.vote
    rw [hv] at h1 h2 h3
    subst h1 h2 h3
    rfl
  refine ⟨⟨k₈, em₈.interp, hv₈, hm₈, ?_⟩, k₉, em₉.interp, hv₉, hm₉, ?_⟩
  · exact control_next_votes_extend vc (show vc ≠ vf by decide) k₈ _ hv₈
      (by change em₈.vote.slot = 8; rw [hm₈]; rfl)
  · change SA.VoteExtends _ em₉.vote Bk
    rw [hm₉]
    exact DataRun.extends_of_chain hX (valid_honest true) (by decide) (by decide)

end Consensus.Goldilocks.Test.HalfCommittee.Later

end
