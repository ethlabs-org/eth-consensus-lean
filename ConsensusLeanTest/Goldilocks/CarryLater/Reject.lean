module
public import ConsensusLeanTest.Goldilocks.CarryLater.Premises
@[expose] public section

/-! # The later-Carry run: `carryLater` is necessary

Kind (r), rejection: **premise necessity, not a counterexample**. In the rejection run of
`Goldilocks/CarryLater/Run` (`ctl = false`) every premise of `PersistPremises … a i₀ 6 8 B CV`
except `carryLater` holds (`run_premisesExceptCarryLater false`,
`Goldilocks/CarryLater/Premises`), and `carryLater` fails at both of its slots
(`rejection_not_carryLater`):

* `s' = 7`, at `c`'s slot-8 vote (`rejection_c_slot8`): `c` holds every honest slot-7 vote
  (`a7, b7, d7`, head `Y`, stamped `29 < 31`), but it never accepts `Y` (no `ac_on_block` cut of
  `c` names it: `c_no_Y`), so the head `Y` of `a7 ∈ S_7` is not accepted before `t_7 + 3 = 31`
  (`rejection_not_carry_seven`);
* `s' = 8`, at `c`'s slot-9 vote (`rejection_c_slot9`): the head `Y` of `a8 ∈ S_8` is not
  accepted before `t_8 + 3 = 35` (`rejection_not_carry_eight`).

The mechanism: `a, b, d` accepted `Y` before the window `[t_6, t_8 + Δ] = [24, 33]` (`a, b` at
`12`, `d` at `23`), so `Sync` owes no delivery of `Y` to `c`, which restarts at `25`; a vote that
names `Y` obliges nobody to deliver `Y`. The initial `Carry(6, CV, B)` quantifies only the
slot-7 votes, and `c`, not joined in slot `7`, first votes in slot `8`, so it says nothing about
`c` either. The negation runs through the membership `a7 ∈ honestVotes 7` (`a7_mem`), not through
`CV`.

The conclusion fails too: at `32` `c` holds no lock (`c_slot8_no_lock`), so its anchor is
genesis; `Y` is unresolved at `c`, so `B` gets no slot-7 support there, and `c` votes the
current-slot block `W`, which does not extend `B` (`rejection_c_votes_W`).
`carryLater_necessary` bundles the run, the other premises, the failing `carryLater`, the source
event and the failing conclusion; the corollary
`rejection_not_persistPremises` derives `¬ PersistPremises` from the proved
`recent_source_next_vote`.

Finite horizon: the run ends at `39`; the failing conclusion does not contradict the theorem (a
premise fails). -/

namespace Consensus.Goldilocks.Test.HalfCommittee.Later

open SA Fix ScheduleRun Compose
open Five (va vb vc vd vf H)

/-! ## `c` never accepts `Y` -/

/-- **No `ac_on_block` cut of `c` names `Y`** in the rejection run. -/
theorem c_no_Y : (rowsD false).all (DataRun.noAccD vc 3) = true := by
  decide +kernel

/-- `c` never accepts `Y` in the rejection run. -/
theorem c_not_accepted (T : Time) : ¬ AcceptedBefore (tr false).projAC vc (X.blk 3) T :=
  DataRun.not_accepted (runD false) (by decide) (by decide) c_no_Y T

/-- A vote of an honest node on data is an honest vote of its slot. -/
theorem honestVote_of {ctl : Bool} {y : Fin 5} (hy : y ≠ vf) {v : X.V}
    (h : DataRun.voteAnyD (dataD ctl) y (fun em => decide (em.vote = v)) = true) :
    v ∈ honestVotes (tr ctl) H v.slot := by
  obtain ⟨k, em, hv, hP⟩ := DataRun.voteAny_spec (runD ctl) h
  exact ⟨y, hy, k, em.interp, hv, of_decide_eq_true hP, rfl⟩

/-- `a7` is an honest vote of slot `7`. -/
theorem a7_mem : vt va 7 3 ∈ honestVotes (tr false) H 7 :=
  honestVote_of (show va ≠ vf by decide) (checks_true false).2.2.1

/-- `a8` is an honest vote of slot `8`. -/
theorem a8_mem : vt va 8 3 ∈ honestVotes (tr false) H 8 :=
  honestVote_of (show va ≠ vf by decide) (checks_true false).2.2.2.1

/-- **`c` holds no lock at its slot-8 vote** in the rejection run. -/
theorem c_slot8_no_lock : DataRun.voteAnyD (dataD false) vc
    (fun em => decide (em.vote = vt vc 8 4) && em.rp.locks.isEmpty) = true := by
  decide +kernel

/-! ## The failure of `carryLater` and of the conclusion -/

/-- **`c`'s slot-8 vote in the rejection run**: head `W`; at its read point `c` holds every
honest slot-7 vote received before `t_7 + 3 = 31` (`holds`), but it never accepted `Y`. -/
theorem rejection_c_slot8 : ∃ k e, SA.VoteAt (tr false).projAC vc k e ∧ e.msg = vt vc 8 4 ∧
    (∀ v ∈ honestVotes (tr false) H 7, SA.HeldBefore e.readPoint v 31) ∧
    ¬ AcceptedBefore (tr false).projAC vc (X.blk 3) 31 := by
  obtain ⟨k, em, hv, hP⟩ := DataRun.voteAny_spec (runD false) (checks_true false).2.2.2.2.1
  have hm : em.vote = vt vc 8 4 := of_decide_eq_true hP
  obtain ⟨r, hr, -, call, M, ems, hc, em', hem', he, hchk⟩ := voteAt_chk hv
  have hs : em'.vote.slot = 8 := by
    rw [show em'.vote = em.vote from (congrArg (fun e => e.msg) he).symm, hm]; rfl
  refine ⟨k, em.interp, hv, hm, fun v hvS => ?_, c_not_accepted 31⟩
  rw [he]
  exact DataRun.heldD_spec ((voteD_slot8 hchk hs).2.1 v (DataRun.mem_votesD (runD false) hvS)).2.1

/-- **`c`'s slot-9 vote in the rejection run**: `c` holds every honest slot-8 vote received
before `t_8 + 3 = 35`, but it never accepted `Y`. -/
theorem rejection_c_slot9 : ∃ k e, SA.VoteAt (tr false).projAC vc k e ∧ e.msg.slot = 9 ∧
    (∀ v ∈ honestVotes (tr false) H 8, SA.HeldBefore e.readPoint v 35) ∧
    ¬ AcceptedBefore (tr false).projAC vc (X.blk 3) 35 := by
  obtain ⟨k, em, hv, hP⟩ := DataRun.voteAny_spec (runD false) (checks_true false).2.2.2.2.2.1
  have hm : em.vote.slot = 9 := by
    simp only [cVote9, Bool.not_false, Bool.true_or, Bool.and_true, decide_eq_true_eq] at hP
    exact hP.2
  obtain ⟨r, hr, -, call, M, ems, hc, em', hem', he, hchk⟩ := voteAt_chk hv
  have hs : em'.vote.slot = 9 := by
    rw [show em'.vote = em.vote from (congrArg (fun e => e.msg) he).symm, hm]
  refine ⟨k, em.interp, hv, hm, fun v hvS => ?_, c_not_accepted 35⟩
  rw [he]
  exact DataRun.heldD_spec ((voteD_slot9 hchk hs).2 v (DataRun.mem_votesD (runD false) hvS)).2.1

/-- A `Carry(σ, S_σ, B)` that holds at a vote of `c` would make `c` accept `Y` before
`t_σ + 3Δ`, if some honest slot-`σ` vote has head `Y`. -/
theorem c_accepts_of_carry {σ : Nat} {v : Vote 5} (hvS : v ∈ honestVotes (tr false) H σ)
    (hY : v.head = 3) {k : Nat} {e : SA.Em X.sp (List (FG.Att X.sp.n))}
    (hv : SA.VoteAt (tr false).projAC vc k e) (hs : e.msg.slot = σ + 1)
    (h : SA.Carry (tr false).projAC H ((tr false).HonestBlocks H) σ
      (honestVotes (tr false) H σ)) :
    AcceptedBefore (tr false).projAC vc (X.blk 3) (X.sp.ts σ + 3 * X.sp.Δ) := by
  obtain ⟨Hv, hU, hroot, hacc⟩ := (h vc (show vc ≠ vf by decide) k e hv hs).heads v hvS
  obtain ⟨r, hr, rfl⟩ := DataRun.honest_sub (runD false) frag_rows hU
  have hr3 : r = 3 := by rw [← blk_root (DataRun.mem_allR.1 hr), hroot, hY]
  subst hr3
  exact hacc _ .refl

/-- **`Carry(7, S_7, B)` fails in the rejection run**, at `c`'s slot-8 vote: the only honest
block with root `Y` is `Y` itself (`Anc.refl`), which `c` never accepts. -/
theorem rejection_not_carry_seven :
    ¬ SA.Carry (tr false).projAC H ((tr false).HonestBlocks H) 7 (honestVotes (tr false) H 7) := by
  intro h
  obtain ⟨k, e, hv, hm, -, hY⟩ := rejection_c_slot8
  exact hY (c_accepts_of_carry a7_mem rfl hv (by rw [hm]; rfl) h)

/-- **`Carry(8, S_8, B)` fails in the rejection run**, at `c`'s slot-9 vote. -/
theorem rejection_not_carry_eight :
    ¬ SA.Carry (tr false).projAC H ((tr false).HonestBlocks H) 8 (honestVotes (tr false) H 8) := by
  intro h
  obtain ⟨k, e, hv, hs, -, hY⟩ := rejection_c_slot9
  exact hY (c_accepts_of_carry a8_mem rfl hv hs h)

/-- **(ii) `carryLater` fails in the rejection run** (at both slots `s' = 7, 8`). -/
theorem rejection_not_carryLater : ¬ CarryLaterHolds (tr false) H 6 8 :=
  fun h => rejection_not_carry_seven (h 7 (by decide) (by decide))

/-- **(iii) `c` votes `W` in slot `8`** in the rejection run: the vote does not extend `B`. -/
theorem rejection_c_votes_W : ∃ k e, SA.VoteAt (tr false).projAC vc k e ∧ e.msg.slot = 8 ∧
    e.msg.head = 4 ∧ ¬ SA.VoteExtends ((tr false).HonestBlocks H) e.msg Bk := by
  obtain ⟨k, e, hv, hm, -⟩ := rejection_c_slot8
  refine ⟨k, e, hv, by rw [hm]; rfl, by rw [hm]; rfl, ?_⟩
  exact DataRun.not_extends (runD false) hX frag_rows (Or.inr (by decide))
    (by rw [hm]; decide)

/-- **(r) `carryLater` is necessary in `RecentSourceNextVote`**: a Goldilocks run with every
other premise of `PersistPremises` (`PersistPremisesExceptCarryLater`) for the fast lock of slot
`j = 6` on `B` written by `a` at `i₀`, `ac_to_fg` returning `B` at `i` in slot `m = 7`
(`j ≤ m ≤ j + 2`), `carryLater` false, and an honest vote of slot `m + 1` that does not extend
`B`. -/
theorem carryLater_necessary :
    ∃ (tr' : GoldilocksTrace X.sp ro) (i₀ i : Nat) (ℓ : ACLabel (goldilocksNode X.sp ro)),
      GoldilocksRun proposer dg H tr' ∧
      PersistPremisesExceptCarryLater tr' H dg 1 va i₀ 6 (7 + 1) Bk CV ∧
      ¬ CarryLaterHolds tr' H 6 (7 + 1) ∧ SA.ToFGAt tr'.projAC va i ℓ Bk ∧
      X.sp.slot (tr'.time i) = 7 ∧ 6 ≤ 7 ∧ 7 ≤ 6 + 2 ∧
      ∃ y ∈ H, ∃ k e, SA.VoteAt tr'.projAC y k e ∧ e.msg.slot = 7 + 1 ∧
        ¬ SA.VoteExtends (tr'.HonestBlocks H) e.msg Bk := by
  obtain ⟨ℓ, htf, hsl⟩ := (source false).2.2
  obtain ⟨k, e, hv, hs, -, hne⟩ := rejection_c_votes_W
  exact ⟨tr false, i0 false, i0 false + 1, ℓ, run_goldilocksRun false,
    run_premisesExceptCarryLater false, rejection_not_carryLater, htf, hsl, by decide, by decide,
    vc, show vc ≠ vf by decide, k, e, hv, hs, hne⟩

/-- **The corollary**: by the proved `recent_source_next_vote`, the premises `PersistPremises`
fail in the rejection run (this is premise necessity, not a counterexample to the theorem). -/
theorem rejection_not_persistPremises :
    ¬ PersistPremises (tr false) H dg 1 va (i0 false) 6 8 Bk CV := by
  intro hp
  obtain ⟨ℓ, htf, hsl⟩ := (source false).2.2
  obtain ⟨k, e, hv, hs, -, hne⟩ := rejection_c_votes_W
  exact hne (recent_source_next_vote X.sp ro dg H (tr false) 1 va (i0 false) (i0 false + 1) 6 7 ℓ
    Bk CV proposer (run_goldilocksRun false) hp htf hsl (by decide) (by decide) vc
    (show vc ≠ vf by decide) k e hv hs)

end Consensus.Goldilocks.Test.HalfCommittee.Later

end
