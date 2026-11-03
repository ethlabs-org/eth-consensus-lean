module
public import ConsensusLeanTest.GoldilocksInitialCarryPremises
@[expose] public section

/-! # The Initial-Carry run: the initial `Carry` is necessary

Kind (r), rejection: **premise necessity, not a counterexample**. In the rejection run of
`GoldilocksInitialCarryRun` (`ctl = false`) every premise of `PersistPremises … a i₀ 6 8 B CV`
except the initial `Carry(6, CV, B)` holds (`run_premisesExceptCarry false`,
`GoldilocksInitialCarryPremises`), and `Carry` fails at `c`'s slot-7 vote
(`rejection_not_carry`): `c` holds the counted votes `f6, a6, b6` received before `27`
(`holds` is true), but it never accepts `Da` or `Db` (no `ac_on_block` cut of `c` names them:
`c_no_heads`, `acceptAt_row`), so the head `Da` of `a6` (and `Db` of `b6`) is not accepted
before `27` (`heads` is false; `rejection_c_slot7`). The conclusion fails too: `c` votes `V` in
every slot, keeps its slow lock `(V, 4, slow, 8)`, and at `33` (slot `8`) its unlock against
the opponents `{a7, b7}` (`2 · 2 < 5`) keeps it on `V`, so `c` votes `V`, which does not extend
`B` (`rejection_c_votes_V`). `carry_necessary` bundles the run, the other premises, the failing
`Carry`, the source event and the failing conclusion; the corollary
`rejection_not_persistPremises` derives `¬ PersistPremises` from the proved
`recent_source_next_vote`.

Finite horizon (as in stage 2): the run ends at `35`, `carryLater` at `s' = 8` is vacuous, and
the failing conclusion does not contradict the theorem (a premise fails).

Duplication: `rejection_c_votes_V`, `carry_necessary` and `rejection_not_persistPremises`
parallel the rejection part of `GoldilocksHalfCommitteePremises` (`rejection_c_votes_V`,
`halfCommittee_necessary`, `rejection_not_persistPremises`), written for the new table;
`acceptAt_row` and the negation of `heads` have no stage-2 counterpart. -/

namespace Consensus.Goldilocks.Test.HalfCommittee.Heads

open SA Fix ScheduleRun Compose
open Five (va vb vc vd vf H)

/-! ## `c` never accepts `Da` or `Db` -/

/-- An `ac_on_block` cut names neither `Da` nor `Db` (by root). -/
def noHeadD (r : RowD) : Bool :=
  match r.cut with
  | .ac (.block b) _ _ => (X.blk b).root != 4 && (X.blk b).root != 5
  | _ => true

/-- **No `ac_on_block` cut of `c` names `Da` or `Db`** in the rejection run. -/
theorem c_no_heads : (rowsD false).all (fun r => r.node != vc || noHeadD r) = true := by
  decide +kernel

/-- **An acceptance of the AC projection is an `ac_on_block` row.** -/
theorem acceptAt_row {ctl : Bool} {y : Fin 5} {k : Nat} {B : X.Blk}
    (h : (tr ctl).projAC.AcceptAt y k B) :
    ∃ r, (rowsD ctl)[k]? = some r ∧ r.node = y ∧
      ∃ b M ems, r.cut = .ac (.block b) M ems ∧ B = X.blk b := by
  obtain ⟨ℓ, hc, hcall⟩ := h
  obtain ⟨r, hr, hn, call, M, ems, hcut, rfl⟩ := acRow hc
  refine ⟨r, hr, hn, ?_⟩
  cases call with
  | block b =>
    exact ⟨b, M, ems, hcut, by simpa [CallD.interp] using hcall.symm⟩
  | _ => simp [CallD.interp] at hcall

/-- `c` never accepts `Da` or `Db` in the rejection run. -/
theorem c_not_accepted {h : Nat} (hh : h = 4 ∨ h = 5) (T : Time) :
    ¬ AcceptedBefore (tr false).projAC vc (X.blk h) T := by
  have hroot : (X.blk h).root = h := blk_root (by rcases hh with rfl | rfl <;> decide)
  rintro (hg | ⟨k, hk, -⟩)
  · rw [hroot] at hg
    change h = 2 at hg
    omega
  · obtain ⟨r, hr, hn, b, M, ems, hcut, hb⟩ := acceptAt_row hk
    have hrb : (X.blk b).root = h := by rw [← hb]; exact hroot
    have := List.all_eq_true.1 c_no_heads r (List.mem_of_getElem? hr)
    simp only [hn, bne_self_eq_false, Bool.false_or, noHeadD, hcut, hrb, Bool.and_eq_true,
      bne_iff_ne, ne_eq] at this
    omega

/-! ## The failure of the initial `Carry` and of the conclusion -/

/-- **`c`'s slot-7 vote in the rejection run**: head `V`; at its read point `c` holds every
counted vote received before `t_6 + 3 = 27` (`holds`), but it accepted neither `Da` nor `Db`
before `27` (the `heads` of `a6` and `b6` fail). -/
theorem rejection_c_slot7 : ∃ k e, SA.VoteAt (tr false).projAC vc k e ∧ e.msg.slot = 7 ∧
    e.msg.head = 3 ∧ (∀ v ∈ CV, SA.HeldBefore e.readPoint v 27) ∧
    ¬ AcceptedBefore (tr false).projAC vc (X.blk 4) 27 ∧
    ¬ AcceptedBefore (tr false).projAC vc (X.blk 5) 27 := by
  obtain ⟨k, em, hv, hm, -⟩ := voteRow_spec (checks_true false).2.2.1
  obtain ⟨r, hr, -, call, M, ems, hc, em', hem', he, hchk, -⟩ := voteAt_row hv
  have hvv : em'.vote = em.vote := (congrArg (fun e => e.msg) he).symm
  have hs : em'.vote.slot = 7 := by rw [hvv, hm]; rfl
  refine ⟨k, em.interp, hv, by change em.vote.slot = 7; rw [hm]; rfl,
    by change em.vote.head = 3; rw [hm]; rfl, fun v hvS => ?_,
    c_not_accepted (Or.inl rfl) 27, c_not_accepted (Or.inr rfl) 27⟩
  rw [he]
  exact heldD_spec ((voteD_slot7 hchk hs).2.1 v hvS)

/-- **(ii) The initial `Carry(6, CV, B)` fails in the rejection run**, at `c`'s slot-7 vote: the
only honest block with root `Da` is `Da` itself (`Anc.refl`), which `c` never accepts. -/
theorem rejection_not_carry : ¬ CarryHolds (tr false) H 6 CV := by
  intro h
  obtain ⟨k, e, hv, hs, -, -, hDa, -⟩ := rejection_c_slot7
  obtain ⟨Hv, hU, hroot, hacc⟩ :=
    (h vc (show vc ≠ vf by decide) k e hv hs).heads (vt va 6 4) (show vt va 6 4 ∈ cvL by decide)
  obtain ⟨r, hr, rfl⟩ := honest_sub hU
  have hr4 : r = 4 := by rw [← blk_root (allR_closed.valid r hr)]; exact hroot
  subst hr4
  exact hDa (hacc _ .refl)

/-- **(iii) `c` votes `V` in slot `8`** in the rejection run, with its lock `(V, 4, slow, 8)` at
the read point (kept by the unlock: opponents `{a, b}`, `2 · 2 < 5`): the vote does not extend
`B`. -/
theorem rejection_c_votes_V : ∃ k e, SA.VoteAt (tr false).projAC vc k e ∧ e.msg.slot = 8 ∧
    e.msg.head = 3 ∧ (⟨3, 4, false, 8⟩ : Lock) ∈ e.readPoint.locks ∧
    ¬ SA.VoteExtends ((tr false).HonestBlocks H) e.msg Bk := by
  obtain ⟨k, em, hv, hm, hl⟩ := voteRow_spec (checks_true false).2.2.2.1
  simp only [lockV, Bool.false_or, decide_eq_true_eq] at hl
  exact ⟨k, em.interp, hv, by change em.vote.slot = 8; rw [hm]; rfl,
    by change em.vote.head = 3; rw [hm]; rfl, hl,
    not_extends_V false (by change em.vote.head = 3; rw [hm]; rfl)⟩

/-- **(r) The initial `Carry` is necessary in `RecentSourceNextVote`**: a Goldilocks run with
every other premise of `PersistPremises` (`PersistPremisesExceptCarry`) for the fast lock of slot
`j = 6` on `B` written by `a` at `i₀`, `ac_to_fg` returning `B` at `i` in slot `m = 7`
(`j ≤ m ≤ j + 2`), the initial `Carry` false, and an honest vote of slot `m + 1` that does not
extend `B`. -/
theorem carry_necessary :
    ∃ (tr' : GoldilocksTrace X.sp ro) (i₀ i : Nat) (ℓ : ACLabel (goldilocksNode X.sp ro)),
      GoldilocksRun proposer dg H tr' ∧
      PersistPremisesExceptCarry tr' H dg 1 va i₀ 6 (7 + 1) Bk CV ∧
      ¬ CarryHolds tr' H 6 CV ∧ SA.ToFGAt tr'.projAC va i ℓ Bk ∧
      X.sp.slot (tr'.time i) = 7 ∧ 6 ≤ 7 ∧ 7 ≤ 6 + 2 ∧
      ∃ y ∈ H, ∃ k e, SA.VoteAt tr'.projAC y k e ∧ e.msg.slot = 7 + 1 ∧
        ¬ SA.VoteExtends (tr'.HonestBlocks H) e.msg Bk := by
  obtain ⟨ℓ, htf, hsl⟩ := (source false).2.2
  obtain ⟨k, e, hv, hs, -, -, hne⟩ := rejection_c_votes_V
  exact ⟨tr false, i0 false, i0 false + 1, ℓ, run_goldilocksRun false,
    run_premisesExceptCarry false, rejection_not_carry, htf, hsl, by decide, by decide, vc,
    show vc ≠ vf by decide, k, e, hv, hs, hne⟩

/-- **The corollary**: by the proved `recent_source_next_vote`, the premises `PersistPremises`
fail in the rejection run (this is premise necessity, not a counterexample to the theorem). -/
theorem rejection_not_persistPremises :
    ¬ PersistPremises (tr false) H dg 1 va (i0 false) 6 8 Bk CV := by
  intro hp
  obtain ⟨ℓ, htf, hsl⟩ := (source false).2.2
  obtain ⟨k, e, hv, hs, -, -, hne⟩ := rejection_c_votes_V
  exact hne (recent_source_next_vote X.sp ro dg H (tr false) 1 va (i0 false) (i0 false + 1) 6 7 ℓ
    Bk CV proposer (run_goldilocksRun false) hp htf hsl (by decide) (by decide) vc
    (show vc ≠ vf by decide) k e hv hs)

end Consensus.Goldilocks.Test.HalfCommittee.Heads

end
