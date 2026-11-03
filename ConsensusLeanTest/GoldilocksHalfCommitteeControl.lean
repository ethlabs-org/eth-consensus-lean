module
public import ConsensusLeanTest.GoldilocksHalfCommitteePremises
@[expose] public section

/-! # The halfCommittee run: the control with the full premises

Kind (control). The control run of `GoldilocksHalfCommitteeRun` (`ctl = true`) differs from the
rejection run only in `d`: it wakes and restarts at `24`, joins in slot `7` and votes `B` in
slots `7` and `8` (and signs at `30`). The source and every other premise are those of
`run_premisesExceptHalf true`; now `halfCommittee` holds too (`control_halfCommittee`: the honest
voters of slots `7` and `8` include `a, b, d`, and `5 ≤ 2 · 3`), so the full `PersistPremises`
holds (`control_persistPremises`), and the proved `recent_source_next_vote` applies: every
honest vote of slot `8` extends `B` (`control_next_votes_extend`). In particular `c`, which
votes `V` in the rejection run, now votes `B`: the opponents `{a7, b7, d7}` of its lock
`(V, 4, slow, 8)` reach `2 · 3 ≥ 5`, the unlock moves the lock to genesis (`(G, 4, slow, 8)`), and
its walk from genesis picks `B` (`control_c_votes_B`). -/

namespace Consensus.Goldilocks.Test.HalfCommittee.Five

open SA Fix ScheduleRun Compose

/-- **`halfCommittee` holds in the control**: the honest voters of slots `7` and `8` include
`a, b, d`. -/
theorem control_halfCommittee : HalfCommitteeHolds (tr true) H 6 8 := by
  intro s' h1 h2
  rw [voters_eq]
  have hsub : ({va, vb, vd} : Set (Fin 5)) ⊆ {x' | x' ∈ votersD true s'} := by
    have hs : s' = 7 ∨ s' = 8 := by omega
    have hL : [va, vb, vd] ⊆ votersD true s' := by
      rcases hs with rfl | rfl
      · exact voters_checks.2.1
      · exact voters_checks.2.2
    rintro y (rfl | rfl | rfl)
    · exact hL (by decide)
    · exact hL (by decide)
    · exact hL (by decide)
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem (by decide), Set.ncard_pair (by decide)] at this
  change 5 ≤ _
  omega

/-- **The full premises of `RecentSourceNextVote` in the control.** -/
theorem control_persistPremises :
    PersistPremises (tr true) H dg 1 va (i0 true) 6 8 Bk CV :=
  persistPremises_iff.2 ⟨run_premisesExceptHalf true, control_halfCommittee⟩

/-- **The proved theorem applied**: in the control, every honest vote of slot `8` extends `B`. -/
theorem control_next_votes_extend : ∀ y ∈ H, ∀ k e, SA.VoteAt (tr true).projAC y k e →
    e.msg.slot = 8 → SA.VoteExtends ((tr true).HonestBlocks H) e.msg Bk := by
  obtain ⟨ℓ, htf, hsl⟩ := (source true).2.2
  exact recent_source_next_vote X.sp ro dg H (tr true) 1 va (i0 true) (i0 true + 1) 6 7 ℓ Bk CV
    proposer (run_goldilocksRun true) control_persistPremises htf hsl (by decide) (by decide)

/-- **`c` votes `B` in slot `8` in the control**, its lock unlocked to `(G, 4, slow, 8)` at its
read point; the vote extends `B`, as the theorem says. -/
theorem control_c_votes_B : ∃ k e, SA.VoteAt (tr true).projAC vc k e ∧ e.msg.slot = 8 ∧
    e.msg.head = 1 ∧ (⟨2, 4, false, 8⟩ : Lock) ∈ e.readPoint.locks ∧
    SA.VoteExtends ((tr true).HonestBlocks H) e.msg Bk := by
  obtain ⟨k, e, hv, hm, hl⟩ := cVote_row true
  refine ⟨k, e, hv, by rw [hm]; rfl, by rw [hm]; rfl, hl, ?_⟩
  exact control_next_votes_extend vc (show vc ≠ vf by decide) k e hv (by rw [hm]; rfl)

end Consensus.Goldilocks.Test.HalfCommittee.Five

end
