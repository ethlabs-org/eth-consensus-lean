module
public import ConsensusLeanTest.Goldilocks.Regimes.Sleepy
public import ConsensusLeanTest.Goldilocks.Runs.TwoValidator.AC
public import ConsensusLean.Instances.Goldilocks.Results.Statements.OptimisticInclusion
@[expose] public section

/-! # The premises of optimistic inclusion on a concrete run, and a rejection test

**The premises hold** (CONTRIBUTING "Statements", kind (a)). On the one-validator tick run of
`Goldilocks/Runs/OneValidator/Premises` (`n = 1`, `Δ = 1`, `t_s = 4s`, a tick at every time
`t ≥ 0`, cut `i` at time `⌊i/8⌋`, no restart), read with the constant honest set and the full
committee as in `Regimes/Sleepy`, every premise of `Regimes.Growing.OptimisticInclusion` holds
together for the own block `blk p` of every slot `p ≥ 1`, the validator as reader and every
`t ≥ t_p + 2Δ` (`optimisticInclusion_premises`):

* the switch is on (the default of `ACParams.optimistic`);
* the run from the full committee's start, `NoColl`, the committee facts, `Sleepy` with look-ahead
  `ahead` and the committee support (`Regimes/Sleepy`, `Regimes/SleepyCommittee`);
* `blk p` is a ready proposal released at `t_p`, held through `t_p + Δ`;
* unanimity: every slot-`p` vote of the run is `cv p`, whose head is `blk p` (`emit_cases`);
* the committee premise: the one member is honest at `t_p + 2Δ`, awake and joined at `t_p + Δ`,
  and `3 · 1 ≤ 4 · 1`;
* the reader is awake and joined throughout `[t_p, t_p + 2Δ]` (no restart in the run), ready at
  `t`, with the first cut `8(t + 1)` after `t`.

With `n = 1` and `f = 0` this shows the premises consistent, not met with faults.

**Rejection** (kind (c)): with more than a quarter of the committee withholding, here one
validator of the two of `Runs/TwoValidator`, the optimistic confirmation has nothing to fire on.

* `optimistic_rejected_withholding`: a node whose slot pool holds the vote of one validator only
  writes no optimistic lock (`optimisticSelect = none`), at any frame and time.

**The switch** (kind (c)): `optimistic_switch_off_rejected` isolates it. On the two-validator
fixture's passing witness, a joined node before `t_s + 2Δ` with both slot-`s` votes on a chain
frame, the optimistic check selects the slot's block with the switch on (`optimisticSelect_two`)
and nothing at the same pool, frame and time with the switch off. -/

namespace Consensus.Goldilocks.Test.OptimisticInclusion

open AC Node Witness Witness.One ChainFrame

/-! ## The premises hold on the one-validator tick run -/

/-- Every slot-`p` vote of the tick run has the head `blk p`. -/
theorem tickRun_unanimous (p : Nat) :
    Healing.Unanimous (tickRun N1 dg1) Set.univ p (blk p) := by
  rintro x - j e ⟨ℓ, hc, he⟩ hs
  obtain ⟨-, -, hl⟩ := projAC_call hc
  rcases emit_cases hl he with ⟨-, hm, -⟩ | ⟨k, fg', -, -, -, -, hm, -⟩ <;>
  · rw [hm] at hs ⊢
    change _ = p at hs
    subst hs
    rfl

/-- The validator is joined at every time: the tick run has no restart. -/
theorem tickRun_joinedAt (y : Fin sp1.n) (t : Time) : (tickRun N1 dg1).JoinedAt y t :=
  fun k hk => absurd hk (tickRun_no_restart y k)

/-- The one member of the full committee is honest at every time, and awake and joined at every
time `t ≥ 0`. -/
theorem committee_ncard {p : Nat} {u t : Time} (ht : 0 ≤ t) :
    {x | x ∈ (CommitteeDict.full sp1.n).committee p ∧
      x ∈ (fun _ => (Set.univ : Set (Fin sp1.n))) u ∧
      (tickRun N1 dg1).awake x t ∧ (tickRun N1 dg1).JoinedAt x t}.ncard = 1 := by
  have : {x | x ∈ (CommitteeDict.full sp1.n).committee p ∧
      x ∈ (fun _ => (Set.univ : Set (Fin sp1.n))) u ∧
      (tickRun N1 dg1).awake x t ∧ (tickRun N1 dg1).JoinedAt x t} = Set.univ := by
    ext x
    exact iff_of_true ⟨Set.mem_univ _, Set.mem_univ _, ht, tickRun_joinedAt x t⟩
      (Set.mem_univ _)
  rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- (a) **The premises of optimistic inclusion hold together** on the tick run, for the own block
`blk p` of every slot `p ≥ 1`, the validator as reader and every `t ≥ t_p + 2Δ`, with the first
cut `8(t + 1)` after `t`. -/
theorem optimisticInclusion_premises (p t : Nat) (hp : 1 ≤ p) (ht : 4 * p + 2 ≤ t) :
    sp1.optimistic = true ∧
      Consensus.Goldilocks.Growing.GoldilocksRun (sp := sp1) (fun _ => v0) dg1
        (fun _ => Set.univ) (tickRun N1 dg1)
        (committeeStart sp1.genesisRoot (CommitteeDict.full sp1.n)) ∧
      Compose.NoCollRun dg1 (tickRun N1 dg1) ∧
      Compose.Growing.CommitteeFacts (tickRun N1 dg1) (fun _ => Set.univ)
        (CommitteeDict.full sp1.n) ∧
      (tickRun N1 dg1).SleepyRunAt (fun _ => Set.univ) 1 (Regimes.Growing.ahead sp1) ∧
      Regimes.Growing.CommitteeSleepy (tickRun N1 dg1) (fun _ => Set.univ)
        (CommitteeDict.full sp1.n) ∧
      Regimes.Growing.ReadyProposalAt (tickRun N1 dg1) (fun _ => Set.univ)
        (Regimes.catchUp sp1) (sp1.ts p) (Regimes.Growing.hold sp1) (blk p) ∧
      Healing.Unanimous (tickRun N1 dg1) ((fun _ => Set.univ) (sp1.ts p + sp1.Δ)) p (blk p) ∧
      3 * sp1.committeeSize ≤
        4 * {x | x ∈ (CommitteeDict.full sp1.n).committee p ∧
          x ∈ (fun _ => Set.univ) (sp1.ts p + 2 * sp1.Δ) ∧
          (tickRun N1 dg1).awake x (sp1.ts p + sp1.Δ) ∧
          (tickRun N1 dg1).JoinedAt x (sp1.ts p + sp1.Δ)}.ncard ∧
      sp1.ts p + 2 * sp1.Δ ≤ t ∧
      Regimes.Growing.ReadyAt (tickRun N1 dg1) (fun _ => Set.univ) (Regimes.catchUp sp1)
        v0 t ∧
      (∀ d, sp1.ts p ≤ d → d ≤ sp1.ts p + 2 * sp1.Δ →
        (tickRun N1 dg1).awake v0 d ∧ (tickRun N1 dg1).JoinedAt v0 d) ∧
      Regimes.CutAfter (tickRun N1 dg1) (8 * (t + 1)) t := by
  have hrun := Regimes.Growing.Test.run_full tickRun_growingRun
  have hnc := dg1_noColl (tickRun N1 dg1)
  have hts : sp1.ts p = ((4 * p : Nat) : Time) := ts_eq p
  have hts0 : (0 : Time) ≤ sp1.ts p := by rw [hts]; exact Int.natCast_nonneg _
  obtain ⟨q, kP, hq, hkP, hτP⟩ := tickRun_readyProposalAt (Regimes.catchUp sp1) p hp
  refine ⟨rfl, hrun, hnc, Compose.Growing.CommitteeFacts.of_full tickRun_growingRun hnc rfl,
    tickRun_sleepyAt, Regimes.Growing.Test.committeeSleepy_full tickRun_growingRun
      tickRun_sleepyAt,
    ⟨q, kP, ⟨Set.mem_univ _, hq.2⟩, Set.mem_univ _, hkP, hτP⟩, tickRun_unanimous p, ?_, ?_,
    ⟨Set.mem_univ _, fun _ h _ => (le_max_left _ _).trans h⟩,
    fun d hd _ => ⟨hts0.trans hd, tickRun_joinedAt v0 d⟩, tickRun_cutAfter t⟩
  · rw [committee_ncard (u := sp1.ts p + 2 * sp1.Δ)
      (hts0.trans (le_add_of_nonneg_right sp1.toParams.hΔ.le))]
    decide
  · rw [hts, delta1]
    change ((4 * p : Nat) : Int) + 2 * 1 ≤ (t : Int)
    omega

/-! ## Rejection above a quarter withholding -/

/-- **Rejection: one of two validators withholding locks nothing.** If the slot pool of a node
holds a single vote, the vote of the one validator that did not withhold, the optimistic check
selects no block. -/
theorem optimistic_rejected_withholding {A : ACState Witness.TwoRun.sp.n}
    {Φ : Witness.TwoRun.N.Frm} {t : Time} {v : Vote Witness.TwoRun.sp.n}
    (h : A.pool (Witness.TwoRun.sp.slot t) = [v]) :
    optimisticSelect Witness.TwoRun.sp A Φ t = none :=
  Witness.TwoRun.optimisticSelect_one h

/-- The two-validator fixture's parameters with the optimistic switch off. -/
abbrev spOff : ACParams := { Witness.TwoRun.sp with optimistic := false }

/-- **Rejection: the switch alone stops the optimistic confirmation.** At the two-validator
fixture's passing witness (a joined node in slot `s ≥ 1` before `t_s + 2Δ`, both slot-`s` votes
in its pool, a chain frame), the optimistic check selects the slot's block with the switch on and
nothing with the switch off, at the same pool, frame and time. -/
theorem optimistic_switch_off_rejected {Φ : Witness.TwoRun.N.Frm} {f j s : Nat}
    (h : Witness.TwoRun.ChainFrame Φ f j s) (hs : 1 ≤ s) {A : ACState Witness.TwoRun.sp.n}
    {t : Time} (hst : Witness.TwoRun.sp.slot t = s)
    (ht : t < Witness.TwoRun.sp.ts s + 2 * Witness.TwoRun.sp.Δ)
    (hjn : joined Witness.TwoRun.sp A t) {y : Fin Witness.TwoRun.sp.n}
    (hpool : A.pool s = [Witness.TwoRun.vote y s, Witness.TwoRun.vote (Witness.TwoRun.other y) s]) :
    optimisticSelect Witness.TwoRun.sp A Φ t = some (Witness.TwoRun.blk s) ∧
      optimisticSelect spOff A Φ t = none := by
  refine ⟨Witness.TwoRun.optimisticSelect_two h hs hst ht hjn hpool, ?_⟩
  unfold optimisticSelect
  exact ite_eq_left (Or.inr (Or.inr (Or.inr rfl)))

end Consensus.Goldilocks.Test.OptimisticInclusion

end
