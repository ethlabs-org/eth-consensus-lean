module
public import ConsensusLeanTest.Goldilocks.Persist.Premises
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Regimes.Inclusion
@[expose] public section

/-! # The one-validator tick run meets the premises of the sleepy rows R.1 and R.2

On the one-validator tick run of `Goldilocks/Runs/OneValidator/Premises` (`n = 1`, `Δ = 1`,
`t_s = 4s`, a tick at every time `t ≥ 0`, cut `i` at time `⌊i/8⌋`, no restart), with `Δ_F = 1` and
catch-up `c = 18Δ`:

* (a) `tickRun_readyAt`, `tickRun_readPoint`, `tickRun_cutAfter`, `tickRun_readyProposalAt`: the
  validator is ready at every time; `(8t, t)` is a read point between its events and `8(t + 1)`
  is the first cut after `t`, for every `t ∈ ℕ`; the own block `blk s` of slot `s ≥ 1` is a ready
  proposal released at `t_s` (cut `8·t_s + 2`).
* (a) `sleepySafe_premises`, `includeSleepy_premises`, `growSleepy_premises`: the premises of
  `SleepySafe`, `IncludeSleepy` and `GrowSleepy` (at `k = 1`, `ProposerRecurrence … 1 0 (t + 10Δ)`)
  hold together, with ready readers at these read points and cuts.
* (b) `tickRun_sleepySafe`: `sleepy_safe` at the reads `(8t, t)` and `(8t', t')`: compatible, and
  the earlier one an ancestor of the later one.
  `tickRun_includeSleepy`: `include_sleepy` puts `blk s` in the read after every `t ≥ t_s + 6Δ`.
  `tickRun_growSleepy`: `grow_sleepy` at `k = 1` yields a ready proposal `P` released after `t`
  that is in the read after `t + 10Δ` (cut `8(t + 11)`) and not in the read after `t` (cut
  `8(t + 1)`), the earlier read an ancestor of the later one.

With `n = 1` and `f = 0` this shows the premises consistent, not met with faults. -/

namespace Consensus.Goldilocks.Witness.One

open SA Node ChainFrame

/-! ## Ready readers, read points, cuts and proposals -/

/-- The validator is ready at every time, for every catch-up (it is awake at every `t ≥ 0`). -/
theorem tickRun_readyAt (c t : Time) (y : Fin sp1.n) :
    Regimes.ReadyAt (tickRun N1 dg1) Set.univ c y t :=
  ⟨Set.mem_univ _, fun _ h _ => (le_max_left _ _).trans h⟩

/-- `(8t, t)` is a read point (the state before the tick of `t`) between the validator's events. -/
theorem tickRun_readPoint (t : Nat) :
    Regimes.ReadPoint (tickRun N1 dg1) (8 * t) (t : Time) ∧
      Regimes.Boundary (tickRun N1 dg1) v0 (8 * t) := by
  refine ⟨⟨fun k hk => ?_, ?_⟩, fun _ => ?_⟩
  · change ((k / 8 : Nat) : Int) ≤ (t : Int); omega
  · change (t : Int) ≤ ((8 * t / 8 : Nat) : Int); omega
  · change 8 * t % 8 = 0; omega

/-- Cut `8(t + 1)` is the first cut after the time `t`. -/
theorem tickRun_cutAfter (t : Nat) : Regimes.CutAfter (tickRun N1 dg1) (8 * (t + 1)) (t : Time) :=
  ⟨fun k hk => by change ((k / 8 : Nat) : Int) ≤ (t : Int); omega,
    by change (t : Int) < ((8 * (t + 1) / 8 : Nat) : Int); omega⟩

/-- The own block of slot `s ≥ 1` is a ready proposal released at `t_s` (cut `8·t_s + 2`). -/
theorem tickRun_readyProposalAt (c : Time) (s : Nat) (hs : 1 ≤ s) :
    Regimes.ReadyProposalAt (tickRun N1 dg1) Set.univ c (sp1.ts s) (blk s) := by
  obtain ⟨k, B, hR, rfl⟩ := tickRun_readyProposal s hs
  obtain ⟨⟨acc, -, hl⟩, -⟩ := hR.2.2.2.1.1
  obtain ⟨s', -, -, rfl, -⟩ := blockCall_eq hl
  have : s' = s := by rw [← hR.2.2.2.2.1, blk_slot]
  subst this
  refine ⟨v0, _, tickRun_readyAt c _ v0, hR.2.2.2.1, ?_⟩
  rw [time_run, ts_eq]
  congr 1
  omega

/-! ## The premise bundles -/

/-- (a) **The premises of `SleepySafe`**: a Goldilocks run with `NoColl` and `Sleepy`, and the
validator ready at the read points `(8t, t)`, `(8t', t')` between its events. -/
theorem sleepySafe_premises (t t' : Nat) :
    GoldilocksRun (sp := sp1) (ro := ro1) (fun _ => v0) dg1 Set.univ (tickRun N1 dg1) ∧
      Compose.NoCollRun dg1 (tickRun N1 dg1) ∧ (tickRun N1 dg1).SleepyRun Set.univ 1 ∧
      Regimes.ReadPoint (tickRun N1 dg1) (8 * t) (t : Time) ∧
      Regimes.ReadPoint (tickRun N1 dg1) (8 * t') (t' : Time) ∧
      Regimes.Boundary (tickRun N1 dg1) v0 (8 * t) ∧
      Regimes.Boundary (tickRun N1 dg1) v0 (8 * t') ∧
      Regimes.ReadyAt (tickRun N1 dg1) Set.univ (Regimes.catchUp sp1) v0 t ∧
      Regimes.ReadyAt (tickRun N1 dg1) Set.univ (Regimes.catchUp sp1) v0 t' :=
  ⟨tickRun_goldilocksRun, dg1_noColl _, tickRun_sleepy, (tickRun_readPoint t).1,
    (tickRun_readPoint t').1, (tickRun_readPoint t).2, (tickRun_readPoint t').2,
    tickRun_readyAt _ _ _, tickRun_readyAt _ _ _⟩

/-- (a) **The premises of `IncludeSleepy`**: a Goldilocks run with `NoColl` and `Sleepy`, the ready
proposal `blk s` released at `t_s` (`s ≥ 1`), and for `t ≥ t_s + 6Δ` the validator ready at `t`
with the first cut `8(t + 1)` after `t`. -/
theorem includeSleepy_premises (s t : Nat) (hs : 1 ≤ s) (ht : 4 * s + 6 ≤ t) :
    GoldilocksRun (sp := sp1) (ro := ro1) (fun _ => v0) dg1 Set.univ (tickRun N1 dg1) ∧
      Compose.NoCollRun dg1 (tickRun N1 dg1) ∧ (tickRun N1 dg1).SleepyRun Set.univ 1 ∧
      Regimes.ReadyProposalAt (tickRun N1 dg1) Set.univ (Regimes.catchUp sp1) (sp1.ts s)
        (blk s) ∧
      sp1.ts s + 6 * sp1.Δ ≤ t ∧
      Regimes.ReadyAt (tickRun N1 dg1) Set.univ (Regimes.catchUp sp1) v0 t ∧
      Regimes.CutAfter (tickRun N1 dg1) (8 * (t + 1)) t := by
  refine ⟨tickRun_goldilocksRun, dg1_noColl _, tickRun_sleepy, tickRun_readyProposalAt _ s hs,
    ?_, tickRun_readyAt _ _ _, tickRun_cutAfter t⟩
  rw [ts_eq, delta1]
  change ((4 * s : Nat) : Int) + 6 * 1 ≤ (t : Int)
  omega

/-- (a) **The premises of `GrowSleepy` at `k = 1`**: a Goldilocks run with `NoColl` and `Sleepy`,
`t ≥ 0` and a ready proposer at every slot start (`ProposerRecurrence … 1 0 (t + 10Δ)`); and the
validator ready at `t` and at `t + 10Δ`, with the first cuts `8(t + 1)` after `t` and `8(t + 11)`
after `t + 10Δ`. -/
theorem growSleepy_premises (t : Nat) :
    GoldilocksRun (sp := sp1) (ro := ro1) (fun _ => v0) dg1 Set.univ (tickRun N1 dg1) ∧
      Compose.NoCollRun dg1 (tickRun N1 dg1) ∧ (tickRun N1 dg1).SleepyRun Set.univ 1 ∧
      1 ≤ 1 ∧ (0 : Time) ≤ t ∧
      Regimes.ProposerRecurrence (tickRun N1 dg1) Set.univ (fun _ => v0) (Regimes.catchUp sp1) 1
        0 (t + (4 * 1 + 6) * sp1.Δ) ∧
      Regimes.ReadyAt (tickRun N1 dg1) Set.univ (Regimes.catchUp sp1) v0 t ∧
      Regimes.CutAfter (tickRun N1 dg1) (8 * (t + 1)) t ∧
      Regimes.ReadyAt (tickRun N1 dg1) Set.univ (Regimes.catchUp sp1) v0
        (t + (4 * 1 + 6) * sp1.Δ) ∧
      Regimes.CutAfter (tickRun N1 dg1) (8 * (t + 11)) (t + (4 * 1 + 6) * sp1.Δ) := by
  refine ⟨tickRun_goldilocksRun, dg1_noColl _, tickRun_sleepy, le_rfl, Int.natCast_nonneg _,
    fun s₀ _ _ => ⟨s₀, le_rfl, Nat.lt_succ_self _, tickRun_readyAt _ _ _⟩,
    tickRun_readyAt _ _ _, tickRun_cutAfter t,
    tickRun_readyAt _ _ _, ?_⟩
  have h := tickRun_cutAfter (t + 10)
  rwa [show (((t + 10 : Nat)) : Time) = t + (4 * 1 + 6) * sp1.Δ by rw [delta1]; push_cast; ring]
    at h

/-! ## The sleepy rows applied -/

/-- (b) **R.1 on the tick run** (`sleepy_safe`): the validator's reads at the read points
`(8t, t)` and `(8t', t')` are compatible, and the earlier one is an ancestor of the later one. -/
theorem tickRun_sleepySafe (t t' : Nat) :
    Compatible ((tickRun N1 dg1).HonestBlocks Set.univ)
        (Regimes.readAfter (tickRun N1 dg1) v0 (8 * t) t)
        (Regimes.readAfter (tickRun N1 dg1) v0 (8 * t') t') ∧
      (t ≤ t' → Anc ((tickRun N1 dg1).HonestBlocks Set.univ)
        (Regimes.readAfter (tickRun N1 dg1) v0 (8 * t) t)
        (Regimes.readAfter (tickRun N1 dg1) v0 (8 * t') t')) := by
  obtain ⟨hrun, hnc, hsl, hi, hj, hbi, hbj, hy, hy'⟩ := sleepySafe_premises t t'
  have h := Regimes.sleepy_safe sp1 ro1 dg1 Set.univ (tickRun N1 dg1) (fun _ => v0) 1 rfl hrun
    hnc hsl
  refine ⟨h.1 v0 (Set.mem_univ _) v0 (Set.mem_univ _) _ _ _ _, fun htt => ?_⟩
  exact h.2 v0 _ _ _ _ hi hj hbi hbj (by omega) hy hy'

/-- (b) **R.2 inclusion on the tick run** (`include_sleepy`): the own block of slot `s ≥ 1` is in
the validator's read after every time `t ≥ t_s + 6Δ`. -/
theorem tickRun_includeSleepy (s t : Nat) (hs : 1 ≤ s) (ht : 4 * s + 6 ≤ t) :
    Anc ((tickRun N1 dg1).HonestBlocks Set.univ) (blk s)
      (Regimes.readAfter (tickRun N1 dg1) v0 (8 * (t + 1)) t) := by
  obtain ⟨hrun, hnc, hsl, hP, hτ, hy, hj⟩ := includeSleepy_premises s t hs ht
  exact Regimes.include_sleepy sp1 ro1 dg1 Set.univ (tickRun N1 dg1) (fun _ => v0) 1 rfl hrun
    hnc hsl _ _ hP v0 t _ hτ hy hj

/-- (b) **R.2 growth on the tick run** (`grow_sleepy`, `k = 1`): some ready proposal `P` released
after `t` is in the validator's read after `t + 10Δ` and not in its read after `t`, and the read
after `t` is an ancestor of the read after `t + 10Δ`. -/
theorem tickRun_growSleepy (t : Nat) :
    ∃ τ P, (t : Time) < τ ∧
      Regimes.ReadyProposalAt (tickRun N1 dg1) Set.univ (Regimes.catchUp sp1) τ P ∧
      Anc ((tickRun N1 dg1).HonestBlocks Set.univ) P
        (Regimes.readAfter (tickRun N1 dg1) v0 (8 * (t + 11)) (t + (4 * 1 + 6) * sp1.Δ)) ∧
      ¬ Anc ((tickRun N1 dg1).HonestBlocks Set.univ) P
        (Regimes.readAfter (tickRun N1 dg1) v0 (8 * (t + 1)) t) ∧
      Anc ((tickRun N1 dg1).HonestBlocks Set.univ)
        (Regimes.readAfter (tickRun N1 dg1) v0 (8 * (t + 1)) t)
        (Regimes.readAfter (tickRun N1 dg1) v0 (8 * (t + 11)) (t + (4 * 1 + 6) * sp1.Δ)) := by
  obtain ⟨hrun, hnc, hsl, hk, ht, hrec, hx, hjx, hy, hj⟩ := growSleepy_premises t
  obtain ⟨τ, P, hτ, hP, hin, hnot, hanc⟩ := Regimes.grow_sleepy sp1 ro1 dg1 Set.univ
    (tickRun N1 dg1) (fun _ => v0) 1 1 rfl hrun hnc hsl hk t ht hrec
  exact ⟨τ, P, hτ, hP, hin v0 _ hy hj, hnot v0 _ hx hjx, hanc v0 _ v0 _ hx hjx hy hj⟩

end Consensus.Goldilocks.Witness.One

end
