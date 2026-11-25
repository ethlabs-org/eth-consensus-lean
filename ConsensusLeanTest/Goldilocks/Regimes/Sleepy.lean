module
public import ConsensusLeanTest.Goldilocks.Persist.Premises
public import ConsensusLeanTest.Goldilocks.Regimes.SleepyCommittee
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Const
@[expose] public section

/-! # The one-validator tick run meets the premises of the sleepy row R.2

On the one-validator tick run of `Goldilocks/Runs/OneValidator/Premises` (`n = 1`, `Δ = 1`,
`t_s = 4s`, a tick at every time `t ≥ 0`, cut `i` at time `⌊i/8⌋`, no restart), with `Δ_F = 1` and
catch-up `c = 18Δ`:

* (a) `tickRun_readyAt`, `tickRun_cutAfter`, `tickRun_readyProposalAt`: the validator is ready
  at every time; `8(t + 1)` is the first cut after `t`, for every `t ∈ ℕ`; the own block `blk s`
  of slot `s ≥ 1` is a ready proposal released at `t_s` (cut `8·t_s + 2`).
* (a) `includeSleepy_premises`, `growSleepy_premises`: the run, `NoColl`, `Sleepy`, the ready
  proposal or the proposer recurrence (at `k = 1`, `ProposerRecurrence … 1 0 (t + 10Δ)`) hold
  together, with ready readers at these cuts.
* (b) the committee rows `Regimes.Growing.IncludeSleepy` and `GrowSleepy` at the full committee
  and the constant honest set (`tickRun_growingRun`, `tickRun_sleepyAt`, `tickRun_honestBlocksAt`):
  `tickRun_includeSleepy`: `include_sleepy` puts `blk s` in the read after every `t ≥ t_s + 6Δ`.
  `tickRun_growSleepy`: `grow_sleepy` at `k = 1` yields a ready proposal `P` released after `t`
  that is in the read after `t + 10Δ` (cut `8(t + 11)`) and not in the read after `t` (cut
  `8(t + 1)`), the earlier read an ancestor of the later one.

With `n = 1` and `f = 0` this shows the premises consistent, not met with faults. -/

namespace Consensus.Goldilocks.Witness.One

open AC Node ChainFrame

/-! ## Ready readers, read points, cuts and proposals -/

/-- The validator is ready at every time, for every catch-up (it is awake at every `t ≥ 0`). -/
theorem tickRun_readyAt (c t : Time) (y : Fin sp1.n) :
    Regimes.ReadyAt (tickRun N1 dg1) Set.univ c y t :=
  ⟨Set.mem_univ _, fun _ h _ => (le_max_left _ _).trans h⟩

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

/-- (a) **The inclusion premises**: a Goldilocks run with `NoColl` and `Sleepy`, the ready
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

/-- (a) **The growth premises at `k = 1`**: a Goldilocks run with `NoColl` and `Sleepy`,
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

/-! ## The committee rows at the full committee

The tick run read as a run with the constant honest set `fun _ => Set.univ`: its honest blocks are
the static ones, its run carries over (from the full committee's start, which is the default start,
`run_full`), its `Sleepy` premise carries over with look-ahead `ahead`, and the full committee has
its committee facts and committee support. -/

/-- The honest blocks of the constant honest set are the static honest blocks. -/
theorem tickRun_honestBlocksAt :
    (tickRun N1 dg1).HonestBlocksAt (fun _ => Set.univ) =
      (tickRun N1 dg1).HonestBlocks Set.univ := by
  ext B
  constructor
  · rintro ⟨y, i, -, -, -, -, hB⟩
    exact ⟨y, Set.mem_univ _, i, hB⟩
  · rintro ⟨y, -, i, hB⟩
    refine ⟨y, i, max 0 ((tickRun N1 dg1).time (i - 1)), le_max_left _ _, fun k hk => ?_,
      Set.mem_univ _, hB⟩
    exact (tickRun_goldilocksRun.time_mono (by omega)).trans (le_max_right _ _)

/-- The tick run under the constant honest set. -/
theorem tickRun_growingRun :
    Consensus.Goldilocks.Growing.GoldilocksRun (sp := sp1) (ro := ro1) (fun _ => v0) dg1
      (fun _ => Set.univ) (tickRun N1 dg1) :=
    { toLocalRun := Consensus.Goldilocks.Growing.LocalRun.const_iff.2
        tickRun_goldilocksRun.toLocalRun
      genesis_root_ok := tickRun_goldilocksRun.genesis_root_ok
      vstart := tickRun_goldilocksRun.vstart }

/-- `Sleepy` of the tick run, with look-ahead `ahead`, under the constant honest set. -/
theorem tickRun_sleepyAt :
    (tickRun N1 dg1).SleepyRunAt (fun _ => Set.univ) 1 (Regimes.Growing.ahead sp1) := by
  obtain ⟨hs, hf⟩ := tickRun_sleepy
  refine ⟨⟨hs.deltaF, hs.delta_le,
    fun x i m _ hm hw y j _ hj hd =>
      hs.message x (Set.mem_univ _) i m hm hw y (Set.mem_univ _) j hj hd,
    fun x i B _ hB hw y j _ hj hd =>
      hs.block x (Set.mem_univ _) i B hB hw y (Set.mem_univ _) j hj hd,
    fun x i B _ hB hw y j _ hj hd hanc => hs.relay x (Set.mem_univ _) i B hB hw y (Set.mem_univ _)
      j hj hd (tickRun_honestBlocksAt ▸ hanc),
    fun x i a _ ha hw _ y j _ hj hd =>
      hs.attestation x (Set.mem_univ _) i a ha hw y (Set.mem_univ _) j hj hd, hs.deltaF.le⟩, ?_⟩
  intro s d hd
  have hb : ∀ t e : Time, (tickRun N1 dg1).FaultBound Set.univ t →
      (tickRun N1 dg1).FaultBoundAt (fun _ => Set.univ) t e := fun _ _ h => h
  rcases hd with rfl | rfl | rfl
  · simpa only [add_zero] using hb _ _ (hf s).1
  · exact hb _ _ (hf s).2.1
  · exact hb _ _ (hf s).2.2

/-! ## The sleepy rows applied -/

/-- (b) **R.2 inclusion on the tick run** (`Regimes.Growing.include_sleepy` at the full
committee): the own block of slot `s ≥ 1` is in
the validator's read after every time `t ≥ t_s + 6Δ`. -/
theorem tickRun_includeSleepy (s t : Nat) (hs : 1 ≤ s) (ht : 4 * s + 6 ≤ t) :
    Anc ((tickRun N1 dg1).HonestBlocks Set.univ) (blk s)
      (Regimes.readAfter (tickRun N1 dg1) v0 (8 * (t + 1)) t) := by
  obtain ⟨-, hnc, -, ⟨p, kP, hp, hkP, hτP⟩, hτ, hy, hj⟩ := includeSleepy_premises s t hs ht
  have h := Regimes.Growing.include_sleepy sp1 ro1 dg1 (fun _ => Set.univ) (tickRun N1 dg1)
    (fun _ => v0) 1 _ (Regimes.Growing.Test.run_full tickRun_growingRun) hnc
    (Compose.Growing.CommitteeFacts.of_full tickRun_growingRun hnc rfl) tickRun_sleepyAt
    (Regimes.Growing.Test.committeeSleepy_full tickRun_growingRun tickRun_sleepyAt) _ _
    ⟨p, kP, hp, Set.mem_univ _, hkP, hτP⟩ v0 t _ hτ hy hj
  rwa [tickRun_honestBlocksAt] at h

/-- (b) **R.2 growth on the tick run** (`Regimes.Growing.grow_sleepy` at the full committee,
`k = 1`): some ready proposal `P` released
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
  obtain ⟨-, hnc, -, hk, ht, hrec, hx, hjx, hy, hj⟩ := growSleepy_premises t
  obtain ⟨τ, P, hτ, ⟨p, kP, hp, -, hkP, hτP⟩, hin, hnot, hanc⟩ :=
    Regimes.Growing.grow_sleepy sp1 ro1 dg1 (fun _ => Set.univ) (tickRun N1 dg1) (fun _ => v0) 1 1
      _ (Regimes.Growing.Test.run_full tickRun_growingRun) hnc
      (Compose.Growing.CommitteeFacts.of_full tickRun_growingRun hnc rfl)
      tickRun_sleepyAt (Regimes.Growing.Test.committeeSleepy_full tickRun_growingRun
        tickRun_sleepyAt) hk t ht
      (fun s₀ h₀ h₁ => let ⟨s, h1, h2, h3⟩ := hrec s₀ h₀ h₁; ⟨s, h1, h2, h3, Set.mem_univ _⟩)
  rw [tickRun_honestBlocksAt] at hin hnot hanc
  exact ⟨τ, P, hτ, ⟨p, kP, hp, hkP, hτP⟩, hin v0 _ hy hj, hnot v0 _ hx hjx,
    hanc v0 _ v0 _ hx hjx hy hj⟩

end Consensus.Goldilocks.Witness.One

end
