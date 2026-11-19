module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunCommittee
public import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Seed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Invariant
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Continuation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Binding
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Members

public section

/-! # The bounded healed-safety query of a hand-over run

A hand-over run at `T` is healthy up to `T`: partial synchrony from GST `g`, fewer than fraction
`β` compromised by `T` with full participation on `[max g 0, T]`, the FG delay within its bound,
and its selected committees healthy at `βK` on `[max g 0, T]`. These are the healthy fields of a
healed-safety query with the bound `T`, so a valid collision-free hand-over run with `T` inside
its horizon is such a query. With the heal point at
or before `T` and progress on `[ready, heal]` the query meets the premises of the hand-over seed.

* `Obligations.Growing.handoverQuery`: the query of a hand-over run, bounded at `T`;
* `Obligations.Growing.handover_query_at`: with `heal ≤ T` and progress on `[ready, heal]`, the
  query meets the premises of `handover_seed_cover_at`;
* `Obligations.Growing.handover_invariant_at`: the seed and a read start `t₁ ∈ [t_{r+k}, T]` with
  `t₁ + 8Δ + 1 ≤ heal`, from which the seeded invariant holds through every `b ≥ T`.

The bound must lie inside the run's horizon (`HealthyPreparationQueryAt.bound_le`): a hand-over
past the horizon is a healthy run up to the horizon, covered by the healthy claims. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The healed-safety query of a hand-over run**, bounded at the hand-over time `T`: the healthy
fields are the hand-over's partial synchrony, its health up to `T`, its FG delay bound and the
health of its selected committees. -/
abbrev handoverQuery (hn : 1 ≤ Fintype.card V)
    {r : (Sys (goldilocks S) V).Run}
    (hv : (Sys (goldilocks S) V).Valid r)
    (hx : ¬ (Sys (goldilocks S) V).Excuse r)
    {cap : Capability} (hcap : cap = .available ∨ cap = .stable) (i : (K S A).Idx) {g T : Time}
    (hh : (Sys (goldilocks S) V).Handover
      (shapeProgress (goldilocks S) V).toExternal (K S A) g T r)
    (hTh : T ≤ ((Sys (goldilocks S) V).pt r).horizon) :
    HealthyPreparationQueryAt
        S A V := by
  exact ⟨r, hn, cap, hcap, i, g, T, hv, hx, hTh, ⟨hh.1, hh.2.1, hh.2.2.1⟩, hh.2.2.2.2.2.1⟩

variable {S A V}

/-- **The hand-over query meets the seed's premises**: its heal point is `≥ 0` (it is
`max g 0 + m·ΔAC`), at most its bound `T`, and progress holds on its `[ready, heal]`. -/
theorem handover_query_at (hn : 1 ≤ Fintype.card V)
    {r : (Sys (goldilocks S) V).Run}
    (hv : (Sys (goldilocks S) V).Valid r)
    (hx : ¬ (Sys (goldilocks S) V).Excuse r)
    {cap : Capability} (hcap : cap = .available ∨ cap = .stable) {i : (K S A).Idx} {g T : Time}
    (hh : (Sys (goldilocks S) V).Handover
      (shapeProgress (goldilocks S) V).toExternal (K S A) g T r)
    (hTh : T ≤ ((Sys (goldilocks S) V).pt r).horizon)
    (hT : (Sys (goldilocks S) V).heal (K S A) cap i g r ≤ T)
    (hp : (Sys (goldilocks S) V).prog
      (shapeProgress (goldilocks S) V)
      (K S A) cap i
      ((Sys (goldilocks S) V).ready (K S A) g r)
          ((Sys (goldilocks S) V).heal (K S A) cap i g r)
      r) :
    let Q := handoverQuery S A V hn hv hx hcap i hh hTh
    0 ≤ Q.heal ∧ Q.heal ≤ Q.bound ∧
      (Sys (goldilocks S) V).prog
        (shapeProgress (goldilocks S) V) (K S A)
        Q.cap Q.index
        Q.ready Q.heal Q.run :=
  ⟨add_nonneg (le_max_right g 0) (mul_nonneg (Int.natCast_nonneg _) r.1.ΔAC_pos.le), hT, hp⟩

/-- **The seeded invariant of a healed-safety query** healthy up to its bound `T`, with
`0 ≤ heal ≤ T` and progress on `[ready, heal]`: a hand-over seed at `T` and a read start
`t₁ ∈ [t_{r+k}, T]` with `t₁ + 8Δ + 1 ≤ heal`, from which the seeded invariant holds through
every `b ≥ T` with the reset service, the slot counts from `r` through `b`, the committee counts
of the run's committees `voteK` from `r` through `b` (their committee facts are the run's,
`voteK_facts`) and conviction below a third. `t₁` is the later of the record cover's start and
the drain `t_{r+k}`; both are at least `8Δ + 1` before the heal point (`handover_seed_cover_at`),
and `t₁` does not depend on `b`. -/
theorem handover_invariant_at
    (Q : HealthyPreparationQueryAt S A V) (h0 : 0 ≤ Q.heal)
    (hb : Q.heal ≤ Q.bound)
    (hp : (Sys (goldilocks S) V).prog
      (shapeProgress (goldilocks S) V)
      (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run) :
    ∃ r σ, Compose.Growing.HandoverSeed Q.trace Q.keys
        (runProposer S Q.run.2 Q.hn)
        (digestOf S Q.run.2) Q.gst
        (protoFGDelay (Model.pubOf Q.run.1)) Q.bound r σ
        (cm := runCommittee S Q.run.2 Q.hn)
        (βK := (K S A).params.βK) ∧
      ∃ t₁, t₁ ≤ Q.bound ∧ Q.params.ts (r + Q.params.k : Nat) ≤ t₁ ∧
        t₁ + 8 * Q.params.Δ + 1 ≤ Q.heal ∧
        ∀ b, Q.bound ≤ b →
          Healing.Growing.ResetService Q.trace Q.keys Q.gst (protoFGDelay (Model.pubOf Q.run.1)) b →
          Compose.Growing.SleepyBoundsFrom Q.trace Q.keys r b →
          Compose.Growing.CommitteeBoundsFrom Q.trace Q.keys (voteK S Q.run.2) r b →
          Compose.Growing.ChainConvictedBelow Q.trace Q.keys →
          Compose.Growing.SeededInvariant Q.trace Q.keys Q.gst r (r + Q.params.k - 1) t₁ b := by
  obtain ⟨r, σ, hseed, t₀, ht₀T, hdt₀, hlate, hcov⟩ := handover_seed_cover_at S A V Q h0 hb hp
  obtain ⟨a, hpr, -⟩ := hseed.reset
  have hΔ := Q.params.toParams.hΔ
  refine ⟨r, σ, hseed, max t₀ (Q.params.ts (r + Q.params.k : Nat)), max_le ht₀T (hdt₀.trans ht₀T),
    le_max_right _ _, ?_, fun b hTb hsvc hB hKB hcv =>
      Compose.Growing.seeded_invariant_of_cover_at
        (simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid) hpr.noColl hseed
        hTb hsvc hB hcv hcov
        (voteK_facts S Q.run.2 Q.hn Q.valid hpr.noColl
          (simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid)) hKB⟩
  rw [max_eq_left hdt₀]
  exact hlate

end Consensus.Goldilocks.Obligations.Growing

end
