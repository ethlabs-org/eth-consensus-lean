module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Seed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Invariant
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Continuation

public section

/-! # The bounded healed-safety query of a hand-over run

A hand-over run at `T` is healthy up to `T`: partial synchrony from GST `g`, fewer than fraction
`β` compromised by `T` with full participation on `[max g 0, T]`, and the FG delay within its
bound. These are the healthy fields of a healed-safety query with the bound `T`, so a valid
collision-free hand-over run with `T` inside its horizon is such a query. With the heal point at
or before `T` and progress on `[ready, heal]` the query meets the premises of the hand-over seed.

* `Obligations.Growing.handoverQuery`: the query of a hand-over run, bounded at `T`;
* `Obligations.Growing.handoverQuery_eq`: its run, keys, trace, GST, capability, index, bound,
  ready and heal points, each the run's own (definitionally);
* `Obligations.Growing.handover_query_at`: with `heal ≤ T` and progress on `[ready, heal]`, the
  query meets the premises of `handover_seed_at`;
* `Obligations.Growing.handover_seed_of_handover_at`: the hand-over seed at `T` on the run's
  canonical trace and honest keys;
* `Obligations.Growing.handover_invariant_at`: the seed and a read start `t₁ ∈ [t_{r+k}, T]` with
  `t₁ + 8Δ + 1 ≤ heal`, from which the seeded invariant holds through every `b ≥ T`.

The bound must lie inside the run's horizon (`HealthyPreparationQueryAt.bound_le`): a hand-over
past the horizon is a healthy run up to the horizon, covered by the healthy claims. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The healed-safety query of a hand-over run**, bounded at the hand-over time `T`: the healthy
fields are the hand-over's partial synchrony, its health up to `T` and its FG delay bound. -/
abbrev handoverQuery (hn : 1 ≤ Fintype.card V) {r : (Sys (goldilocks S) V).Run}
    (hv : (Sys (goldilocks S) V).Valid r) (hx : ¬ (Sys (goldilocks S) V).Excuse r)
    {cap : Capability} (hcap : cap = .available ∨ cap = .stable) (i : (K S A).Idx) {g T : Time}
    (hh : (Sys (goldilocks S) V).Handover (K S A) g T r)
    (hTh : T ≤ ((Sys (goldilocks S) V).pt r).horizon) : HealthyPreparationQueryAt S A V :=
  ⟨r, hn, cap, hcap, i, g, T, hv, hx, hTh, hh.1, hh.2.1, hh.2.2.1⟩

variable {S A V}

/-- **The hand-over query's data are the run's own**: its run, keys, trace, GST, capability,
index, bound, ready and heal points. -/
theorem handoverQuery_eq (hn : 1 ≤ Fintype.card V) {r : (Sys (goldilocks S) V).Run}
    (hv : (Sys (goldilocks S) V).Valid r) (hx : ¬ (Sys (goldilocks S) V).Excuse r)
    {cap : Capability} (hcap : cap = .available ∨ cap = .stable) (i : (K S A).Idx) {g T : Time}
    (hh : (Sys (goldilocks S) V).Handover (K S A) g T r)
    (hTh : T ≤ ((Sys (goldilocks S) V).pt r).horizon) :
    let Q := handoverQuery S A V hn hv hx hcap i hh hTh
    Q.run = r ∧ Q.keys = honestKeysAt ⟨S, stock⟩ r.2 ∧ Q.trace = simTraceAt ⟨S, stock⟩ r.2 hn ∧
        Q.gst = g ∧
      Q.cap = cap ∧ Q.index = i ∧ Q.bound = T ∧
      Q.ready = (Sys (goldilocks S) V).ready (K S A) g r ∧
      Q.heal = (Sys (goldilocks S) V).heal (K S A) cap i g r :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The hand-over query meets the seed's premises**: its heal point is `≥ 0` (it is
`max g 0 + m·ΔAC`), at most its bound `T`, and progress holds on its `[ready, heal]`. -/
theorem handover_query_at (hn : 1 ≤ Fintype.card V) {r : (Sys (goldilocks S) V).Run}
    (hv : (Sys (goldilocks S) V).Valid r) (hx : ¬ (Sys (goldilocks S) V).Excuse r)
    {cap : Capability} (hcap : cap = .available ∨ cap = .stable) {i : (K S A).Idx} {g T : Time}
    (hh : (Sys (goldilocks S) V).Handover (K S A) g T r)
    (hTh : T ≤ ((Sys (goldilocks S) V).pt r).horizon)
    (hT : (Sys (goldilocks S) V).heal (K S A) cap i g r ≤ T)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) cap i
      ((Sys (goldilocks S) V).ready (K S A) g r) ((Sys (goldilocks S) V).heal (K S A) cap i g r)
      r) :
    let Q := handoverQuery S A V hn hv hx hcap i hh hTh
    0 ≤ Q.heal ∧ Q.heal ≤ Q.bound ∧
      (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
        Q.ready Q.heal Q.run :=
  ⟨add_nonneg (le_max_right g 0) (mul_nonneg (Int.natCast_nonneg _) r.1.ΔAC_pos.le), hT, hp⟩

/-- **The hand-over seed of a hand-over run** at `T`, on the run's canonical trace and honest keys,
with the run's proposer, digest and FG delay `protoFGDelay` (`handover_seed_at` on the hand-over
query). -/
theorem handover_seed_of_handover_at (hn : 1 ≤ Fintype.card V) {r : (Sys (goldilocks S) V).Run}
    (hv : (Sys (goldilocks S) V).Valid r) (hx : ¬ (Sys (goldilocks S) V).Excuse r)
    {cap : Capability} (hcap : cap = .available ∨ cap = .stable) {i : (K S A).Idx} {g T : Time}
    (hh : (Sys (goldilocks S) V).Handover (K S A) g T r)
    (hTh : T ≤ ((Sys (goldilocks S) V).pt r).horizon)
    (hT : (Sys (goldilocks S) V).heal (K S A) cap i g r ≤ T)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) cap i
      ((Sys (goldilocks S) V).ready (K S A) g r) ((Sys (goldilocks S) V).heal (K S A) cap i g r)
      r) :
    ∃ rL σ, Compose.Growing.HandoverSeed (simTraceAt ⟨S, stock⟩ r.2 hn)
        (honestKeysAt ⟨S, stock⟩ r.2)
      (runProposer ⟨S, stock⟩ r.2 hn) (digestOf ⟨S, stock⟩ r.2) g (protoFGDelay (Model.pubOf r.1)) T
          rL σ :=
  let h := handover_query_at hn hv hx hcap hh hTh hT hp
  handover_seed_at S A V (handoverQuery S A V hn hv hx hcap i hh hTh) h.1 h.2.1 h.2.2

/-- **The seeded invariant of a healed-safety query** healthy up to its bound `T`, with
`0 ≤ heal ≤ T` and progress on `[ready, heal]`: a hand-over seed at `T` and a read start
`t₁ ∈ [t_{r+k}, T]` with `t₁ + 8Δ + 1 ≤ heal`, from which the seeded invariant holds through
every `b ≥ T` with the reset service and the slot counts from `r` through `b` and conviction below a
third. `t₁` is the later of the record cover's start and the drain `t_{r+k}`; both are at least
`8Δ + 1` before the heal point (`handover_seed_cover_at`), and `t₁` does not depend on `b`. -/
theorem handover_invariant_at (Q : HealthyPreparationQueryAt S A V) (h0 : 0 ≤ Q.heal)
    (hb : Q.heal ≤ Q.bound)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run) :
    ∃ r σ, Compose.Growing.HandoverSeed Q.trace Q.keys (runProposer ⟨S, stock⟩ Q.run.2 Q.hn)
        (digestOf ⟨S, stock⟩ Q.run.2) Q.gst (protoFGDelay (Model.pubOf Q.run.1)) Q.bound r σ ∧
      ∃ t₁, t₁ ≤ Q.bound ∧ Q.params.ts (r + Q.params.k : Nat) ≤ t₁ ∧
        t₁ + 8 * Q.params.Δ + 1 ≤ Q.heal ∧
        ∀ b, Q.bound ≤ b →
          Healing.Growing.ResetService Q.trace Q.keys Q.gst (protoFGDelay (Model.pubOf Q.run.1)) b →
          Compose.Growing.SleepyBoundsFrom Q.trace Q.keys r b →
          Compose.Growing.ChainConvictedBelow Q.trace Q.keys →
          Compose.Growing.SeededInvariant Q.trace Q.keys Q.gst r (r + Q.params.k - 1) t₁ b := by
  obtain ⟨r, σ, hseed, t₀, ht₀T, hdt₀, hlate, hcov⟩ := handover_seed_cover_at S A V Q h0 hb hp
  obtain ⟨a, hpr, -⟩ := hseed.reset
  have hΔ := Q.params.toParams.hΔ
  refine ⟨r, σ, hseed, max t₀ (Q.params.ts (r + Q.params.k : Nat)), max_le ht₀T (hdt₀.trans ht₀T),
    le_max_right _ _, ?_, fun b hTb hsvc hB hcv =>
      Compose.Growing.seeded_invariant_of_cover_at hpr.run hpr.noColl hseed hTb hsvc hB hcv hcov
        rfl⟩
  rw [max_eq_left hdt₀]
  exact hlate

end Consensus.Goldilocks.Obligations.Growing

end
