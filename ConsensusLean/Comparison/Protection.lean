module
public import ConsensusLean.Comparison.Basic

@[expose] public section

/-! # Slice 2: the protection profile (statements)

Slice 2 answers: how long before an outage must a read be made to survive it, and from when is it
kept? A read of the source output made at `T` by a node ready at `T` is **protected** through an
outage `[b₀, b₁)` of length at most `β·ΔAC` if it is a prefix of every ready read of the resilience
target from a recovery point on. The profile bounds the arming lag `ℓ` (`T + ℓ·ΔAC ≤ b₀`) and the
recovery delay `rec` (protection from `b₁ + rec·ΔAC`), as functions of the budget `β`, a lower
bound `A` on the outage cohort, the fault cap `fcap`, the source output, the outage windows and
the readiness numbers.

* `ProtSrc`: the source output, `available` or `stable` (B11 reads the available output; the
  contract's `persists` reads the stable one).
* `ProtQ`: the parameters `⟨β, A, fcap, src, η, noSleep, cohortAhead, ahead, θ, catchUp⟩`. The
  windows, the sleepy threshold and the catch-up are coordinates of the point, not the contract's
  numbers, so two protocols at the same point are ranked on the same run class and the same ready
  readers. The order (`ProtQ.le_def`) implies inclusion of the run classes (`ProtClassMono`).
* `ProtClass`: the **bound-independent** run class, the contract's `Outage` without its arming lag
  and with the point's numbers in place of the contract's (`OutageTimes` without
  `T + lag·ΔAC ≤ b₀`; `OutageNet`; η-sleepy participation; `NoSleepOn` and `CohortOn` on the
  retained view), plus the cohort refinement `A ≤ |awakeAt (start)|` on the same retained view and
  the fault cap. It reads no contract.
* `ProtectionProfile S ℓ rec`: on valid runs of the class at `q` armed with `T + ℓ q·ΔAC ≤ b₀`,
  unless the run's excuse holds, every read of the source at `T` by a node ready at `T` is a prefix
  of the read of the resilience target by every node ready at a time from `b₁ + rec q·ΔAC` to the
  horizon (`ProtectedReadyFrom`). Both bounds are monotone in the adverse parameters.
* `ContinuousProtection S ℓ`: the stronger, optional variant (B11's continuous protection): the
  same reads are kept by every ready reader from `b₀` on, through the outage. **Not ranked** until
  it has its own coverage.
* Coverage, a separate obligation: `ProtDomainCoverage` (the class at every domain-feasible point is
  nonempty with the claim active; the representative's cohort is at least `A` and its fault count
  at most `fcap`) and `ProtBoundaryCoverage` (at every boundary-feasible point, a witness attaining
  `β`, `A` and `fcap` exactly).
* The default from the contract (`ProtectionDefault`): from `Behaviour.persists`, `ℓ = lag` and
  `rec = recovery` for the stable source at every point whose numbers put the class inside the
  contract's `Outage` and its readers among the contract's ready readers (`β ≤ budget`,
  `η ≥ K.η`, `ahead ≥ K.ahead`, `noSleep ≥ K.noSleep` with the same retention offset
  `noSleep + cohortAhead`, `θ ≥ K.θ`, `catchUp ≥ K.catchUp`), whatever `A` and `fcap`; `⊤`
  elsewhere. The contract's row is the `A = 0` column at the contract's numbers (where
  the cohort refinement is vacuous and `CohortOn` alone constrains the run); the default is finite
  at every `A`, as monotonicity requires, because the class at `A` is included in the class at `0`.
  At `θ ≥ 1` the class is empty, so a finite default there is a vacuous implication: such points
  are outside both feasible predicates (`0 ≤ θ < 1`) and are never ranked.

Statements only: the proofs are in `Proofs/Comparison`. -/

namespace Consensus.Comparison

/-- The source output of a protected read: `available` (B11's source) or `stable` (the contract's
`persists`). The final output has no protection row. -/
inductive ProtSrc where
  | available
  | stable
  deriving DecidableEq, Repr

/-- The capability a source names. -/
def ProtSrc.cap : ProtSrc → Capability
  | .available => .available
  | .stable => .stable

/-- Slice 2 parameters:
* the outage budget `β` (`b₁ − b₀ ≤ β·ΔAC`);
* a **lower** bound `A` on the outage cohort (the validators honest and awake at the start of the
  no-sleep window, on the view retained through the cohort point);
* the fault cap `fcap` (`faultCount horizon ≤ fcap`);
* the source output `src`;
* the windows, `ΔAC`-coefficients as in the contract's `Params`: the η-sleepy look-back `η`, the
  no-sleep margin `noSleep` (the window `[b₀ − noSleep·ΔAC, b₁ + noSleep·ΔAC]`), the cohort
  look-ahead `cohortAhead` (the cohort is counted on the view retained through
  `b₁ + (noSleep + cohortAhead)·ΔAC`) and the sleepy look-ahead `ahead`;
* the readiness numbers: the sleepy threshold `θ` and the catch-up `catchUp` (a reader is ready
  after `catchUp·ΔAC + 1` awake, `EnvPoint.Ready`). -/
structure ProtQ where
  β : ℕ
  A : ℕ
  fcap : ℕ
  src : ProtSrc
  η : ℕ
  noSleep : ℕ
  cohortAhead : ℕ
  ahead : ℕ
  θ : ℚ
  catchUp : ℕ

namespace ProtQ

/-- The order, a larger point admitting more runs:
* `β` and `fcap` increase;
* the cohort lower bound `A` decreases (a smaller lower bound admits more runs);
* the source is fixed (two sources are two claims, not two adversities);
* the η-sleepy look-back `η` decreases (a longer look-back charges more validators against the
  ready ones, a stronger premise);
* the sleepy look-ahead `ahead` decreases (a later retention charges more faults);
* the retention offset `noSleep + cohortAhead` is fixed, and at that offset `noSleep` decreases (a
  wider no-sleep window on the same retained view is a stronger premise). The offset is fixed
  because a later retention point strengthens `CohortOn` but weakens `NoSleepOn`, which constrains
  only the validators still honest at that point; neither direction includes the classes;
* the sleepy threshold `θ` decreases (`θ·X < |ready|` is a stronger premise at a larger `θ`);
* the catch-up `catchUp` decreases (a longer catch-up leaves fewer validators ready: a stronger
  sleepy premise, and fewer sources and readers in the claim, so a claim at a smaller catch-up
  implies the claim at a larger one). -/
instance : LE ProtQ :=
  ⟨fun q q' => q.β ≤ q'.β ∧ q'.A ≤ q.A ∧ q.fcap ≤ q'.fcap ∧ q.src = q'.src ∧ q'.η ≤ q.η ∧
    q'.ahead ≤ q.ahead ∧ q'.noSleep ≤ q.noSleep ∧
    q.noSleep + q.cohortAhead = q'.noSleep + q'.cohortAhead ∧ q'.θ ≤ q.θ ∧
    q'.catchUp ≤ q.catchUp⟩

theorem le_def (q q' : ProtQ) :
    q ≤ q' ↔ q.β ≤ q'.β ∧ q'.A ≤ q.A ∧ q.fcap ≤ q'.fcap ∧ q.src = q'.src ∧ q'.η ≤ q.η ∧
      q'.ahead ≤ q.ahead ∧ q'.noSleep ≤ q.noSleep ∧
      q.noSleep + q.cohortAhead = q'.noSleep + q'.cohortAhead ∧ q'.θ ≤ q.θ ∧
      q'.catchUp ≤ q.catchUp :=
  Iff.rfl

variable (V : Type) [Fintype V]

/-- **Domain-feasible points** (for domain coverage): a positive budget (an active outage lasts at
least `ΔAC`), a realizable threshold `0 ≤ θ < 1`, and a representative fault count `f ≤ fcap` (the
cap need not be attained) with some cohort size `A' ≥ A`, `f < A' ≤ n − f − 1` (the cohort
outnumbers the faults, and an honest validator outside the cohort remains to sleep through the
outage under `NoSleepOn`). Equivalently (take `f = 0`): `β ≥ 1`, `0 ≤ θ < 1` and
`max A 1 + 1 ≤ n`, whatever `fcap`.

**The sleeping witness imposes no further limit here.** `OutageActive` needs an honest validator
asleep at a time `t` of the outage, and the η-sleepy premise at `t` needs `θ·X < |ready_t|` with
the sleeper outside `ready_t`; at `θ ≥ 1` the premise fails at every time (`X ≥ |ready_t|`), so the
class is empty. At `0 ≤ θ < 1` the fault-free representative with one honest validator asleep
throughout the run and the other `n − 1` awake throughout has `ready_t` of size `n − 1`, nobody else
awake and no faults, so the premise is `θ·(n − 1) < n − 1`, which holds for every `n ≥ 2` (implied
by `A' ≥ 1`, `A' + 1 ≤ n`). -/
def DomainFeasible (q : ProtQ) : Prop :=
  1 ≤ q.β ∧ 0 ≤ q.θ ∧ q.θ < 1 ∧
    ∃ f A', f ≤ q.fcap ∧ q.A ≤ A' ∧ f < A' ∧ A' + f + 1 ≤ Fintype.card V

/-- **Boundary-feasible points** (for boundary coverage, exact attainment): a positive budget, a
realizable threshold `0 ≤ θ < 1`, `fcap < A ≤ n − fcap − 1`, and the sleeping witness's sleepy
budget `θ·(A + fcap) < A`. These conditions are what the static witness needs: `fcap` validators
faulty from the start, the `A` cohort validators awake throughout, and the other
`n − A − fcap ≥ 1` honest validators asleep throughout (the required sleepers). At every time its
ready validators are exactly the cohort and nobody else honest is awake, so the η-sleepy premise is
`θ·(A + fcap) < A` (for every look-back and look-ahead), and `CohortOn` is `fcap < A`.

The conditions are **sufficient, not necessary**. `A = 0` is never boundary-feasible: `CohortOn`
forces a cohort larger than the faults and the late wakers. Under growing faults, validators
compromised after the cohort point count toward `fcap` but neither against the cohort nor in the
sleepy budget before they are charged, and the sleepers may wake after the no-sleep window, so
`fcap < A`, `A + fcap + 1 ≤ n` and `θ·(A + fcap) < A` can all be relaxed by other witnesses. -/
def BoundaryFeasible (q : ProtQ) : Prop :=
  1 ≤ q.β ∧ 0 ≤ q.θ ∧ q.θ < 1 ∧ q.fcap < q.A ∧ q.A + q.fcap + 1 ≤ Fintype.card V ∧
    q.θ * (q.A + q.fcap) < q.A

end ProtQ

variable {V : Type} [Fintype V] [DecidableEq V] {Prog : Type} (S : System V)

/-- The catch-up duration `catchUp·ΔAC` of run `r` at `q` (as the contract's `cDur`). -/
def protCDur (q : ProtQ) (r : S.Run) : Time := (q.catchUp : Time) * (S.pt r).env.ΔAC

/-- The start of the no-sleep window of an outage `[b₀, b₁)` at `q`:
`b₀ − noSleep·ΔAC`, clamped to `[0, horizon]` (as the contract's `outageStart`). -/
def protStart (q : ProtQ) (b₀ : Time) (r : S.Run) : Time :=
  min (max 0 (b₀ - (q.noSleep : Time) * (S.pt r).env.ΔAC)) (S.pt r).horizon

/-- The end of the no-sleep window of an outage `[b₀, b₁)` at `q`: `b₁ + noSleep·ΔAC`, clamped to
the horizon (as the contract's `outageEnd`). -/
def protEnd (q : ProtQ) (b₁ : Time) (r : S.Run) : Time :=
  min (b₁ + (q.noSleep : Time) * (S.pt r).env.ΔAC) (S.pt r).horizon

/-- Where the cohort of an outage `[b₀, b₁)` at `q` is charged: `protEnd + cohortAhead·ΔAC`,
clamped to the horizon (as the contract's `cohortAt`). -/
def protCohortAt (q : ProtQ) (b₁ : Time) (r : S.Run) : Time :=
  min (protEnd S q b₁ r + (q.cohortAhead : Time) * (S.pt r).env.ΔAC) (S.pt r).horizon

/-- The outage cohort of `[b₀, b₁)` at `q` in run `r`: the validators honest and awake at the start
of the no-sleep window, on the view retained through the cohort point (a validator compromised by
then is not in it). This is the right-hand side of `CohortOn`. -/
noncomputable def cohort (q : ProtQ) (b₀ b₁ : Time) (r : S.Run) : Finset V :=
  ((S.pt r).retain (protCohortAt S q b₁ r)).awakeAt (protStart S q b₀ r)

/-- **Slice 2's run class** at `q`, armed at `T`, with outage `[b₀, b₁)`: the contract's
`Outage K T b₀ b₁` without its arming lag, with the point's budget, windows, threshold and catch-up
in place of the contract's, plus the cohort refinement and the fault cap. It reads no contract.

* Times: `0 ≤ T`, `b₀ ≤ b₁`, `b₁ ≤ b₀ + β·ΔAC` (`OutageTimes` without `T + lag·ΔAC ≤ b₀`).
* Network: synchronous before `b₀`, partially synchronous with GST `b₁` (`OutageNet`).
* Participation: η-sleepy on `[0, horizon]` with the point's threshold `θ`, catch-up
  `catchUp·ΔAC`, look-back `η·ΔAC` and sleepy look-ahead `ahead·ΔAC` (`EtaSleepyOn`).
* On the view retained through `protCohortAt`: no honest validator falls asleep in the no-sleep
  window `[protStart, protEnd]` (`NoSleepOn`), the validators compromised by the cohort point and
  the late wakers of the window are fewer than the cohort (`CohortOn`), and the cohort has at least
  `A` members.
* At most `fcap` validators are compromised by the horizon.

It mentions no bound: the arming lag is the profile's premise. -/
def ProtClass (q : ProtQ) (T b₀ b₁ : Time) (r : S.Run) : Prop :=
  0 ≤ T ∧ b₀ ≤ b₁ ∧ b₁ ≤ b₀ + (q.β : Time) * (S.pt r).env.ΔAC ∧
    (S.log r).OutageNet (S.pt r) b₀ b₁ ∧
    (S.pt r).EtaSleepyOn q.θ ((q.η : Time) * (S.pt r).env.ΔAC) (protCDur S q r)
      ((q.ahead : Time) * (S.pt r).env.ΔAC) 0 (S.pt r).horizon ∧
    ((S.pt r).retain (protCohortAt S q b₁ r)).NoSleepOn (protStart S q b₀ r) (protEnd S q b₁ r) ∧
    ((S.pt r).retain (protCohortAt S q b₁ r)).CohortOn (protStart S q b₀ r) (protEnd S q b₁ r) ∧
    q.A ≤ (cohort S q b₀ b₁ r).card ∧
    (S.pt r).faultCount (S.pt r).horizon ≤ q.fcap

/-- **The protection profile** with arming-lag bound `ℓ` and recovery bound `rec`. At every point
`q` with finite `ℓ q = c` and `rec q = d`, for every outage `[b₀, b₁)` armed at `T` with
`T + c·ΔAC ≤ b₀`, on valid runs of the class at `q`, unless the run's excuse holds: what a node
ready at `T` reads from the source output `q.src` is a prefix of what every node ready at a time
`t ∈ [b₁ + d·ΔAC, horizon]` reads from the resilience target (the available output when provided,
as in `persists`), ready at the point's catch-up. A `⊤` bound claims nothing; a source the
protocol does not provide claims nothing. Both bounds are monotone in the adverse parameters. -/
structure ProtectionProfile (ℓ rec : Bound ProtQ) : Prop where
  mono : AdverseMonotone ℓ ∧ AdverseMonotone rec
  protects : ∀ q (c d : ℕ), ℓ q = c → rec q = d → ∀ g, S.schema.output q.src.cap = some g →
    ∀ T b₀ b₁, S.Holds
      (fun r => ProtClass S q T b₀ b₁ r ∧ T + (c : Time) * (S.pt r).env.ΔAC ≤ b₀)
      (fun r => (S.trace r).ProtectedReadyFrom (protCDur S q r) g (resilienceTarget S.schema g) T
        (b₁ + (d : Time) * (S.pt r).env.ΔAC))

/-- **Continuous protection** with arming-lag bound `ℓ` (B11's stronger variant, the defensible
part of B12; optional per protocol): on the same runs as `ProtectionProfile.protects`, the read of
the source at `T` by a node ready at `T` is a prefix of the read of the resilience target by every
node ready at a time `t ∈ [b₀, horizon]`, so a protected read never disappears during the outage. It
implies the protection claim at every recovery bound. **Not ranked:** comparing
`ContinuousProtection` bounds across protocols needs its own coverage, with a reader ready during
the outage and a nonempty source ledger, which `ProtDomainCoverage` does not ask. -/
structure ContinuousProtection (ℓ : Bound ProtQ) : Prop where
  mono : AdverseMonotone ℓ
  protectsFrom : ∀ q (c : ℕ), ℓ q = c → ∀ g, S.schema.output q.src.cap = some g →
    ∀ T b₀ b₁, S.Holds
      (fun r => ProtClass S q T b₀ b₁ r ∧ T + (c : Time) * (S.pt r).env.ΔAC ≤ b₀)
      (fun r => (S.trace r).ProtectedReadyFrom (protCDur S q r) g (resilienceTarget S.schema g) T
        b₀)

/-- **Protection domain coverage** of `(ℓ, rec)`: for every domain-feasible point with finite `ℓ`
and `rec`, the protocol provides the source output, and a valid, excuse-free run of the class at `q`
(a representative: its cohort has at least `A` members and its fault count is at most `fcap`, not
exactly `A` or `fcap`), armed with
`T + ℓ q·ΔAC ≤ b₀`, makes the claim active (`OutageActive` with recovery delay `rec q·ΔAC`: a node
ready at `T`, an honest node asleep in the outage, which lasts at least `ΔAC`, and a node ready at a
time from the recovery point within the horizon). The `A = 0` column is covered by any run of the
class: exact `A = 0` is unattainable. -/
structure ProtDomainCoverage (ℓ rec : Bound ProtQ) : Prop where
  covers : ∀ q : ProtQ, q.DomainFeasible V → ∀ c d : ℕ, ℓ q = c → rec q = d →
    (S.schema.output q.src.cap).isSome ∧ ∃ r T b₀ b₁, S.Valid r ∧ ¬ S.Excuse r ∧
      ProtClass S q T b₀ b₁ r ∧ T + (c : Time) * (S.pt r).env.ΔAC ≤ b₀ ∧
      OutageActive (protCDur S q r) ((d : Time) * (S.pt r).env.ΔAC) T b₀ b₁ (S.pt r)

/-- **Protection boundary coverage** of `(ℓ, rec)`: as `ProtDomainCoverage`, at every
boundary-feasible point, by a witness that **attains the environment parameters**: the outage
lasts exactly `β·ΔAC`, the cohort has exactly `A` members, and exactly `fcap` validators are
compromised by the horizon. -/
structure ProtBoundaryCoverage (ℓ rec : Bound ProtQ) : Prop where
  covers : ∀ q : ProtQ, q.BoundaryFeasible V → ∀ c d : ℕ, ℓ q = c → rec q = d →
    (S.schema.output q.src.cap).isSome ∧ ∃ r T b₀ b₁, S.Valid r ∧ ¬ S.Excuse r ∧
      ProtClass S q T b₀ b₁ r ∧ T + (c : Time) * (S.pt r).env.ΔAC ≤ b₀ ∧
      b₁ - b₀ = (q.β : Time) * (S.pt r).env.ΔAC ∧ (cohort S q b₀ b₁ r).card = q.A ∧
      (S.pt r).faultCount (S.pt r).horizon = q.fcap ∧
      OutageActive (protCDur S q r) ((d : Time) * (S.pt r).env.ΔAC) T b₀ b₁ (S.pt r)

/-- **The order implies class inclusion**: a run of the class at `q` is a run of the class at every
`q' ≥ q` with a nonnegative threshold, for every system, arming time and outage. The sign premise
is needed by the look-ahead direction: at `θ < 0` an earlier retention can break the sleepy budget
(`θ = −1`, no ready validator: one fault charged satisfies it, none charged does not). A threshold
`θ ≥ 1` makes the class empty, so no upper bound is needed. -/
def ProtClassMono : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (S : System V) (q q' : ProtQ) (T b₀ b₁ : Time)
    (r : S.Run), q ≤ q' → 0 ≤ q'.θ → ProtClass S q T b₀ b₁ r → ProtClass S q' T b₀ b₁ r

/-- The points at which `persists` applies: the stable source, and numbers that put the class
inside the contract's `Outage` and the point's ready validators among the contract's (`β ≤ budget`;
a look-back `η ≥ K.η`, a sleepy look-ahead `ahead ≥ K.ahead` and a threshold `θ ≥ K.θ`, stronger
participation premises; a no-sleep margin `noSleep ≥ K.noSleep` at the contract's retention offset
`noSleep + cohortAhead`, a wider window on the same retained view; a catch-up
`catchUp ≥ K.catchUp`, which leaves fewer ready validators, so a stronger sleepy premise and fewer
sources and readers than `persists` covers). Any cohort bound and fault cap. The points with
`q.θ ≥ 1` among them have an empty class, so the finite default there is a vacuous implication;
they are infeasible for coverage and are never ranked. -/
def PersistsPoint (K : Contract Prog) (q : ProtQ) : Prop :=
  q.src = .stable ∧ q.β ≤ K.params.budget ∧ K.params.η ≤ q.η ∧ K.params.ahead ≤ q.ahead ∧
    K.params.noSleep ≤ q.noSleep ∧
    q.noSleep + q.cohortAhead = K.params.noSleep + K.params.cohortAhead ∧ K.params.θ ≤ q.θ ∧
    K.params.catchUp ≤ q.catchUp

instance (K : Contract Prog) (q : ProtQ) : Decidable (PersistsPoint K q) := by
  unfold PersistsPoint; infer_instance

/-- The default arming lag: the contract's `lag` at the points where `persists` applies
(`PersistsPoint`); `⊤` elsewhere. -/
def protLagDefault (K : Contract Prog) : Bound ProtQ := fun q =>
  if PersistsPoint K q then (K.params.lag : WithTop ℕ) else ⊤

/-- The default recovery delay: the contract's `recovery` at the points where `persists` applies
(`PersistsPoint`); `⊤` elsewhere. -/
def protRecDefault (K : Contract Prog) : Bound ProtQ := fun q =>
  if PersistsPoint K q then (K.params.recovery : WithTop ℕ) else ⊤

/-- **The protection default** (`ProtectionDefault`): every system with the L0 property table has
the protection profile `(protLagDefault, protRecDefault)`. The proof instantiates `persists`: at a
`PersistsPoint`, the class with the arming premise `T + lag·ΔAC ≤ b₀` is contained in
`Outage K T b₀ b₁` (the cohort point is the contract's `cohortAt`, and `NoSleepOn` with `CohortOn`
on the wider window give both on the contract's window; the sleepy premise transfers through
`θ ≤ ½` from `Behaviour.admissible`), the point's ready validators are ready at the contract's
catch-up, and the profile's target and recovery point are `persists`'s. -/
def ProtectionDefault : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (Prog : Type) (S : System V) (X : Progress S Prog)
    (K : Contract Prog), Behaviour S X K →
      ProtectionProfile S (protLagDefault K) (protRecDefault K)

end Consensus.Comparison

end
