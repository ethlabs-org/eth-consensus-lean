module
public import ConsensusLean.Spec.Problem.Network
public import Mathlib.Data.PNat.Basic

@[expose] public section

/-! # Numbers and regimes (L0)

A protocol's contract (`Contract`) supplies only numbers (`Params`) and a
progress requirement per capability and index. Every duration is a
coefficient of `ΔAC`. `Params.Admissible` bounds the thresholds by the standard
ones (`Params.standard`), so a contract cannot buy its claims with stronger
thresholds. The other numbers are instance numbers that the reviewer reads;
they are not bounded: the generic outage witness of the realizability proofs
assumes of a shape contract's numbers only `Admissible`, so every `η`, `lag`,
`noSleep`, `recovery` and every `budget ≥ 1` is realizable there (with at least
five validators, `ΔAC, ΔFG > 1`, on every window `(T, [b₀, b₁))` with
`OutageTimes` (`0 ≤ T`, `T + lag·ΔAC ≤ b₀`, `b₁ ≤ b₀ + budget·ΔAC`), `T < b₀` and
`b₀ + ΔAC ≤ b₁`, and a horizon at or after `b₁ + recovery·ΔAC`). The direction of
each, for a larger value:

* catch-up (mixed): a reader needs `catchUp·ΔAC` awake to be ready, so fewer
  validators are ready: the participation premises (sleepy, η-sleepy) are
  stronger, and the claims cover fewer readers; the healthy progress premise
  counts only ready proposers but starts later, at
  `ready = max g 0 + catchUp·ΔAC + 1`;
* arming lag: `T + lag·ΔAC ≤ b₀` is a stronger premise;
* outage budget: `b₁ ≤ b₀ + budget·ΔAC` is a weaker premise (longer outages are
  admitted), so the persistence claim is stronger;
* look-back `η`: validators awake anywhere in the longer window count against
  the threshold, a stronger premise;
* outage no-sleep margin: the no-sleep window `[b₀ − noSleep·ΔAC, b₁ + noSleep·ΔAC]`
  is longer, a stronger premise;
* recovery delay: protection starts later (`b₁ + recovery·ΔAC`), a weaker claim;
* heal points: liveness and healed safety start later, weaker claims (and
  healed safety's progress premise covers a longer window);
* latencies: later transaction deadlines, weaker claims;
* look-aheads `ahead`, `cohortAhead`, `committeeAhead`: participation and the outage cohort are
  charged with later faults, and validators compromised by then leave the honest
  support, a stronger premise (`EnvPoint.retain`; `0`: current faults);
* FG delay bound `fgDelay`: the healthy regime assumes `ΔFG ≤ fgDelay·ΔAC`, so a
  larger bound weakens that premise (it admits slower FG attestations) and strengthens the
  claims; it is an upper envelope of the FG delay `ΔFG` for the coefficients, never
  a deadline (FG attestations are delivered strictly before `ΔFG` itself, `CommLog.PSync`)
  and never an order between the delays (`ΔFG < ΔAC` is allowed).

The sleepy and outage regimes carry no FG delay bound: they are stated at every FG
delay `ΔFG > 0` (whether sleepy needs a bound on `ΔFG` is an open audit question).

The three regimes (`System.Sleepy`, `System.Healthy`, `System.Outage`) and
the run quantities they use (`System.cDur`, `heal`, `ready`, `lat`) are read
off a run's environment point and communication log; Outage also reads the
external selection through `External.selected`. Its public committee band is
set by `bandLead` and `bandLen`, independently of run events. The GST is a parameter
of the regimes, not of the environment; an outage run is partially
synchronous with GST `b₁`, so the after-GST entries apply with `g = b₁` when their
other premises hold: `Outage` supplies only the `PSync b₁` part of `Healthy`,
not `HealthyOn` (participation and the fault bound) or the FG delay bound. -/

namespace Consensus

/-- The numbers of a protocol. Durations are `ΔAC`-coefficients. -/
structure Params (Idx : Type) where
  /-- Readers' catch-up `c`: a reader is ready after `c·ΔAC + 1` awake
  (`EnvPoint.Ready`: awake throughout `[t − c·ΔAC − 1, t]`, clamped at `0`). -/
  catchUp : Nat
  /-- Sleepy threshold: `θ·(|ready| + |faulty|) < |ready|`. -/
  θ : ℚ
  /-- Healthy fault bound: fewer than `β·n` faulty (`System.Healthy`). -/
  β : ℚ
  /-- A cover fraction `cover·n`: read by no regime (the outage has no
  absolute participation premise); kept for `Admissible`. -/
  cover : ℚ
  /-- Accountable fraction of the final output. -/
  α : ℚ
  /-- Arming lag: `T + lag·ΔAC ≤ b₀`. -/
  lag : Nat
  /-- Outage budget: `b₁ ≤ b₀ + budget·ΔAC`. -/
  budget : Nat
  /-- Outage look-back `η·ΔAC` (`0`: plain sleepy). -/
  η : Nat
  /-- Outage no-sleep margin: no honest validator falls asleep in
  `[b₀ − noSleep·ΔAC, b₁ + noSleep·ΔAC]` (`System.Outage`). -/
  noSleep : Nat
  /-- Outage recovery delay: protection holds for every ready reader from
  `b₁ + recovery·ΔAC` (`Behaviour.persists`). -/
  recovery : Nat
  /-- Heal point per capability and index (`System.heal`). -/
  heal : Capability → Idx → Nat
  /-- Transaction latency per capability and index. -/
  latency : Capability → Idx → Nat
  /-- FG delay bound `fgDelay ≥ 1`, a `ΔAC`-coefficient: the healthy regime assumes
  `ΔFG ≤ fgDelay·ΔAC` (`System.Healthy`). Unlike the other numbers, a larger bound weakens that
  premise (it admits slower FG attestations) and so strengthens the claims. An upper envelope of
  the FG delay for the coefficients, not an order between the delays (`ΔFG < ΔAC` is allowed),
  and never a deadline (FG attestations are delivered strictly before `ΔFG`). -/
  fgDelay : ℕ+
  /-- Participation look-ahead `ahead·ΔAC` of the sleepy and η-sleepy budgets:
  participation at `t` is counted against the validators compromised by
  `t + ahead·ΔAC` (clamped to the horizon, `EnvPoint.lookAhead`), and only
  validators still honest then count as support (`EnvPoint.retain`). `0`: the
  current faults. A larger look-ahead is a stronger premise, a weaker claim. -/
  ahead : Nat
  /-- Outage cohort look-ahead: the cohort count and the no-sleep window are read
  on the view retained through `outageEnd + cohortAhead·ΔAC` (clamped to the
  horizon, `System.cohortAt`). A larger look-ahead is a stronger premise. -/
  cohortAhead : Nat
  /-- The public outage band starts `bandLead·ΔAC` before the outage. -/
  bandLead : Nat := 0
  /-- The public outage band lasts `bandLen·ΔAC`. -/
  bandLen : Nat := 0
  /-- Committee participation look-ahead, in units of `ΔAC`. -/
  committeeAhead : Nat := 0

namespace Params

variable {Idx : Type}

/-- The standard thresholds `θ = ½`, `β = ⅓`, `cover = ½`, `α = ⅓`,
look-back, no-sleep margin and recovery delay `0`, and FG delay bound `1` (an
instance sets them with
`{ standard … with η := k, noSleep := C, recovery := D, fgDelay := r }`). -/
def standard (catchUp lag budget : Nat) (heal latency : Capability → Idx → Nat) :
    Params Idx where
  catchUp := catchUp
  θ := 1 / 2
  β := 1 / 3
  cover := 1 / 2
  α := 1 / 3
  lag := lag
  budget := budget
  η := 0
  noSleep := 0
  recovery := 0
  heal := heal
  latency := latency
  fgDelay := 1
  ahead := 0
  cohortAhead := 0

/-- Admissible numbers: thresholds no stronger than standard (the healthy
fault bound `β ≥ ⅓`: a larger `β` admits more faults, a weaker premise),
`β ≤ α` (so the healthy regime implies faults below the accountable
fraction), a positive catch-up and a positive budget. -/
structure Admissible (P : Params Idx) : Prop where
  catchUp_pos : 1 ≤ P.catchUp
  θ_range : 0 ≤ P.θ ∧ P.θ ≤ 1 / 2
  β_range : 1 / 3 ≤ P.β
  cover_range : 0 ≤ P.cover ∧ P.cover ≤ 1 / 2
  α_range : P.β ≤ P.α ∧ P.α ≤ 1
  budget_pos : 1 ≤ P.budget

end Params

namespace EnvPoint

variable {V : Type} [Fintype V] [DecidableEq V] (p : EnvPoint V)

/-- Sleepy participation on `[a, b]` with look-ahead `W` (a duration): at each
`t`, the participation of `t` on the view retained through `lookAhead W t`. -/
def SleepyOn (θ : ℚ) (c W a b : Time) : Prop :=
  ∀ t, a ≤ t → t ≤ b → (p.retain (p.lookAhead W t)).ReadyAbove θ c t

/-- η-sleepy participation (look-back `η`, a duration) on `[a, b]` with
look-ahead `W`. -/
def EtaSleepyOn (θ : ℚ) (η c W a b : Time) : Prop :=
  ∀ t, a ≤ t → t ≤ b → (p.retain (p.lookAhead W t)).EtaReadyAbove θ η c t

/-- Committee η-sleepy participation on a time window. The committee is read at
the observation time, while honesty is retained through the look-ahead. -/
def CommitteeSleepyOn (K : Time → Finset V) (θ : ℚ) (η c W a b : Time) : Prop :=
  ∀ t, a ≤ t → t ≤ b → (K t).Nonempty →
    let q := p.retain (p.lookAhead W t)
    if η ≤ 0 then
      θ * (((q.readyAt c t ∩ K t).card + (q.faultyAt t ∩ K t).card : Nat) : ℚ) <
        ((q.readyAt c t ∩ K t).card : ℚ)
    else
      θ * (((q.readyAt c t ∪ q.awakeIn (max 0 (t - η)) t ∪ q.faultyAt t) ∩ K t).card : ℚ) <
        ((q.readyAt c t ∩ K t).card : ℚ)

/-- Healthy participation on `[max g 0, b]` (see `System.Healthy`): fewer
than fraction `β` of all validators are compromised by `b` (faults only grow, so
at every time up to `b`), and every validator honest at a time of the window is
awake then (full participation). -/
def HealthyOn (β : ℚ) (g b : Time) : Prop :=
  (p.faultCount b : ℚ) < β * Fintype.card V ∧
    ∀ v t, max g 0 ≤ t → t ≤ b → p.HonestAt v t → p.env.awake v t = true

/-- No validator honest at `b` falls asleep in `[a, b]`: one awake at a time of
`[a, b]` stays awake through `b`. Validators may wake inside the window. -/
def NoSleepOn (a b : Time) : Prop :=
  ∀ v, p.HonestAt v b → ∀ t, a ≤ t → t ≤ b → p.env.awake v t = true → p.AwakeOnClosed v t b

/-- The late wakers of `[a, b]`: honest validators asleep at `a` and awake at
some time of `[a, b]`. -/
noncomputable def lateWakers (a b : Time) : Finset V := p.awakeIn a b \ p.awakeAt a

/-- The outage cohort count on `[a, b]`: the validators compromised by `b` and
the late wakers are fewer than the validators honest and awake at `a` (on a
retained view the three sets are disjoint, so fewer than half of all
validators). -/
def CohortOn (a b : Time) : Prop :=
  (p.faultyAt b ∪ p.lateWakers a b).card < (p.awakeAt a).card

/-- The retained cohort inequality restricted to each committee in a fixed public
time band. The cohort window and the band are independent of run events. -/
def CommitteeCohortOn (K : Time → Finset V) (a z bandStart bandEnd : Time) : Prop :=
  ∀ t, max 0 bandStart ≤ t → t ≤ bandEnd → t ≤ p.horizon → (K t).Nonempty →
    ((p.faultyAt z ∪ p.lateWakers a z) ∩ K t).card < (p.awakeAt a ∩ K t).card

end EnvPoint

/-- The outage times: armed at `T ≥ 0` at least `lag·ΔAC` before the window
`[b₀, b₁)`, which lasts at most `budget·ΔAC`. -/
def OutageTimes {Idx : Type} (P : Params Idx) (ΔAC T b₀ b₁ : Time) : Prop :=
  0 ≤ T ∧ T + (P.lag : Time) * ΔAC ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ b₀ + (P.budget : Time) * ΔAC

/-- What a protocol advertises: numbers (`Params`) over a nonempty index type,
and a progress requirement per capability and index. -/
structure Contract (Prog : Type) where
  Idx : Type
  idx_nonempty : Nonempty Idx
  params : Params Idx
  progress : Capability → Idx → Prog

/-- External run data and its admissibility: what a run fixes before execution
besides its environment point (in the model: the PKI and the selection). -/
structure External {V : Type} (S : System V) where
  /-- The external data of runs in environment `E`. -/
  Ext : Env V → Type
  /-- The external data of a run. -/
  ext : (r : S.Run) → Ext (S.trace r).point.env
  /-- Admissible external data (in the model: the protocol's selection spec). -/
  Admits : (E : Env V) → Ext E → Prop
  /-- The population selected at an observation time. A later fault charge reads
  this same set; it does not select again at the charge time. -/
  selected : (E : Env V) → Ext E → Time → Finset V

namespace System

variable {V : Type} (S : System V) {Prog : Type}

/-- The environment point of a run. -/
abbrev pt (r : S.Run) : EnvPoint V := (S.trace r).point

/-- The catch-up duration `catchUp·ΔAC` of run `r`. -/
def cDur (K : Contract Prog) (r : S.Run) : Time := (K.params.catchUp : Time) * (S.pt r).env.ΔAC

/-- The heal point of `cap` at `i` after GST `g` in run `r`: `max g 0 + heal·ΔAC`
(catch-up is inside `heal`; for final, the first finality). -/
def heal (K : Contract Prog) (cap : Capability) (i : K.Idx) (g : Time) (r : S.Run) : Time :=
  max g 0 + (K.params.heal cap i : Time) * (S.pt r).env.ΔAC

/-- The start of progress windows after GST `g` in run `r`,
`max g 0 + catchUp·ΔAC + 1`: for `g > 0` the first time from which a node awake
since `g` is ready; for `g ≤ 0` a sufficient start (the clamp of
`EnvPoint.Ready` makes a node awake since `0` ready earlier). -/
def ready (K : Contract Prog) (g : Time) (r : S.Run) : Time := max g 0 + S.cDur K r + 1

/-- The latency `latency·ΔAC` of `cap` at `i` in run `r`. -/
def lat (K : Contract Prog) (cap : Capability) (i : K.Idx) (r : S.Run) : Time :=
  (K.params.latency cap i : Time) * (S.pt r).env.ΔAC

/-- The no-sleep window of an outage `[b₀, b₁)`:
`[b₀ − noSleep·ΔAC, b₁ + noSleep·ΔAC]` clamped to `[0, horizon]` (no
participation history before `0`, like `Ready`; nothing executes after the
horizon). -/
def outageStart (K : Contract Prog) (b₀ : Time) (r : S.Run) : Time :=
  min (max 0 (b₀ - (K.params.noSleep : Time) * (S.pt r).env.ΔAC)) (S.pt r).horizon

/-- The end of the no-sleep window of an outage `[b₀, b₁)` (`outageStart`). -/
def outageEnd (K : Contract Prog) (b₁ : Time) (r : S.Run) : Time :=
  min (b₁ + (K.params.noSleep : Time) * (S.pt r).env.ΔAC) (S.pt r).horizon

/-- The sleepy look-ahead `ahead·ΔAC` of run `r`. -/
def aheadDur (K : Contract Prog) (r : S.Run) : Time :=
  (K.params.ahead : Time) * (S.pt r).env.ΔAC

/-- Where the outage cohort of `[b₀, b₁)` is charged: `outageEnd + cohortAhead·ΔAC`,
clamped to the horizon. -/
def cohortAt (K : Contract Prog) (b₁ : Time) (r : S.Run) : Time :=
  min (S.outageEnd K b₁ r + (K.params.cohortAhead : Time) * (S.pt r).env.ΔAC) (S.pt r).horizon

/-- The unclamped start of the fixed public committee band. -/
def bandStart (K : Contract Prog) (b₀ : Time) (r : S.Run) : Time :=
  b₀ - (K.params.bandLead : Time) * (S.pt r).env.ΔAC

/-- The end of the fixed public committee band. -/
def bandEnd (K : Contract Prog) (b₀ : Time) (r : S.Run) : Time :=
  S.bandStart K b₀ r + (K.params.bandLen : Time) * (S.pt r).env.ΔAC

/-- The committee participation look-ahead. -/
def committeeAheadDur (K : Contract Prog) (r : S.Run) : Time :=
  (K.params.committeeAhead : Time) * (S.pt r).env.ΔAC

/-- The recovery point of an outage `[b₀, b₁)`: `b₁ + recovery·ΔAC`, from which
every ready reader is protected (`Behaviour.persists`). -/
def recoveryAt (K : Contract Prog) (b₁ : Time) (r : S.Run) : Time :=
  b₁ + (K.params.recovery : Time) * (S.pt r).env.ΔAC

variable [Fintype V] [DecidableEq V]

/-- **Sleepy**: synchrony (`PSync 0`) and, at every time `t`, the validators
ready at `t` and still honest at `t + ahead·ΔAC` (clamped to the horizon) exceed
fraction `θ` of them and the validators compromised by then (look-ahead `aheadDur`). -/
def Sleepy (K : Contract Prog) (r : S.Run) : Prop :=
  (S.log r).PSync (S.pt r) 0 ∧
    (S.pt r).SleepyOn K.params.θ (S.cDur K r) (S.aheadDur K r) 0 (S.pt r).horizon

/-- **Healthy from GST `g`**: partial synchrony with GST `g`, fewer than
`β·n` validators compromised by the horizon, and full participation: every
validator honest at a time of `[max g 0, horizon]` is awake then (awake, not
ready: readiness restricts readers and progress only); and the FG delay is within its bound,
`ΔFG ≤ fgDelay·ΔAC`. -/
def Healthy (K : Contract Prog) (g : Time) (r : S.Run) : Prop :=
  (S.log r).PSync (S.pt r) g ∧ (S.pt r).HealthyOn K.params.β g (S.pt r).horizon ∧
    (S.pt r).env.ΔFG ≤ (K.params.fgDelay : Time) * (S.pt r).env.ΔAC

/-- **Outage `[b₀, b₁)` armed at `T`** (`OutageTimes`): synchronous before
`b₀`, partially synchronous with GST `b₁`, η-sleepy throughout (look-back
`η·ΔAC`; `η = 0` is plain sleepy), with the sleepy look-ahead; and, on the view
retained through `cohortAt` (the surviving cohort: a member compromised by then
counts as faulty), no honest validator falls asleep in the no-sleep window
`[a, z]` (`outageStart`, `outageEnd`; validators may wake in it), and the
compromised validators with the late wakers of `[a, z]` are fewer than the
honest validators awake at `a` (`CohortOn`; hence fewer than half of all
validators, `EnvPoint.CohortOn.two_mul_lt`). No absolute fraction of
validators needs to be awake or ready. The same cohort inequality is required
inside each nonempty selected committee in the public band. Committee η-sleepy
participation holds throughout the horizon with its own look-ahead; both
committee clauses are vacuous at empty selections. -/
def Outage (X : External S) (K : Contract Prog) (T b₀ b₁ : Time) (r : S.Run) : Prop :=
  OutageTimes K.params (S.pt r).env.ΔAC T b₀ b₁ ∧ (S.log r).OutageNet (S.pt r) b₀ b₁ ∧
    (S.pt r).EtaSleepyOn K.params.θ ((K.params.η : Time) * (S.pt r).env.ΔAC) (S.cDur K r)
      (S.aheadDur K r) 0 (S.pt r).horizon ∧
    ((S.pt r).retain (S.cohortAt K b₁ r)).NoSleepOn (S.outageStart K b₀ r) (S.outageEnd K b₁ r) ∧
    ((S.pt r).retain (S.cohortAt K b₁ r)).CohortOn (S.outageStart K b₀ r) (S.outageEnd K b₁ r) ∧
    ((S.pt r).retain (S.cohortAt K b₁ r)).CommitteeCohortOn
      (X.selected (S.pt r).env (X.ext r)) (S.outageStart K b₀ r) (S.outageEnd K b₁ r)
      (S.bandStart K b₀ r) (S.bandEnd K b₀ r) ∧
    (S.pt r).CommitteeSleepyOn (X.selected (S.pt r).env (X.ext r)) K.params.θ
      ((K.params.η : Time) * (S.pt r).env.ΔAC) (S.cDur K r) (S.committeeAheadDur K r)
      0 (S.pt r).horizon

end System

end Consensus

end
