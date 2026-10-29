module
public import ConsensusSpec.Problem.Regimes
public import ConsensusSpec.Problem.Properties
public import Mathlib.Tactic

@[expose] public section

/-! # The definition of a good protocol (L0)

`Good S X K`: system `S`, with progress requirements read by `X`, meets the
contract `K` (numbers only). Three parts:

* `Behaviour`: a fixed table of properties, each under a fixed regime
  (`Regimes.lean`); the table is on `Behaviour`.
* `Adequate`: the acceptance interface that rules out a vacuous system
  (coverage of every environment point and GST by a valid, excuse-free run;
  prefix closure).
* `Realizable` (for at least five validators): every regime, at every `Δ`,
  every GST and arbitrarily late outages, is met by a clean witness with
  active claims, plus a sleepy stress witness with at most two honest
  validators awake.

What L0 cannot check, and L1 proves once for the model: the log is the
engine's real communication (`Model.sysOf_log_faithful`), and the external data
are fixed before execution (`Model.sysExternal`: the PKI and the selection).
Claims hold on valid runs unless the run's excuse holds (an observed hash
collision in the model): `System.Holds`. There are no other escapes. -/

namespace Consensus

namespace System

variable {V : Type}

/-- On valid runs satisfying `A`, `P` holds or the excuse holds. -/
def Holds (S : System V) (A P : S.Run → Prop) : Prop :=
  ∀ r, S.Valid r → A r → P r ∨ S.Excuse r

/-- On valid runs, `P` holds. -/
def HoldsAlways (S : System V) (P : S.Run → Prop) : Prop :=
  ∀ r, S.Valid r → P r

end System

/-- The output resilience is measured against: the available output if
provided, else the same output. -/
def resilienceTarget (O : OutputSchema) (g : O.Id) : O.Id := (O.output .available).getD g

/-- The schema serves a ledger: it provides a final output or an available
one (possibly with others). A schema that provides neither (no output at all,
or only a stable one) is not a consensus service; `Behaviour` requires this. -/
def OutputSchema.Serves (O : OutputSchema) : Prop :=
  (O.output .final).isSome ∨ (O.output .available).isSome

/-- External run data and its admissibility: what a run fixes before execution
besides its environment point (in the model: the PKI and the selection). -/
structure External {V : Type} (S : System V) where
  /-- The external data of runs in environment `E`. -/
  Ext : Env V → Type
  /-- The external data of a run. -/
  ext : (r : S.Run) → Ext (S.trace r).point.env
  /-- Admissible external data (in the model: the protocol's selection spec). -/
  Admits : (E : Env V) → Ext E → Prop

/-- Progress requirements (leader-based progress), read **only** from the
participation of the environment point — awake profile, honest set, horizon —
and the external data; not from the submissions. `holds π c start stop p x`:
requirement `π` with catch-up `c` holds on the window `[start, stop]`. A smaller
window or a smaller horizon is weaker. -/
structure Progress {V : Type} (S : System V) (Prog : Type) extends External S where
  holds : Prog → Time → Time → Time → (p : EnvPoint V) → Ext p.env → Prop
  mono : ∀ {π : Prog} {c s s' e e' : Time} {p : EnvPoint V} {x : Ext p.env},
    s ≤ s' → e' ≤ e → holds π c s e p x → holds π c s' e' p x
  shrink : ∀ {π : Prog} {c s e : Time} {p : EnvPoint V} {x : Ext p.env} {b : Time},
    b ≤ p.horizon → holds π c s e p x → holds π c s e { p with horizon := b } x
  /-- Progress does not read the transaction submissions. -/
  submit_irrel : ∀ {π : Prog} {c s e : Time} {p : EnvPoint V} {x : Ext p.env}
    (σ : V → Time → List Tx), holds π c s e p x → holds π c s e { p with submit := σ } x

namespace System

variable {V : Type} (S : System V) {Prog : Type}

/-- The progress requirement of `cap` at `i` holds on `[start, stop]` in run `r`. -/
def prog (X : Progress S Prog) (K : Contract Prog) (cap : Capability) (i : K.Idx)
    (start stop : Time) (r : S.Run) : Prop :=
  X.holds (K.progress cap i) (S.cDur K r) start stop (S.pt r) (X.ext r)

variable [Fintype V] [DecidableEq V]

/-- A clean witness: valid, no excuse, a faulty and an honest validator. -/
def Witness (r : S.Run) : Prop :=
  S.Valid r ∧ ¬ S.Excuse r ∧ (S.pt r).faulty.Nonempty ∧ (S.pt r).honest.Nonempty

end System

variable {V : Type} [Fintype V] [DecidableEq V] {Prog : Type}

/-- **Behaviour**: the fixed property table. Each claim names the output it
reads; regimes and run quantities are the `System` accessors of `Regimes.lean`.
Besides laws, admissible numbers, a served ledger and `nonFraming`:

| outputs | always | any network | healthy from GST | sleepy | outage |
|---|---|---|---|---|---|
| all | `nested` | | `healthyLive` | | |
| final | `finalMonotone` | `finalAccountable` | | | |
| available, stable | | | `healedSafe` | `sleepySafe`, `sleepyLive` | |
| stable | | | | | `persists` |
-/
structure Behaviour (S : System V) (X : Progress S Prog) (K : Contract Prog) :
    Prop where
  laws : S.Laws
  admissible : K.params.Admissible
  serves : S.schema.Serves
  /-- Honest validators are never convicted by honest evidence. -/
  nonFraming : S.HoldsAlways S.NonFraming
  /-- Lower-rank outputs are prefixes of higher-rank ones, unconditionally. -/
  nested : ∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank → S.schema.output c₁ = some g₁ →
    S.schema.output c₂ = some g₂ → S.HoldsAlways (fun r => (S.trace r).Nested g₁ g₂)
  /-- The final output never rolls back, unconditionally. -/
  finalMonotone : ∀ g, S.schema.output .final = some g →
    S.HoldsAlways (fun r => (S.trace r).Monotone g 0)
  /-- Local accountability of the final output for fraction `α`, in every
  environment. -/
  finalAccountable : ∀ g, S.schema.output .final = some g →
    S.Holds (fun _ => True) (fun r => S.AccountablySafe r K.params.α g 0)
  /-- Every provided output, at every index: healthy from a GST with progress
  from `ready` to the horizon, transaction liveness from the heal point. -/
  healthyLive : ∀ cap g, S.schema.output cap = some g → ∀ i gst, S.Holds
    (fun r => S.Healthy K gst r ∧ S.prog X K cap i (S.ready K gst r) (S.pt r).horizon r)
    (fun r => (S.trace r).TxLive (S.cDur K r) g (S.heal K cap i gst r) (S.lat K cap i r))
  /-- Available and stable: ready-reader safety when sleepy. -/
  sleepySafe : ∀ cap g, (cap = .available ∨ cap = .stable) → S.schema.output cap = some g →
    S.Holds (S.Sleepy K) (fun r => (S.trace r).ReadySafe (S.cDur K r) g 0)
  /-- Available and stable: transaction liveness when sleepy, with progress on
  the whole run. -/
  sleepyLive : ∀ cap g, (cap = .available ∨ cap = .stable) → S.schema.output cap = some g →
    ∀ i, S.Holds (fun r => S.Sleepy K r ∧ S.prog X K cap i 0 (S.pt r).horizon r)
      (fun r => (S.trace r).TxLive (S.cDur K r) g 0 (S.lat K cap i r))
  /-- Available and stable: ready-reader safety from the heal point when
  healthy from a GST ("stay in recovery"; progress needed only on
  `[ready, heal]`). -/
  healedSafe : ∀ cap g, (cap = .available ∨ cap = .stable) → S.schema.output cap = some g →
    ∀ i gst, S.Holds
      (fun r => S.Healthy K gst r ∧ S.prog X K cap i (S.ready K gst r) (S.heal K cap i gst r) r)
      (fun r => (S.trace r).ReadySafe (S.cDur K r) g (S.heal K cap i gst r))
  /-- Outage resilience of the stable output, into the resilience target:
  what a node ready at `T` reads as stable is kept by eligible readers. -/
  persists : ∀ g, S.schema.output .stable = some g → ∀ T b₀ b₁,
    S.Holds (S.Outage K T b₀ b₁) (fun r => (S.trace r).ProtectedThrough (S.cDur K r) g
      (resilienceTarget S.schema g) T b₀ b₁)

/-- **Adequacy**: the L0 acceptance interface, which rules out a vacuous
system. -/
structure System.Adequate (S : System V) (X : Progress S Prog) : Prop where
  /-- Every environment has admissible external data (otherwise coverage would
  be vacuous). -/
  admits : ∀ E : Env V, ∃ e : X.Ext E, X.Admits E e
  /-- Coverage: every point with a nonnegative horizon, admissible external
  data and GST `g` has a valid excuse-free run with that point, whose log is
  eager from `g` (`g ≤ 0`: synchronous; `g > horizon`: silent), carrying every
  progress requirement that holds at the point and data (the progress is
  transported, not the data; `Model.sysOf_adequate` keeps both). -/
  covers : ∀ p : EnvPoint V, 0 ≤ p.horizon → ∀ e : X.Ext p.env, X.Admits p.env e → ∀ g : Time,
    ∃ r, S.Valid r ∧ ¬ S.Excuse r ∧ S.pt r = p ∧ (S.log r).EagerFrom (S.pt r) g ∧
      ∀ π c s t, X.holds π c s t p e → X.holds π c s t (S.pt r) (X.ext r)
  /-- Prefix closure: the prefix of a valid run up to any `b ∈ [0, horizon]` is
  a valid run with the same reads, views and log up to `b`, no new excuse, and
  the same progress on windows ending by `b`. -/
  prefixClosed : ∀ r, S.Valid r → ∀ b : Time, 0 ≤ b → b ≤ (S.pt r).horizon → ∃ r', S.Valid r' ∧
    (S.trace r').PrefixOf (S.trace r) b ∧
    (∀ v i, i ≤ (S.trace r').cuts → S.view r' v i = S.view r v i) ∧
    (S.log r').AgreesUpTo (S.log r) b ∧ (S.Excuse r' → S.Excuse r) ∧
    ∀ π c s t, t ≤ b → X.holds π c s t (S.pt r) (X.ext r) → X.holds π c s t (S.pt r') (X.ext r')

/-- Non-vacuity of `TxLive` (used by realizability witnesses): a transaction
submitted at `t ≥ 0` to an awake honest `u`, and a *different* honest `w`
that never receives it by submission, ready at a reachable deadline
`t' ≥ max t start + Δ + D`, `t' ≤ horizon`. -/
def EnvPoint.TxLiveActive (p : EnvPoint V) (c start D : Time) : Prop :=
  ∃ (x : Tx) (t t' : Time) (u w : V), 0 ≤ t ∧ u ∈ p.honest ∧
    p.env.awake u t = true ∧ x ∈ p.submit u t ∧ w ∈ p.honest ∧ w ≠ u ∧
    (∀ τ, x ∉ p.submit w τ) ∧
    max t start + p.env.Δ + D ≤ t' ∧ t' ≤ p.horizon ∧ p.Ready c w t'

/-- Safety is active after `t₀`: two distinct readers ready at one time after
`t₀`, one of them ready again at a later time within the horizon. -/
def SafeActive (c t₀ : Time) (p : EnvPoint V) : Prop :=
  ∃ u w t t', u ≠ w ∧ t₀ < t ∧ t < t' ∧ t' ≤ p.horizon ∧
    p.Ready c u t ∧ p.Ready c w t ∧ p.Ready c u t'

/-- The outage is active: armed at `T ≥ 0` before the window, which lasts at
least `Δ` and ends within the horizon; a node is ready at `T` (a protected
source); an honest node sleeps in the window; an honest node is caught up
before the window and awake through its end (an eligible reader). -/
def OutageActive (c T b₀ b₁ : Time) (p : EnvPoint V) : Prop :=
  0 ≤ T ∧ T < b₀ ∧ b₀ + p.env.Δ ≤ b₁ ∧ b₁ ≤ p.horizon ∧ (∃ u, p.Ready c u T) ∧
    (∃ v ∈ p.honest, ∃ t, b₀ ≤ t ∧ t < b₁ ∧ p.env.awake v t = false) ∧
    ∃ w ∈ p.honest, p.AwakeOnClosed w (max 0 (b₀ - c - 1)) b₁

namespace System

variable (S : System V)

/-- Sleepy liveness of `cap` at `i` is exercised on run `r`: the sleepy
regime, progress on the whole run, and an active liveness claim. -/
def SleepyLive (X : Progress S Prog) (K : Contract Prog) (cap : Capability) (i : K.Idx)
    (r : S.Run) : Prop :=
  S.Sleepy K r ∧ S.prog X K cap i 0 (S.pt r).horizon r ∧
    (S.pt r).TxLiveActive (S.cDur K r) 0 (S.lat K cap i r)

/-- Healed liveness of `cap` at `i` after GST `g` is exercised on run `r`: a
log eager from `g`, the healthy regime from `g`, progress from `ready` to
the horizon, and an active liveness claim from the heal point. -/
def HealthyLive (X : Progress S Prog) (K : Contract Prog) (cap : Capability) (i : K.Idx)
    (g : Time) (r : S.Run) : Prop :=
  (S.log r).EagerFrom (S.pt r) g ∧ S.Healthy K g r ∧
    S.prog X K cap i (S.ready K g r) (S.pt r).horizon r ∧
    (S.pt r).TxLiveActive (S.cDur K r) (S.heal K cap i g r) (S.lat K cap i r)

end System

/-- **Realizability**: every regime is met by a clean witness with active
claims, at every `Δ`, every GST (with a log silent before it), and arbitrarily
late outages; and every provided available or stable output is live, at
some index, with at most two honest validators awake (sleepy stress
witness). -/
structure Realizable (S : System V) (X : Progress S Prog) (K : Contract Prog) :
    Prop where
  sleepy : ∀ cap i (Δ : Time), 0 < Δ → ∃ r, S.Witness r ∧ (S.pt r).env.Δ = Δ ∧
    S.SleepyLive X K cap i r
  healthy : ∀ cap i (Δ g : Time), 0 < Δ → 0 ≤ g → ∃ r, S.Witness r ∧ (S.pt r).env.Δ = Δ ∧
    S.HealthyLive X K cap i g r ∧ SafeActive (S.cDur K r) (S.heal K cap i g r) (S.pt r)
  /-- Sleepy stress: every provided available or stable output is live, at
  some index, on a sleepy witness where at most two honest validators are
  awake at any time, whatever the number of validators (the witness has a
  faulty validator, so with `θ ≤ ½` two ready honest validators meet the
  sleepy threshold). A progress requirement that demands any growing
  participation at every index (e.g. at most `n − 3` validators not ready)
  fails here. -/
  sleepyStress : ∀ cap, (cap = .available ∨ cap = .stable) → (S.schema.output cap).isSome →
    ∀ Δ : Time, 0 < Δ → ∃ i r, S.Witness r ∧ (S.pt r).env.Δ = Δ ∧ S.SleepyLive X K cap i r ∧
      (S.pt r).AwakeAtMost 2
  outage : ∀ (Δ : Time) (k : Nat), 0 < Δ → ∃ r T b₀ b₁, S.Witness r ∧ (S.pt r).env.Δ = Δ ∧
    S.Outage K T b₀ b₁ r ∧ OutageActive (S.cDur K r) T b₀ b₁ (S.pt r) ∧ (k : Time) * Δ ≤ T

/-- **A good protocol.** -/
structure Good (S : System V) (X : Progress S Prog) (K : Contract Prog) : Prop where
  behaviour : Behaviour S X K
  adequate : S.Adequate X
  realizable : 5 ≤ Fintype.card V → Realizable S X K

end Consensus

end
