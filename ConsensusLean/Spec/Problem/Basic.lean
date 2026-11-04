module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Infix
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.Interval.Finset.Nat
public import ConsensusLean.Init

@[expose] public section

/-! # The consensus problem: objects, environment, systems (L0)

What the consensus problem is, independently of any protocol or execution
model: what users read (ledgers of transactions, one per output of the
protocol's output schema, each serving some of three capabilities), what
the world is (an environment: the bounds `ΔAC` and `ΔFG` and an awake profile; and per run the
honest nodes, a horizon and transaction submissions), and what an
abstract system of runs exposes, including its communication log with opaque
messages (`CommLog`; the network conditions on it are in `Network.lean`). No
signatures or schedule: the model layer (L1) instantiates `System`.

Transactions are natural numbers: an infinite type, so that "output every
transaction" is not a way to satisfy liveness. Ledgers may contain transactions
that nobody submitted: this layer says nothing about transaction validity. -/

namespace Consensus

/-- Time: integer units. -/
abbrev Time := Int

/-- A transaction. -/
abbrev Tx := Nat

/-- A ledger: transactions in order, compared by prefix. -/
abbrev Ledger := List Tx

/-- Two lists are on one branch. -/
def Compatible {α : Type} (a b : List α) : Prop := a <+: b ∨ b <+: a

/-- The three services a protocol may provide. The names state the intent: an
available ledger (live under dynamic participation), a stable ledger
(persists through bounded outages), and a final ledger (safe under asynchrony,
accountable). What is claimed for each capability is fixed in `CorrectProtocol.lean`
(`Behaviour`); a protocol supplies only numbers. -/
inductive Capability where
  | available
  | stable
  | final
  deriving DecidableEq, Repr

/-- Nesting order: `final ⪯ stable ⪯ available` (a lower rank is a prefix of
a higher rank). -/
def Capability.rank : Capability → Nat
  | .final => 0
  | .stable => 1
  | .available => 2

/-- The physical outputs of a protocol and which capability each serves. Two
capabilities may map to one output (aliasing); `none` means not provided. -/
structure OutputSchema where
  /-- The output identifiers. -/
  Id : Type
  /-- The output serving each capability, if provided. -/
  output : Capability → Option Id

/-- The physical environment: the delay bound `ΔAC` of messages and
transactions, the delay bound `ΔFG` of FG attestations (the protocol's FG attestation
messages, `CommLog.fgAtt`), and when each node is awake. Time is in integer
units; both bounds are positive integer numbers of units, and neither is
assumed to bound the other; nodes act at every integer time (unit ticks). The
GST is not part of the environment: it is a parameter of the network regimes
(`Network.lean`, `Regimes.lean`). -/
structure Env (V : Type) where
  ΔAC : Time
  ΔAC_pos : 0 < ΔAC
  ΔFG : Time
  ΔFG_pos : 0 < ΔFG
  awake : V → Time → Bool

/-- Awake now, asleep one time unit earlier. -/
def Wakes {V : Type} (E : Env V) (v : V) (t : Time) : Prop :=
  E.awake v t = true ∧ E.awake v (t - 1) = false

/-- The environment point of a run: the environment, the honest nodes, the
horizon, and the adversarially timed transactions submitted to each node.
A transaction submitted to an awake honest node is relayed by the network. -/
structure EnvPoint (V : Type) where
  env : Env V
  honest : Finset V
  horizon : Time
  submit : V → Time → List Tx

namespace EnvPoint

variable {V : Type} (p : EnvPoint V)

/-- `v` is awake throughout `[a, b]`. -/
def AwakeOnClosed (v : V) (a b : Time) : Prop :=
  ∀ u, a ≤ u → u ≤ b → p.env.awake v u = true

/-- `v` is ready at `t` with catch-up `c` (a duration): honest, and awake
throughout `[max 0 (t − c − 1), t]`. -/
def Ready (c : Time) (v : V) (t : Time) : Prop :=
  v ∈ p.honest ∧ p.AwakeOnClosed v (max 0 (t - c - 1)) t

/-- Transaction `x` was submitted to an awake honest node by time `t`. -/
def SubmittedToSome (x : Tx) (t : Time) : Prop :=
  ∃ v ∈ p.honest, ∃ τ, 0 ≤ τ ∧ τ ≤ t ∧ p.env.awake v τ = true ∧ x ∈ p.submit v τ

variable [Fintype V] [DecidableEq V]

/-- The faulty validators. -/
def faulty : Finset V := Finset.univ \ p.honest

/-- The ready honest validators at `t`. -/
noncomputable def readyAt (c t : Time) : Finset V := by
  classical
  exact p.honest.filter (fun v => p.Ready c v t)

/-- The ready honest validators exceed fraction `θ` of the ready and faulty
ones: `θ · (|ready| + |faulty|) < |ready|`. -/
def ReadyAbove (θ : ℚ) (c t : Time) : Prop :=
  θ * ((p.readyAt c t).card + p.faulty.card : ℚ) < (p.readyAt c t).card

/-- The honest validators awake at `t`. -/
noncomputable def awakeAt (t : Time) : Finset V := by
  classical
  exact p.honest.filter (fun v => p.env.awake v t = true)

/-- At most `k` honest validators are awake at every time of `[0, horizon]`. -/
def AwakeAtMost (k : Nat) : Prop :=
  ∀ t, 0 ≤ t → t ≤ p.horizon → (p.awakeAt t).card ≤ k

/-- The honest validators awake at some time in `[a, b]`. -/
noncomputable def awakeIn (a b : Time) : Finset V := by
  classical
  exact p.honest.filter (fun v => ∃ u, a ≤ u ∧ u ≤ b ∧ p.env.awake v u = true)

/-- η-sleepy participation at `t` (look-back `η`, a duration). With `η ≤ 0`
it is plain `ReadyAbove`. With `η > 0` the ready honest validators exceed
fraction `θ` of those awake at some time in `[max 0 (t − η), t]` together with
the faulty ones: `θ · |ready_t ∪ awake_[max 0 (t−η), t] ∪ faulty| < |ready_t|`.
Anyone awake in the window counts against the threshold, even if never ready
(this implies the awake-count form, `EnvPoint.EtaReadyAbove.awakeForm`,
tests). The window is clamped at `0`; `ready_t` is in the union only for
monotonicity. -/
def EtaReadyAbove (θ : ℚ) (η c t : Time) : Prop :=
  if η ≤ 0 then p.ReadyAbove θ c t
  else θ * ((p.readyAt c t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faulty).card : ℚ) <
    (p.readyAt c t).card

end EnvPoint

/-- A trace: the environment point, a sequence of event cuts with their times,
and what each node reads, for each output identifier in `Id`, at each cut. Generic in the element
type, so that the same properties apply to transaction ledgers and to the block
chains of a protocol shape. Cut `i` is the state after the first `i` events; its
time is the time of its last event (`0` for the empty cut). -/
structure Trace (V α Id : Type) where
  point : EnvPoint V
  cuts : Nat
  cutTime : Nat → Time
  read : Id → V → Nat → List α

namespace Trace

variable {V α Id : Type} (tr : Trace V α Id)

/-- The laws of a trace: cut times start at `0`, never decrease, and stay within
the horizon. -/
structure Laws : Prop where
  cutTime_zero : tr.cutTime 0 = 0
  cutTime_mono : ∀ i j, i ≤ j → j ≤ tr.cuts → tr.cutTime i ≤ tr.cutTime j
  cutTime_le_horizon : ∀ i, i ≤ tr.cuts → tr.cutTime i ≤ tr.point.horizon

/-- The cut at the end of time `t`: the last cut whose time is at most `t`. -/
def endCut (t : Time) : Nat := Nat.findGreatest (fun i => tr.cutTime i ≤ t) tr.cuts

/-- The read of output `g` by node `v` at the end of time `t`. -/
def readAt (g : Id) (v : V) (t : Time) : List α := tr.read g v (tr.endCut t)

/-- Cut `i` exists and is at time `≥ t₀` (cut 0 is at time 0, so it counts
for every `t₀ ≤ 0`). -/
def InCuts (t₀ : Time) (i : Nat) : Prop := i ≤ tr.cuts ∧ t₀ ≤ tr.cutTime i

end Trace

/-- A run's communication, with opaque messages `M`: what each node sent and
received at each time, the transactions handed to it at each time (own
submissions and network relay; the inbox is cumulative across restarts), and
the message class: `fgAtt m` marks the FG attestation messages, delivered strictly before
`ΔFG` instead of `ΔAC`. In the model the class is the protocol's (`Model.Run.log`,
`Model.tagLog`), never chosen per run. The network conditions on it are in
`Network.lean`. -/
structure CommLog (V M : Type) where
  sent : V → M → Time → Prop
  recv : V → M → Time → Prop
  inbox : V → Time → List Tx
  fgAtt : M → Prop

/-- A system: an output schema and a space of runs; for each run its trace
of ledgers (one per output identifier), its communication log, its evidence
(what each node has seen by each cut, and how evidence convicts validators),
whether it is a valid execution, and the excuse under which claims may fail
(in the model: an observed hash collision). The model layer instantiates
every field. -/
structure System (V : Type) where
  schema : OutputSchema
  Run : Type
  trace : Run → Trace V Tx schema.Id
  Valid : Run → Prop
  Obs : Type
  /-- The run's communication; messages are the opaque observations `Obs`. -/
  log : Run → CommLog V Obs
  view : Run → V → Nat → Set Obs
  convicts : Run → Set Obs → V → Prop
  Excuse : Run → Prop

namespace System

variable {V : Type} (S : System V)

/-- The laws of a system: valid runs have lawful traces; more evidence convicts
at least as much; views only grow. -/
structure Laws : Prop where
  trace : ∀ r, S.Valid r → (S.trace r).Laws
  convicts_mono : ∀ r (A B : Set S.Obs) v, A ⊆ B → S.convicts r A v → S.convicts r B v
  view_mono : ∀ r v i j, i ≤ j → S.view r v i ⊆ S.view r v j

/-- The evidence that the honest nodes saw over the whole run. -/
def honestEvidence (r : S.Run) : Set S.Obs :=
  {o | ∃ v ∈ (S.trace r).point.honest, o ∈ S.view r v (S.trace r).cuts}

end System

end Consensus

end
