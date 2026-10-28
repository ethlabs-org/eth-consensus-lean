module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Infix
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! # The consensus problem: objects, environment, systems (layer 0)

What the consensus problem is, independently of any protocol or execution
model: what users read (ledgers of transactions, one per output of the
protocol's output schema, each serving some of three capabilities), what
the world is (an environment: `Δ`, GST, an awake profile; and per run the
honest nodes, a horizon and transaction submissions), and what an
abstract system of runs exposes. No network, messages, signatures or schedule:
the model layer instantiates `System`.

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
accountable). What is claimed for a capability is exactly its specification in
the protocol's contract (`CapSpec`); only `final`'s monotonicity and the
nesting order are unconditional. -/
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

/-- The physical environment: the message delay bound `Δ`, the GST, and when
each node is awake. Time is in integer units; `Δ` is a positive integer number
of units; nodes act at every integer time (unit ticks). -/
structure Env (V : Type) where
  Δ : Time
  Δ_pos : 0 < Δ
  gst : Time
  awake : V → Time → Bool

/-- Awake now, asleep one time unit earlier. -/
def Wakes {V : Type} (E : Env V) (v : V) (t : Time) : Prop :=
  E.awake v t = true ∧ E.awake v (t - 1) = false

/-- Awake throughout the half-open interval `[a, b)`. -/
def AwakeOn {V : Type} (E : Env V) (v : V) (a b : Time) : Prop :=
  ∀ u, a ≤ u → u < b → E.awake v u = true

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

/-- Every honest validator is awake at `t`. -/
def FullAt (t : Time) : Prop := ∀ v ∈ p.honest, p.env.awake v t = true

/-- No honest validator wakes at `t`. -/
def NoWakeAt (t : Time) : Prop := ∀ v ∈ p.honest, ¬ Wakes p.env v t

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

/-- Honest validators awake at some time in `[a, b]`. -/
noncomputable def awakeIn (a b : Time) : Finset V := by
  classical
  exact p.honest.filter (fun v => ∃ u, a ≤ u ∧ u ≤ b ∧ p.env.awake v u = true)

/-- Domain of the environment coverage theorems; not a claim premise. -/
def WellFormed : Prop := 0 ≤ p.horizon

/-- The ready honest validators exceed fraction `θ` of the ready and faulty
ones: `θ · (|ready| + |faulty|) < |ready|`. -/
def ReadyAbove (θ : ℚ) (c t : Time) : Prop :=
  θ * ((p.readyAt c t).card + p.faulty.card : ℚ) < (p.readyAt c t).card

/-- Fewer than fraction `β` of all validators are faulty. -/
def FaultsBelow (β : ℚ) : Prop := (p.faulty.card : ℚ) < β * Fintype.card V

/-- At most `m` validators are faulty (an absolute fault bound, for latencies
that depend on the number of faults). -/
def FaultsAtMost (m : Nat) : Prop := p.faulty.card ≤ m

/-- More than fraction `φ` of all validators are ready. -/
def ReadyOfAll (φ : ℚ) (c t : Time) : Prop :=
  φ * Fintype.card V < ((p.readyAt c t).card : ℚ)

/-- `|ready_t| > θ · |H_[t−η,t] ∪ faulty|`. -/
def EtaSleepy (θ : ℚ) (η c t : Time) : Prop :=
  θ * ((p.awakeIn (t - η) t ∪ p.faulty).card : ℚ) < ((p.readyAt c t).card : ℚ)

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

/-- The same trace with every read mapped by `f`. -/
def map {β : Type} (f : List α → List β) : Trace V β Id :=
  ⟨tr.point, tr.cuts, tr.cutTime, fun g v i => f (tr.read g v i)⟩

end Trace

/-- A system: an output schema and a space of runs; for each run its trace
of ledgers (one per output identifier), its evidence
(what each node has seen by each cut, and how evidence convicts validators),
whether it is a valid execution, and the excuse under which escaped claims may
fail. The model layer instantiates every field. -/
structure System (V : Type) where
  schema : OutputSchema
  Run : Type
  trace : Run → Trace V Tx schema.Id
  Valid : Run → Prop
  Obs : Type
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
