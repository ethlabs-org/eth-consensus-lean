module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Infix
public import Mathlib.Order.Interval.Finset.Nat
public import AvailableChainModel.Objects.Time

@[expose] public section

/-! # The consensus problem: objects and systems (layer 0)

This layer says what the consensus problem is, independently of any protocol
or execution model: what users read (ledgers of transactions, for three named
outputs), what the world is (an environment point: honest nodes, an awake
profile, private transaction submissions, `Δ` and GST), and what an abstract
system of runs exposes. It fixes no network, no messages, no signatures and no
schedule: those belong to the model layer below, which instantiates `System`.

Transactions are natural numbers: an infinite type, so that "output every
transaction" is not a way to satisfy liveness. Ledgers may contain transactions
that nobody submitted; this layer says nothing about transaction validity. -/

namespace Consensus

open AvailableChain (Time)

/-- A transaction. -/
abbrev Tx := Nat

/-- A ledger: transactions in order. Ledgers are compared by prefix. -/
abbrev Ledger := List Tx

/-- Two ledgers are on one branch. -/
def Compatible (a b : Ledger) : Prop := a <+: b ∨ b <+: a

/-- The three outputs. -/
inductive Out where
  | confirmed
  | stable
  | finalized
  deriving DecidableEq, Repr

/-- The environment of a run: everything the world fixes, and nothing about how
the protocol or the network behaves. Submissions are private and per node: the
transactions submitted to node `v` at time `t`. -/
structure EnvPoint (V : Type) where
  honest : Finset V
  horizon : Time
  Δ : Time
  gst : Time
  awake : V → Time → Bool
  submit : V → Time → List Tx

/-- A system: a space of runs, each with its environment point, a sequence of
event cuts, the ledgers that each node reads at each cut, the evidence that
each node has seen by each cut, and how evidence convicts validators. Cut `i`
is the state after the first `i` events; its time is the time of its last
event (`0` for the empty cut). -/
structure System (V : Type) where
  Run : Type
  env : Run → EnvPoint V
  /-- Valid executions (bound by the model layer). -/
  Valid : Run → Prop
  /-- The number of events. -/
  cuts : Run → Nat
  cutTime : Run → Nat → Time
  read : Run → Out → V → Nat → Ledger
  /-- Observable evidence objects. -/
  Obs : Type
  /-- What node `v` has seen before cut `i`. -/
  view : Run → V → Nat → Set Obs
  /-- Validator `x` is convicted by the evidence set `A`. -/
  convicts : Run → Set Obs → V → Prop
  /-- The excuse under which an escaped claim may fail (the model layer fixes
  it: an observed hash collision). -/
  Excuse : Run → Prop

namespace System

variable {V : Type} (S : System V)

/-- The laws that make the reads and the evidence meaningful. The model layer
proves them for its system. -/
structure Laws : Prop where
  /-- In valid runs, cut times are nondecreasing and within `[0, horizon]`. -/
  cutTime_mono : ∀ r, S.Valid r → ∀ i j, i ≤ j → j ≤ S.cuts r → S.cutTime r i ≤ S.cutTime r j
  cutTime_nonneg : ∀ r, S.Valid r → ∀ i, 0 ≤ S.cutTime r i
  cutTime_le_horizon : ∀ r, S.Valid r → ∀ i, i ≤ S.cuts r → S.cutTime r i ≤ (S.env r).horizon
  /-- More evidence convicts at least as much. -/
  convicts_mono : ∀ r (A B : Set S.Obs) v, A ⊆ B → S.convicts r A v → S.convicts r B v
  /-- Views only grow. -/
  view_mono : ∀ r v i j, i ≤ j → S.view r v i ⊆ S.view r v j

/-- The cut at the end of time `t`: the last cut whose time is at most `t`
(the empty cut if there is none). -/
def endCut (r : S.Run) (t : Time) : Nat :=
  Nat.findGreatest (fun i => S.cutTime r i ≤ t) (S.cuts r)

/-- The ledger of output `g` that node `v` reads at the end of time `t`. -/
def readAt (r : S.Run) (g : Out) (v : V) (t : Time) : Ledger :=
  S.read r g v (S.endCut r t)

/-- Cut `i` is at or after time `t₀`: it includes an event at a time `≥ t₀`
(the cuts before `t₀` and the empty cut are excluded). -/
def InCuts (r : S.Run) (t₀ : Time) (i : Nat) : Prop :=
  S.endCut r (t₀ - 1) < i ∧ i ≤ S.cuts r

/-- Node `v` is ready at `t` with catch-up `c`: honest, and awake throughout
`[max 0 (t − c − 1), t]`. -/
def Ready (r : S.Run) (c : Time) (v : V) (t : Time) : Prop :=
  v ∈ (S.env r).honest ∧ ∀ u, max 0 (t - c - 1) ≤ u → u ≤ t → (S.env r).awake v u = true

/-- Transaction `x` was submitted to every honest node by time `t`. -/
def SubmittedToAll (r : S.Run) (x : Tx) (t : Time) : Prop :=
  ∀ v ∈ (S.env r).honest, ∃ τ, 0 ≤ τ ∧ τ ≤ t ∧ x ∈ (S.env r).submit v τ

/-- The evidence seen by all honest nodes over the whole run. -/
def honestEvidence (r : S.Run) : Set S.Obs :=
  {o | ∃ v ∈ (S.env r).honest, o ∈ S.view r v (S.cuts r)}

end System

end Consensus

end
