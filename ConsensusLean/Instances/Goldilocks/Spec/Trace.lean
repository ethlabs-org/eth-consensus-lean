module
public import ConsensusLean.Spec.Problem.Basic

@[expose] public section

/-! # Goldilocks: component traces

The common event and cut carrier over which each component (the AC, the FG) states its
multi-node facts (decomposition §2 D, `Trace`). A run of the node is a sequence of **cuts**; a
cut is one component call of one node (a tick step, a delivery or a restart expands, through the
node handler, to a finite list of FG and AC calls; claims C0.4, C0.5). The cut index is the
run's own order (claims F.5 (run)); a finite run stutters after its last cut.

`Trace N S L` has nodes `N`, per-node component states `S`, and component labels `L`. At cut
`i`, node `node i` is at time `time i`, inside the top-level event `event i` at position
`pos i`. When `label i = some ℓ`, the component of `node i` makes the call that `ℓ` describes
(with its call data and its observations, which the component's own label type fixes) and
moves to the state `post i`; when `label i = none`, the component stutters at that cut (the
other component moves, or nothing does). `state y i`, the state of `y` before cut `i`, is
defined by recursion so that only the node of a labelled cut changes state: stuttering is
structural, not a law. The run also fixes an awake function (claims §"Runs").

The carrier holds no protocol, no premise and no order principle: time monotonicity,
finiteness, the call laws and the network premises are stated by each component's `LocalRun`
and by the run model. -/

namespace Consensus.Goldilocks

/-- A component trace with nodes `N`, component states `S` and labels `L`. -/
structure Trace (N S L : Type) where
  /-- The component state of each node before its first cut. -/
  init : N → S
  /-- The node of cut `i`. -/
  node : Nat → N
  /-- The time of cut `i`. -/
  time : Nat → Time
  /-- The top-level event (a tick, a delivery, a restart) that cut `i` belongs to. -/
  event : Nat → Nat
  /-- The position of cut `i` inside its top-level event. -/
  pos : Nat → Nat
  /-- The component's call at cut `i`, or `none` when the component stutters there. -/
  label : Nat → Option L
  /-- The state of `node i` after cut `i`; read only at labelled cuts. -/
  post : Nat → S
  /-- Whether a node is awake at a time (fixed by the run). -/
  awake : N → Time → Prop
  /-- Optional finite observation horizon, independent of labelled protocol actions;
  `none`: the horizon is the one the labelled cuts cover. -/
  observationHorizon : Option Time := none

namespace Trace

variable {N S L : Type}

open Classical in
/-- The state of node `y` before cut `i`: the initial state, changed only at the labelled cuts
of `y`, to their post-state. -/
noncomputable def state (tr : Trace N S L) (y : N) : Nat → S
  | 0 => tr.init y
  | i + 1 => if tr.node i = y ∧ tr.label i ≠ none then tr.post i else tr.state y i

/-- Cut `i` is a call of node `y`'s component with label `ℓ`. -/
def CallAt (tr : Trace N S L) (y : N) (i : Nat) (ℓ : L) : Prop :=
  tr.node i = y ∧ tr.label i = some ℓ

end Trace

end Consensus.Goldilocks

end
