module
public import ConsensusLean.Instances.Goldilocks.Spec.Node.Reachable

@[expose] public section

/-! # Goldilocks runs: the run model

The spec's own run model (fradamt-agent/goldilocks `spec/goldilocks-claims.tex` §"Model",
§"Runs"; `spec/shared/composition.tex` §"Model"; decomposition §2 D, `Run`): a **run** is a
`Trace` over the node states, whose labelled cuts are the component calls (`Cut`) of the honest
nodes, grouped by top-level event (`Node.Event`), with `Node.LocalRun` as the law that makes a
trace a run of the protocol. Faulty nodes have no cuts: what they send is an input of the run.

* **Groups.** A top-level event of an honest node `y` at time `t` (a tick, a delivery, a
  restart) expands through the node handler (`Node.exec`) to a non-empty list of cuts; the run
  records them at consecutive indices, with the same `event` id, positions `0, 1, …`, the same
  node and time, and labels exactly the handler's cuts in order (`GroupAt`). The `event` id is
  injective on groups. A dropped future-slot block makes no cuts, so it is not an event of the
  run.
* **Laws** (`LocalRun`): every honest node starts from the initial node state; every labelled
  honest cut lies in a group and obeys the cut law (`Node.CutStep`); a delivery passes the wire
  checks; the cut order is by time from `0`; finitely many cuts in every bounded interval
  (claims §"Runs", the well-foundedness of F.5 (run)); at one time, restarts come before ticks
  and ticks before deliveries across all honest nodes, and the groups of one node at one time
  are in that order (claims F.5 (run), composition.tex §"Model"); an honest node awake at a
  public time ticks exactly once there (closing `Node.Reachable`'s obligation (i)); an honest
  node is called only while awake, its first call after a sleep is a restart, a wake is a
  restart and a restart is a wake (obligations (ii), (iii): sleep = no cuts, wake = a restart
  cut); the awake function is clamped to the run's horizon (a finite run is a prefix of the
  protocol's run and says nothing after its last cut, so no honest node is awake after it; the
  obligation of workbench#5 for `ACLocalRun.restart_at_wake`); **unforgeability** as a run
  condition (claims §"Runs"): a block of an honest proposer that an honest node processes is
  that proposer's own block, made at or before (the slot key of `B.proposer` signs `B`,
  composition.tex §"Blocks"; that an accepted block's proposer is its slot's is an assertion of
  `state_transition`, not a run law); an attestation of an honest signer that an
  honest node processes, or that a processed block carries, was signed by that signer at an
  earlier `fg_attest` cut; an AC message of an honest signer (by the signer map `sg`, a run
  parameter: the AC interface has no signer) that an honest node receives was emitted by that
  signer's node at an earlier cut. Faulty objects have no law: the adversary injects them.
* **Vocabulary.** The run-level events that the premises and the composition statements read:
  restarts, acceptances and refusals of blocks, signings, attestation and message processing,
  emissions and admissions (`SendOrAdmitAt`, mirroring `ACTrace.SendOrAdmit` with the AC's
  `holdsMsg`; `SendOrAdmitAttAt` with the FG pool), the latest wake and the delivery deadline
  `max(τ, w_y) + Δ'` for a delivery parameter `Δ'` (`Δ` for blocks and AC messages, `Δ_F` for
  attestations), and the outputs at a cut (claims §"Outputs").

Premises (`Sync`, `GST`, `Sleepy`, `Healthy`, `NoColl`) are in `Spec/Run/Premises`; the
concrete Goldilocks run (the node with `goldilocksSA`) in `Spec/Run/Goldilocks`; the
projections onto the component traces in `Spec/Run/Projection`. -/

namespace Consensus.Goldilocks

variable {P : Params}

/-- A run trace: per validator, the node state; labelled cuts are component calls. -/
abbrev RunTrace (A : NodeAC P) := Trace (Fin P.n) (NodeState A) (Cut A)

namespace RunTrace

variable {A : NodeAC P} (tr : RunTrace A)

/-- Cut `i` is a call of `y` (any label). -/
def IsCall (y : Fin P.n) (i : Nat) : Prop := ∃ c, tr.CallAt y i c

/-- `y` makes no call at a cut in `[j, i)`. -/
def NoCallBetween (y : Fin P.n) (j i : Nat) : Prop := ∀ k, j ≤ k → k < i → ¬ tr.IsCall y k

/-- `y` restarts at cut `k` (an `ac_restart` call). -/
def RestartAt (y : Fin P.n) (k : Nat) : Prop :=
  ∃ ℓ : ACLabel A, tr.CallAt y k (.ac ℓ) ∧ ℓ.call = .restart

/-- `y` processes the block `B` at cut `k`: an `fg_on_block(B)` call, accepted or refused. -/
def BlockCallAt (y : Fin P.n) (k : Nat) (B : A.Blk) : Prop :=
  ∃ acc, tr.CallAt y k (.fg (.block B acc))

/-- `y` accepts `B` at cut `k` (an accepted `fg_on_block(B)` call). -/
def AcceptAt (y : Fin P.n) (k : Nat) (B : A.Blk) : Prop := tr.CallAt y k (.fg (.block B true))

/-- The block `B` is `y`'s own, processed at cut `k`: an `fg_on_block(B)` call inside a tick
(position `≠ 0`; a delivery is a group of its own, at position `0`), which the proposal step
makes (`Node.proposeBlock`). -/
def OwnBlockAt (y : Fin P.n) (k : Nat) (B : A.Blk) : Prop :=
  tr.BlockCallAt y k B ∧ tr.pos k ≠ 0

/-- `y` signs the attestation `a` at cut `k` (an `fg_attest` call that signs). -/
def SignAt (y : Fin P.n) (k : Nat) (a : FG.Att P.n) : Prop :=
  ∃ src, tr.CallAt y k (.fg (.attest src (some a)))

/-- `y` processes the attestation `a` at cut `k` (an `fg_on_attestation(a)` call, from the wire
or its own). -/
def AttCallAt (y : Fin P.n) (k : Nat) (a : FG.Att P.n) : Prop :=
  tr.CallAt y k (.fg (.attestation a))

/-- `y` processes the attestation `a` at cut `k`, as such or carried by an accepted block. -/
def ProcessAttAt (y : Fin P.n) (k : Nat) (a : FG.Att P.n) : Prop :=
  tr.AttCallAt y k a ∨ ∃ B, tr.AcceptAt y k B ∧ a ∈ B.fgPayload

/-- `y` emits the AC message `m` at cut `k` (an emission of its AC call). -/
def EmitAt (y : Fin P.n) (k : Nat) (m : A.Msg) : Prop :=
  ∃ ℓ : ACLabel A, tr.CallAt y k (.ac ℓ) ∧ ∃ e ∈ ℓ.emits, e.msg = m

/-- `y` receives the AC message `m` at cut `k` (an `ac_on_message(m)` call). -/
def MsgCallAt (y : Fin P.n) (k : Nat) (m : A.Msg) : Prop :=
  ∃ ℓ : ACLabel A, tr.CallAt y k (.ac ℓ) ∧ ℓ.call = .message m

/-- `y` processes the AC message `m` at cut `k`: an `ac_on_message(m)` call, or an emission of
its call there (an own message is processed at once; `ACTrace.ProcessAt`). -/
def ProcessMsgAt (y : Fin P.n) (k : Nat) (m : A.Msg) : Prop :=
  tr.MsgCallAt y k m ∨ tr.EmitAt y k m

/-- `x` sends the AC message `m` at cut `i` (an emission), or admits it there: an AC call other
than a restart after which its AC holds `m` and before which it did not, whether `m` came as a
message or from the payload of a block the call accepts (`ACTrace.SendOrAdmit`; an honest node
forwards an AC message when its AC admits it; composition.tex §"Model", goldilocks#28, #32). -/
def SendOrAdmitAt (x : Fin P.n) (i : Nat) (m : A.Msg) : Prop :=
  ∃ ℓ : ACLabel A, tr.CallAt x i (.ac ℓ) ∧ ((∃ e ∈ ℓ.emits, e.msg = m) ∨
    (ℓ.call ≠ .restart ∧ ¬ A.holdsMsg (tr.state x i).ac m ∧ A.holdsMsg (tr.post i).ac m))

/-- `x` signs the attestation `a` at cut `i`, or admits it there: an FG call after which its
pool holds `a` and before which it did not (from the wire, or carried by an accepted block; an
honest node forwards an attestation when it admits it). -/
def SendOrAdmitAttAt (x : Fin P.n) (i : Nat) (a : FG.Att P.n) : Prop :=
  tr.SignAt x i a ∨
    ∃ ℓ : FGLabel P A.Payload, tr.CallAt x i (.fg ℓ) ∧
      a ∉ (tr.state x i).fg.atts ∧ a ∈ (tr.post i).fg.atts

/-- The blocks that occur in the run: the blocks an honest node processes (`fg_on_block`,
accepted or refused; every block of an honest tree and every honest proposal is one). -/
def Occurs (B : A.Blk) : Prop := ∃ y k, tr.BlockCallAt y k B

/-- The blocks of the honest nodes' accepted trees, before any cut. -/
def HonestBlocks (H : Set (Fin P.n)) : Set A.Blk :=
  {B | ∃ y ∈ H, ∃ i, B ∈ (tr.state y i).fg.tree}

open Classical in
/-- The latest wake of `y` at or before cut `k`: the time of its latest restart at a cut `≤ k`
(`⊥` if none; a node awake at time `0` has not restarted). -/
noncomputable def lastWake (y : Fin P.n) : Nat → WithBot Time
  | 0 => if tr.RestartAt y 0 then (tr.time 0 : WithBot Time) else ⊥
  | k + 1 => if tr.RestartAt y (k + 1) then (tr.time (k + 1) : WithBot Time) else lastWake y k

/-- The delivery deadline at `y` for an object of time `τ` with delivery parameter `Δ'`, as of
cut `k`: `max(τ, w_y) + Δ'`. -/
noncomputable def deadline (y : Fin P.n) (k : Nat) (τ Δ' : Time) : Time :=
  Option.elim (tr.lastWake y k) τ (fun w => max τ w) + Δ'

/-- Cut `j` is the first cut of the run at a time `≥ t`: every earlier cut is before `t`, so
the state before `j` is "the state at `t`" of every node (the claims' "at `t_s`"). -/
def FirstCutFrom (j : Nat) (t : Time) : Prop := t ≤ tr.time j ∧ ∀ k < j, tr.time k < t

/-- `y` processes its own proposal `B` at cut `k`, at the start of `B`'s slot (G1.10's "a block
that `y` proposes at `T + Δ`"). -/
def ProposesAt (y : Fin P.n) (k : Nat) (B : A.Blk) : Prop :=
  tr.OwnBlockAt y k B ∧ B.proposer = y ∧ tr.time k = P.slotTime B.slot

/-- The time `t` is within the run's horizon: some cut at or after it is labelled. -/
def InHorizon (t : Time) : Prop := ∃ i, tr.label i ≠ none ∧ t ≤ tr.time i

/-- The finalized output of `y` before cut `i`: `Σ.F` (claims §"Outputs"). -/
noncomputable def finalizedAt (y : Fin P.n) (i : Nat) : A.Blk := (tr.state y i).fg.F

/-- The confirmed output of `y` before cut `i`, at its time: `ac_confirmed(𝒜, fg_to_ac(Σ), t)`. -/
noncomputable def confirmedAt (y : Fin P.n) (i : Nat) : A.Blk :=
  A.confirmed (tr.state y i).ac (Node.frame (tr.state y i)) (tr.time i)

/-- The head of `y` before cut `i`, at its time: `ac_head(𝒜, fg_to_ac(Σ), t)`. -/
noncomputable def headAt (y : Fin P.n) (i : Nat) : A.Blk :=
  A.head (tr.state y i).ac (Node.frame (tr.state y i)) (tr.time i)

/-- The cuts of the top-level event `e` of `y` at time `t` start at cut `j`: the handler's cuts
(`Node.exec` on the state before `j`), non-empty, at `j, j + 1, …`, with one `event` id, the
positions `0, 1, …`, the node `y`, the time `t`, and nothing else under that id. -/
def GroupAt (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n) (j : Nat) (t : Time)
    (e : Node.Event A) : Prop :=
  let cs := (Node.exec dg y (tr.state y j) t e).2
  cs ≠ [] ∧
    (∀ k, (hk : k < cs.length) → tr.node (j + k) = y ∧ tr.time (j + k) = t ∧
      tr.event (j + k) = tr.event j ∧ tr.pos (j + k) = k ∧ tr.label (j + k) = some cs[k]) ∧
    ∀ i, tr.event i = tr.event j → j ≤ i ∧ i < j + cs.length

/-- Cut `i` lies in the group of the event `e` of `y` at time `t` that starts at `j`. -/
def InGroup (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n) (j i : Nat) (t : Time)
    (e : Node.Event A) : Prop :=
  tr.GroupAt dg y j t e ∧ j ≤ i ∧ i < j + (Node.exec dg y (tr.state y j) t e).2.length

/-- The tick of `y` at time `t` starts at cut `j`. -/
def TickAt (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n) (j : Nat) (t : Time) :
    Prop :=
  tr.GroupAt dg y j t .tick

end RunTrace

namespace Node

/-- The phase of a top-level event at a time (claims F.5 (run); composition.tex §"Model"):
restarts first, then ticks, then deliveries. -/
def Event.phase {A : NodeAC P} : Event A → Nat
  | .restart => 0
  | .tick => 1
  | _ => 2

/-- **A run of the node** (claims §"Runs"; decomposition §2 D, `Node.LocalRun`), for the honest
validators `H`, the digest `dg` and the AC message signer map `sg`. -/
structure LocalRun {A : NodeAC P} (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Set (Fin P.n)) (sg : A.Msg → Fin P.n) (tr : RunTrace A) : Prop where
  /-- Each honest node starts from the initial node state. -/
  init : ∀ y ∈ H, tr.init y = Node.init A
  /-- Every labelled cut of an honest node lies in the group of a top-level event. -/
  grouped : ∀ y ∈ H, ∀ i c, tr.CallAt y i c → ∃ j e, tr.InGroup dg y j i (tr.time i) e
  /-- Every labelled cut of an honest node obeys the cut law: an AC cut executes the AC with the
  frame `fg_to_ac(Σ)` and changes only `𝒜`, an FG cut executes its FG call. -/
  cutLaw : ∀ y ∈ H, ∀ i c, tr.CallAt y i c → CutStep y (tr.time i) (tr.state y i) c (tr.post i)
  /-- A delivery to an honest node passes the wire checks. -/
  wire : ∀ y ∈ H, ∀ j t e, tr.GroupAt dg y j t e → WireOK dg e
  /-- Cuts are at times from `0` on. -/
  time_nonneg : ∀ i, 0 ≤ tr.time i
  /-- The cut order is by time. -/
  time_mono : Monotone tr.time
  /-- Finitely many labelled cuts in every bounded interval. -/
  finite : ∀ T : Time, {i | tr.label i ≠ none ∧ tr.time i ≤ T}.Finite
  /-- At one time, across the honest nodes, restarts come before ticks and ticks before
  deliveries: the groups of one time are in phase order. -/
  phase_order : ∀ y ∈ H, ∀ y' ∈ H, ∀ j j' t e e', tr.GroupAt dg y j t e →
    tr.GroupAt dg y' j' t e' → j < j' → e.phase ≤ e'.phase
  /-- A tick is at a public time. -/
  tick_public : ∀ y ∈ H, ∀ j t, tr.TickAt dg y j t → P.IsPublic t
  /-- One tick per node and time. -/
  tick_unique : ∀ y ∈ H, ∀ j j' t, tr.TickAt dg y j t → tr.TickAt dg y j' t → j = j'
  /-- An honest node awake at a public time (from `0` on) ticks there. -/
  tick_of_awake : ∀ y ∈ H, ∀ t, 0 ≤ t → P.IsPublic t → tr.awake y t → ∃ j, tr.TickAt dg y j t
  /-- An honest node is awake only within the run's horizon. -/
  awake_in_horizon : ∀ y ∈ H, ∀ t, tr.awake y t → tr.InHorizon t
  /-- An honest node is called only while awake. -/
  awake_of_call : ∀ y ∈ H, ∀ i, tr.IsCall y i → tr.awake y (tr.time i)
  /-- The first call of an honest node after it was asleep is a restart. -/
  restart_of_sleep : ∀ y ∈ H, ∀ i (u : Time), tr.IsCall y i → 0 ≤ u → u < tr.time i →
    ¬ tr.awake y u → (∀ j < i, tr.IsCall y j → tr.time j < u) → tr.RestartAt y i
  /-- A wake is a restart: when an honest node is asleep at `u` and awake at a later `v`, it
  restarts at a cut in `(u, v]`. -/
  restart_at_wake : ∀ y ∈ H, ∀ u v : Time, 0 ≤ u → u < v → ¬ tr.awake y u → tr.awake y v →
    ∃ k, tr.RestartAt y k ∧ u < tr.time k ∧ tr.time k ≤ v
  /-- A restart is a wake: the node was asleep after its previous call. -/
  sleep_of_restart : ∀ y ∈ H, ∀ i, tr.RestartAt y i →
    ∃ u : Time, 0 ≤ u ∧ u < tr.time i ∧ ¬ tr.awake y u ∧ ∀ j < i, tr.IsCall y j → tr.time j < u
  /-- A block of an honest proposer that an honest node processes is that proposer's own block,
  processed by the proposer at or before (at the same cut when it is the proposer's own). -/
  block_unforgeable : ∀ y ∈ H, ∀ i B, tr.BlockCallAt y i B → B.proposer ∈ H →
    ∃ j ≤ i, tr.OwnBlockAt B.proposer j B
  /-- An attestation of an honest signer that an honest node processes, as such or carried by a
  processed block, was signed by that signer at an earlier cut. -/
  att_unforgeable : ∀ y ∈ H, ∀ i a,
    (tr.AttCallAt y i a ∨ ∃ B, tr.BlockCallAt y i B ∧ a ∈ B.fgPayload) → a.val ∈ H →
      ∃ j < i, tr.SignAt a.val j a
  /-- An AC message of an honest signer that an honest node receives was emitted by that signer's
  node at an earlier cut. -/
  msg_unforgeable : ∀ y ∈ H, ∀ i m, tr.MsgCallAt y i m → sg m ∈ H → ∃ j < i, tr.EmitAt (sg m) j m

end Node

end Consensus.Goldilocks

end
