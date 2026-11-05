module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Handlers
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Trace
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Handlers

@[expose] public section

/-! # Goldilocks node: reachable node states and the cut law

`Node.Reachable`: the configurations one honest node reaches by
time-ordered events, under the order of composition.tex §"Model", §"Node" (claims C0.4):
at a time, a restart comes before the tick and before any object of that time; the tick of a
public time runs before the objects received at that time; every own object is processed
inside the step that makes it (`Spec/Node/Handlers`). A configuration is the node state, the
clock and a `Phase`: `pre` while nothing of the current time but restarts has run, `post`
after the tick or an object of that time. A delivery passes the wire checks (`WireOK`). The
relation over-approximates a run, so every fact about it holds of every run; `Spec/Run` owes
three conditions it does not state: (i) an awake node ticks at every public time; (ii) a
restart follows a sleep (no cuts in between), once per wake; (iii) an asleep node receives
nothing.

`CutStep` is the law of one cut, which a run's projections read (claims C0.5): an AC cut
executes the AC on the node's AC state with the frame `fg_to_ac(Σ)` at that cut, and changes
only `𝒜`; an FG cut executes the FG call, and changes only `Σ`, or only `Λ` for `fg_attest`.
`CutChain` strings cuts together; that every handler's cuts form such a chain is claims C0.5. -/

namespace Consensus.Goldilocks.Node

variable {P : Params} {A : NodeAC P}

/-- The phase of a node inside a time: `pre` before the tick of a public time, and before any
object of the time; `post` after. -/
inductive Phase where
  /-- Nothing but restarts has run at this time. -/
  | pre
  /-- The tick, or an object of this time, has run. -/
  | post
  deriving DecidableEq

/-- The phase at time `t'` of a node whose last event was at `t ≤ t'` in phase `ph`: `pre`
when the time advanced, `ph` otherwise. -/
def Phase.at (t t' : Time) (ph : Phase) : Phase := if t < t' then .pre else ph

/-- A configuration of a node: its state, its clock (the time of its last event) and its
phase at that time. -/
structure Config (A : NodeAC P) where
  /-- The node state. -/
  st : NodeState A
  /-- The clock: the time of the last event (`0` before any). -/
  time : Time
  /-- The phase at `time`. -/
  phase : Phase

/-- The initial configuration: the initial state at time `0`, before the tick of time `0`. -/
def Config.init (A : NodeAC P) : Config A := ⟨Node.init A, 0, .pre⟩

/-- When an event may run at time `t'`, found in phase `ph` at `t'`: a tick at a public time
in phase `pre`; a restart in phase `pre`; a delivery after the tick when `t'` is public (in
any phase otherwise). -/
def EventOK (t' : Time) (ph : Phase) : Event A → Prop
  | .tick _ => P.IsPublic t' ∧ ph = .pre
  | .restart => ph = .pre
  | _ => P.IsPublic t' → ph = .post

/-- The phase after an event: a restart keeps `pre`; everything else leaves `post`. -/
def Event.phaseAfter : Event A → Phase
  | .restart => .pre
  | _ => .post

/-- One event `e` at time `t'` from `cfg`, with the digest `dg` at validator `self`: the time
does not decrease; the event is allowed in the phase at `t'` and a delivery passes the wire
checks; the handler runs. -/
def Step (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n) (cfg : Config A)
    (e : Event A) (t' : Time) (cfg' : Config A) : Prop :=
  cfg.time ≤ t' ∧ EventOK t' (Phase.at cfg.time t' cfg.phase) e ∧ WireOK dg e ∧
    cfg'.st = (exec proposer dg self cfg.st t' e).1 ∧ cfg'.time = t' ∧ cfg'.phase = e.phaseAfter

/-- `cfg'` is reached from `cfg` by events. -/
def Reaches (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n) :
    Config A → Config A → Prop :=
  Relation.ReflTransGen (fun cfg cfg' => ∃ e t', Step proposer dg self cfg e t' cfg')

/-- A reachable configuration of validator `self`: reached from the initial one. -/
def Reachable (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n) (cfg : Config A) :
    Prop :=
  Reaches proposer dg self (Config.init A) cfg

/-- The law of one cut at validator `self` and time `t`, from `st` to `st'`: an AC cut
executes the AC on `𝒜` with the frame `fg_to_ac(Σ)` and changes only `𝒜`; an FG cut executes
the FG call and changes only `Σ` (`fg_on_block`, accepted, of a block not of a future slot;
`fg_on_attestation`), nothing (`fg_on_block` refused; `fg_attest` that signs nothing) or only
`Λ` (`fg_attest` that signs). -/
def CutStep (self : Fin P.n) (t : Time) (st : NodeState A) : Cut A → NodeState A → Prop
  | .ac ℓ, st' =>
      ℓ.frame = frame st ∧ A.step self st.ac ℓ.frame t ℓ.call = (st'.ac, ℓ.emits) ∧
        st'.fg = st.fg ∧ st'.record = st.record
  | .fg (.block B true), st' =>
      B.slot ≤ P.slotOf t ∧ st.fg.onBlock B = some st'.fg ∧ st'.ac = st.ac ∧
        st'.record = st.record
  | .fg (.block B false), st' => st.fg.onBlock B = none ∧ st' = st
  | .fg (.attestation a), st' =>
      st'.fg = st.fg.onAttestation a ∧ st'.ac = st.ac ∧ st'.record = st.record
  | .fg (.attest C none), st' => st.fg.attest st.record self C = none ∧ st' = st
  | .fg (.attest C (some a)), st' =>
      st.fg.attest st.record self C = some (a, st'.record) ∧ st'.fg = st.fg ∧ st'.ac = st.ac

/-- The cuts `cs` in order from `st` to `st'`, each by the cut law. -/
inductive CutChain (self : Fin P.n) (t : Time) : NodeState A → List (Cut A) → NodeState A → Prop
  /-- No cut: the state is unchanged. -/
  | nil (st : NodeState A) : CutChain self t st [] st
  /-- One cut, then the rest. -/
  | cons {st st₁ st' : NodeState A} {c : Cut A} {cs : List (Cut A)} :
      CutStep self t st c st₁ → CutChain self t st₁ cs st' → CutChain self t st (c :: cs) st'

end Consensus.Goldilocks.Node

end
