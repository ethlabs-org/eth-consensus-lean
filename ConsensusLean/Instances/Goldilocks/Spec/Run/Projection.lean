module
public import ConsensusLean.Instances.Goldilocks.Spec.Run.Model
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.Trace

@[expose] public section

/-! # Goldilocks runs: projections onto the component traces

A run (`RunTrace`) projects onto the AC trace and the FG trace that the component statements
read (decomposition §2 D, "the node run projects onto the component traces"; claims C0.5):

* `projAC tr`: the same cuts, nodes, times, events, positions and awake function; the labelled
  cuts are the AC cuts of the run, with their `ACLabel` (the call, the frame it was given and
  its emissions); every FG cut stutters (`none`); the states are the `𝒜` parts. So an FG cut
  of `y` leaves `y`'s AC state unchanged (`Node.CutStep`), as a stutter should.
* `projFG tr`: the same, with the FG cuts as labelled cuts (`FGLabel`) and the states the pair
  `(Σ, Λ)` (`FGState`); every AC cut stutters.

A projection keeps the indices, so a statement over the component trace about cut `i` is a
statement about cut `i` of the run; `Trace.state` commutes with the projections (a lemma of
`Lemmas/Compose`, not stated here). That the projection of a `Node.LocalRun` is an
`ACLocalRun` and an `FGLocalRun` (with `U` the honest blocks of the run) is claims C0.5
(`Statements/Compose/Run`). -/

namespace Consensus.Goldilocks.RunTrace

variable {P : Params} {A : NodeAC P} (tr : RunTrace A)

/-- The AC label of a cut, if it is an AC cut. -/
def acLabel : Cut A → Option (ACLabel A)
  | .ac ℓ => some ℓ
  | .fg _ => none

/-- The FG label of a cut, if it is an FG cut. -/
def fgLabel : Cut A → Option (FGLabel P A.Payload)
  | .fg ℓ => some ℓ
  | .ac _ => none

/-- The AC trace of a run: the AC cuts, over the `𝒜` parts of the node states. -/
def projAC : ACTrace A where
  init y := (tr.init y).ac
  node := tr.node
  time := tr.time
  event := tr.event
  pos := tr.pos
  label i := (tr.label i).bind acLabel
  post i := (tr.post i).ac
  awake := tr.awake
  observationHorizon := tr.observationHorizon

/-- The FG trace of a run: the FG cuts, over the `(Σ, Λ)` parts of the node states. -/
def projFG : FGTrace P A.Payload where
  init y := ((tr.init y).fg, (tr.init y).record)
  node := tr.node
  time := tr.time
  event := tr.event
  pos := tr.pos
  label i := (tr.label i).bind fgLabel
  post i := ((tr.post i).fg, (tr.post i).record)
  awake := tr.awake
  observationHorizon := tr.observationHorizon

end Consensus.Goldilocks.RunTrace

end
