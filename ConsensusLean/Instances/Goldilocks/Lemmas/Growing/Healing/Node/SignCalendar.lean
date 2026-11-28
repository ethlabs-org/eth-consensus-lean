module
public import ConsensusLean.Instances.Goldilocks.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Handlers
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Handlers
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Model
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.Handlers
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.View
public import ConsensusLean.Instances.Goldilocks.Spec.Node.Handlers
public import ConsensusLean.Instances.Goldilocks.Spec.Node.State
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Node.Node

public section

/-! # The signing calendar of a shadow run

The signing calendar of a shadow run is read through the shadow tick groups
(`RunTrace.GroupAt'`), not the stock ones: `SignCalendarAt'` is the stock `SignCalendarAt` with
`GroupAt'`. The signing gap `SignGapAt` reads only the calendar and is reused. Kept upstream of
the report and fresh-update suppliers that take a calendar. -/

namespace Consensus.Goldilocks.RunTrace

variable {P : Params} {A : NodeAC P} (tr : RunTrace A)

/-- **The signing calendar of a shadow run** (`SignCalendarAt` over the shadow groups): each tick
of a node honest at its time runs the FG update exactly when the calendar allows it then. -/
theorem signCalendarAt_iff {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
    {sign : Fin P.n → Time → Bool} :
    tr.SignCalendarAt proposer dg H sign ↔
      ∀ y j t x fgDue, y ∈ H t → tr.GroupAt proposer dg y j t (.tick x fgDue) →
        fgDue = sign y t :=
  Iff.rfl

end Consensus.Goldilocks.RunTrace

end
