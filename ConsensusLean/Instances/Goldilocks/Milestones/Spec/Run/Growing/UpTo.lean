module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Trace

@[expose] public section

/-! # The prefix of a trace through a time

`Trace.upTo tr d` keeps the calls of the cuts at times `≤ d` and makes the later cuts stutter;
nobody is awake after `d`, and the observation horizon is `d`. A node honest at `d` was honest at
every earlier time, so on the prefix through `d` it follows every law of a run with the constant
honest set `H d`: the **retention** of a growing-fault run (`Growing.GoldilocksRun.upTo`,
`Lemmas/Growing/Run/UpTo`). It lets a static statement whose conclusion is about nodes honest at
one time `d`, read at cuts up to `d`, serve under growing faults unchanged. -/

namespace Consensus.Goldilocks.Trace

variable {N S L : Type}

/-- The prefix of `tr` through `d`: the cuts after `d` stutter, nobody is awake after `d`, and the
observation horizon is `d`. -/
def upTo (tr : Trace N S L) (d : Time) : Trace N S L :=
  { tr with
    label := fun i => if tr.time i ≤ d then tr.label i else none
    awake := fun y t => tr.awake y t ∧ t ≤ d
    observationHorizon := some d }

end Consensus.Goldilocks.Trace

end
