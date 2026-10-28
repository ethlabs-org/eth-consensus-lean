module
public import ConsensusShape.Shape

@[expose] public section

/-! # Progress fit and tolerance (L2, part of `Accepted`)

What `Accepted` asks of a contract's progress requirements besides the
claims: they fit the family's skeleton (`ProgressFits`) and every provided
output tolerates arbitrary numbers of validators not ready
(`ProgressTolerant`). Both feed the generic realizability theorem
(`regimes_realizable`). -/

namespace Consensus.Shape

open Blocks

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

/-- A progress requirement fits a skeleton: a recurrence needs one proposer
per slot (`.sized 1`, independent of the population: with every key selected,
a faulty validator is always among the proposers and recurrence has no witness,
`allProposers_no_witness`); a bound on the validators not ready fits every
skeleton. -/
def ProgressReq.Fits {n : Nat} (sk : Skeleton n) : ProgressReq → Prop
  | .recur _ => sk.proposerSel = .sized 1
  | .notReadyAtMost _ => True

/-- Every progress requirement of the contract fits the family's skeleton at
every public parameter. -/
def ProgressFits (K : Contract ProgressReq) (F : ShapeFamily O Info) : Prop :=
  ∀ cap i pub, ProgressReq.Fits (F pub).skel (K.progress cap i)

/-- A requirement tolerates `N` validators not ready: recurrence always,
while a bound must be at least `N`. -/
def ProgressReq.Tolerates (N : Nat) : ProgressReq → Prop
  | .recur _ => True
  | .notReadyAtMost m => N ≤ m

/-- Every provided output has an index tolerating any requested number of
validators not ready. -/
def ProgressTolerant (O : OutputSchema) (K : Contract ProgressReq) : Prop :=
  ∀ cap, (O.output cap).isSome → ∀ N : Nat, ∃ i, ProgressReq.Tolerates N (K.progress cap i)

end Consensus.Shape

end
