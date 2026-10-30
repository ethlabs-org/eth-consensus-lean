module
public import ConsensusLean.Spec.Shape.Shape

@[expose] public section

/-! # Progress fit and tolerance (L2, part of `Accepted`)

What `Accepted` asks of a contract's progress requirements besides the
claims: they fit the family's skeleton (`ProgressFits`) and every provided
output has indices that tolerate arbitrary numbers of validators not ready
and a bad (faulty or not ready) proposer slot in every window
(`ProgressTolerant`). Both feed the generic realizability theorem
(`regimes_realizable`), whose `badProposer` witness shows the second
tolerance semantically: a run with a faulty proposer in every window meets
the requirement and is live. -/

namespace Consensus.Shape

open Blocks

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

/-- A progress requirement fits a skeleton: a recurrence needs one proposer
chosen by the run at every slot (`.sized 1`, independent of the population:
with every key selected, a faulty validator is always among the proposers and
recurrence has no witness, `allProposers_no_witness`; a fixed schedule is not
admitted either: the generic bad-proposer witness needs a schedule-side
condition, since a round-robin schedule whose period is coprime to the window
puts every validator at the periodic bad slots, and a constant schedule has
no witness at all); a bound on the validators not ready fits every skeleton. -/
def ProgressReq.Fits {n : Nat} (sk : Skeleton n) : ProgressReq → Prop
  | .recur _ => ∀ s, sk.proposerSel s = .sized 1
  | .notReadyAtMost _ => True

/-- Every progress requirement of the contract fits the family's skeleton at
every public parameter. -/
def ProgressFits (K : Contract ProgressReq) (F : ShapeFamily O Info) : Prop :=
  ∀ cap i pub, ProgressReq.Fits (F pub).skel (K.progress cap i)

/-- A requirement tolerates `N` validators not ready and a bad proposer slot
in every window: a recurrence needs the slack `span + 2 ≤ gap` (its
proposers stay ready on the witnesses, so the number not ready does not
matter); a bound on the validators not ready must be at least `N`. For
`N ≥ n` the bound holds on every point, so it also holds when every
round-robin leader is faulty or asleep: such a requirement has no proposer
slots to tolerate. -/
def ProgressReq.Tolerates (N : Nat) : ProgressReq → Prop
  | .recur ρ => ρ.BadSlotSlack
  | .notReadyAtMost m => N ≤ m

/-- Every provided output has, for every requested number `N`, an index
tolerating `N` validators not ready and a bad proposer slot in every
window. -/
def ProgressTolerant (O : OutputSchema) (K : Contract ProgressReq) : Prop :=
  ∀ cap, (O.output cap).isSome → ∀ N : Nat, ∃ i, ProgressReq.Tolerates N (K.progress cap i)

end Consensus.Shape

end
