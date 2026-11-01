module
public import AvailableChainStatements.Generic.Conditions

@[expose] public section

namespace AvailableChain.Framework

open AvailableChain.Generic AvailableChain.Statements.Generic

variable {n : Nat}

/-- The effect of one handler call on one handled object (design E4). -/
inductive Outcome where
  /-- `processed` changes from false to true. -/
  | accepted
  /-- `excludes` holds after the call; it holds for the rest of the epoch. -/
  | rejected
  /-- No change for the object, and it is not excluded. -/
  | refused
  deriving DecidableEq, Repr

/-- The effect of the call `process st o` on the handled object `o'`. -/
def classify (P : ProtocolSpec n) (st : P.State) (o o' : P.Object) : Outcome :=
  if P.processed st o' = false ∧ P.processed (P.process st o) o' = true then .accepted
  else if P.excludes (P.process st o) o' = true then .rejected
  else .refused

/-- E4 obligations on the v1 engine. The v1 engine has no restart, so a run
is one epoch. Stability is stated along runs, because `clock` can move back
in time on states that no run reaches. -/
structure HooksSound (P : ProtocolSpec n) : Prop where
  /-- An excluded object does not change the state. -/
  excludes_inert : ∀ st o, P.excludes st o = true → P.process st o = st
  /-- Exclusion is stable along a run. -/
  excludes_stable : ∀ {V : Type} [DecidableEq V] [Fintype V] (E : Env V)
    (rho : Run V P), ScheduleWellFormed E rho → ∀ v o i j, i ≤ j →
      P.excludes (Run.stateBefore P rho i v) o = true →
      P.excludes (Run.stateBefore P rho j v) o = true
  /-- `processed` is monotone along a run. -/
  processed_stable : ∀ {V : Type} [DecidableEq V] [Fintype V] (E : Env V)
    (rho : Run V P), ScheduleWellFormed E rho → ∀ v o i j, i ≤ j →
      P.processed (Run.stateBefore P rho i v) o = true →
      P.processed (Run.stateBefore P rho j v) o = true
  /-- `depsPresent` is monotone along a run (design E4). -/
  deps_stable : ∀ {V : Type} [DecidableEq V] [Fintype V] (E : Env V)
    (rho : Run V P), ScheduleWellFormed E rho → ∀ v o i j, i ≤ j →
      P.depsPresent (Run.stateBefore P rho i v) o = true →
      P.depsPresent (Run.stateBefore P rho j v) o = true
  /-- A handled object is the delivered object or one that it carries. -/
  handles_carries : ∀ st o o', P.handles st o o' → o = o' ∨ P.carries o o'

end AvailableChain.Framework

end
