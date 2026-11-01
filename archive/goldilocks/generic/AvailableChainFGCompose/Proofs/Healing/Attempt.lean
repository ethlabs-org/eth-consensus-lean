module
public import AvailableChainFGCompose.Statements.Attempt

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot)
variable (O : FGObservationReads R) (T : FGTiming) (I : V2.D.Interface Prot)
variable (A : FGAttemptGateReads Prot) (pair : Wire → NamedHeightPair) (Jst : Time)

/-- Four proved branch functions supply the complete stopped-attempt dispatcher. -/
theorem progressAttempt_of (G repairAllowance : Time)
    (raise_contest : ∀ k ev, AttemptValid R S E rho O T I A pair Jst k →
      rho.events[k.start]? = some ev →
      ev.time + attemptBudget T G repairAllowance k ≤ rho.horizon →
      k.task = .raise → k.phase = .contest →
      AttemptEndsBy R S E rho O T pair k (attemptBudget T G repairAllowance k))
    (raise_other : ∀ k ev, AttemptValid R S E rho O T I A pair Jst k →
      rho.events[k.start]? = some ev →
      ev.time + attemptBudget T G repairAllowance k ≤ rho.horizon →
      k.task = .raise → k.phase ≠ .contest →
      AttemptEndsBy R S E rho O T pair k (attemptBudget T G repairAllowance k))
    (firstRow_contest : ∀ k ev, AttemptValid R S E rho O T I A pair Jst k →
      rho.events[k.start]? = some ev →
      ev.time + attemptBudget T G repairAllowance k ≤ rho.horizon →
      k.task = .firstRow → k.phase = .contest →
      AttemptEndsBy R S E rho O T pair k (attemptBudget T G repairAllowance k))
    (firstRow_other : ∀ k ev, AttemptValid R S E rho O T I A pair Jst k →
      rho.events[k.start]? = some ev →
      ev.time + attemptBudget T G repairAllowance k ≤ rho.horizon →
      k.task = .firstRow → k.phase ≠ .contest →
      AttemptEndsBy R S E rho O T pair k (attemptBudget T G repairAllowance k))
    : ∀ k ev, AttemptValid R S E rho O T I A pair Jst k →
      rho.events[k.start]? = some ev →
      ev.time + attemptBudget T G repairAllowance k ≤ rho.horizon →
      AttemptEndsBy R S E rho O T pair k (attemptBudget T G repairAllowance k) := by
  intro k ev hvalid hstart hhor
  cases ht : k.task with
  | raise =>
    by_cases hp : k.phase = .contest
    · exact raise_contest k ev hvalid hstart hhor ht hp
    · exact raise_other k ev hvalid hstart hhor ht hp
  | firstRow =>
    by_cases hp : k.phase = .contest
    · exact firstRow_contest k ev hvalid hstart hhor ht hp
    · exact firstRow_other k ev hvalid hstart hhor ht hp

end AvailableChain.FGCompose
end
