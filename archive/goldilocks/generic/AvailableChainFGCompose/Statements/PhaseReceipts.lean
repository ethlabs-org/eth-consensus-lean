module
public import AvailableChainFGCompose.Statements.Phase
public import AvailableChainFGCompose.Statements.FinalityReceipts -- shake: keep (receipt API)

@[expose] public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P)
variable (O : FGObservationReads R)
variable (joined : P.State → Bool) (receipt : Block → Time → V → Prop)

/-- DC: INTENTIONAL. One selected witness, strict deadline, and actual joined read.
`receipt` is the target service of the protocol. The generic c2 instance is
`TargetReceiptService`; a frozen protocol can keep its opaque service predicate.
The consumer requires its proved receipt-to-held consequence at the same deadline. -/
structure WitnessReceiptScope (W : FGBlock (Fin n)) (deadline : Time) : Prop where
  atRead : ∀ iy y t, y ∈ rho.honest → rho.events[iy]? = some (.tick y t) →
    joined (P.clock (V2.D.Run.stateBefore E rho iy y) t) = true → deadline ≤ t →
    Block.Preceq (R.erase (R.core (rho.stateBeforeTime E deadline y)).fg.F)
      (R.erase W) → receipt (R.erase W) deadline y

/-- DC: INTENTIONAL. Select only the frontier, top, and contest carriers at this cut. -/
structure PhaseWitnessReceiptScope (i m : Nat) (deadline : Time) : Prop where
  frontier : ∃ x W, HeldAt R E rho i x W ∧ (O.height W).h = m ∧
    WitnessReceiptScope R E rho joined receipt W deadline
  top : TopEvidence R E rho i m →
    ∃ x C, HeldAt R E rho i x C ∧ (O.height C).h = m ∧
      (O.height C).h_j + 1 = m ∧
      (O.height C).J = (R.core (V2.D.Run.stateBefore E rho i x)).fg.J ∧
      WitnessReceiptScope R E rho joined receipt C deadline
  contest : ContestEvidence R E rho O i m →
    ∃ x C W, HeldAt R E rho i x C ∧ HeldAt R E rho i x W ∧
      (O.height C).h = m ∧ (O.height W).h = m ∧
      (O.height C).h_j + 1 = m ∧ ¬ FGBlock.Preceq (O.height C).J W ∧
      WitnessReceiptScope R E rho joined receipt C deadline ∧
      WitnessReceiptScope R E rho joined receipt W deadline

end AvailableChain.FGCompose
end
