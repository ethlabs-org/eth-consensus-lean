module
public import AvailableChainFGCompose.Statements.Observations
public import AvailableChainFGCompose.Statements.SafetyReads

@[expose] public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In}
variable [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)
variable (S : FGSafetyReads P n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P)

structure FGSelectionReads (P : V2.ProtocolSpecD In) (n : Nat) where
  select : P.State → Option (FGBlock (Fin n)) × Option (FGBlock (Fin n))
  clientInputs : P.State → Option (FGBlock (Fin n)) × HeadFields

structure FGSelectionLaws (O : FGObservationReads R)
    (Q : FGSelectionReads P n) (Good : P.State → Prop)
    (headFields : (FGBlock (Fin n)) → HeadFields) : Prop where
  source_eq : ∀ nd, Good nd → (Q.select nd).1 = R.source nd
  head_eq : ∀ nd, Good nd → (Q.select nd).2 = R.finalityHead nd
  head_held : ∀ nd, Good nd →
    ∃ H, (Q.select nd).2 = some H ∧ H ∈ (R.core nd).fg.TF
  source_viable : ∀ nd C, Good nd → (Q.select nd).1 = some C →
    C ∈ O.viable nd (R.core nd).fg.TF
  source_head : ∀ nd C H, Good nd →
    Q.select nd = (some C, some H) → FGBlock.Preceq C H
  client_eq : ∀ nd H, Good nd → (Q.select nd).2 = some H →
    Q.clientInputs nd = ((Q.select nd).1, headFields H)

structure FGSelectionClientLaws (Q : FGSelectionReads P n)
    (S : FGSafetyReads P n Wire) : Prop where
  inputs_eq : ∀ nd, Q.clientInputs nd = S.inputs nd

structure FGActionSelectionLaws (E : Generic.Env V) (rho : V2.D.Run V P)
    (Q : FGSelectionReads P n) (action : Nat → Time)
    (ActionScope Joined : V → Nat → P.State → Prop) : Prop where
  nonempty_joined : ∀ x r nd C,
    postClock E rho x (action r) = some nd →
    ActionScope x r nd → (Q.select nd).1 = some C → Joined x r nd

end AvailableChain.FGCompose
end
