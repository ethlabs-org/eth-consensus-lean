module
public import AvailableChainSAPC.Model.Protocol
public import AvailableChainSA.Statements.Contract
public import AvailableChainStatements.Strong.Claims

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic

def sapcInterface (p : Params) : StrongInterface (sapc p) where
  confirmed := confirmed
  stable := stable
  block := block
  opening := fun _ => True
  strong := strong

/-- Only the two Recovery participation constants differ from SA. -/
def sapcConstants (p : Params) (G : Time) : Constants :=
  { SA.saConstants p G with θrec := 2 / 3, recoveryFull := true }

def sapcStrongConstants (p : Params) : StrongConstants where
  faultCap := pcFaultCap p
  strongDelay := 6 * p.Δ

/-- The complete Draft 4.3 bundle. No global cap premise. -/
def SAPCContract {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (G : Time) (E : Env V) : Prop :=
  E.Δ = p.Δ ∧ AvailableChain (sapc p) E (sapcInterface p).toInterface (sapcConstants p G)

def SAPCStrong {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (G : Time) (E : Env V) : Prop :=
  E.Δ = p.Δ ∧ StrongClaims (sapc p) E (sapcInterface p)
    (sapcConstants p G) (sapcStrongConstants p)

end AvailableChain.SAPC
end
