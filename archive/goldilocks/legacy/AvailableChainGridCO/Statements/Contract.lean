module
public import AvailableChainGridCO.Model.Protocol
public import AvailableChainStatements.Generic.Claims

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

section Shared
variable [LeasePolicy]

open AvailableChain.Generic
open AvailableChain.Statements.Generic

def gridInterface (p : Params) : Interface (gridCO p) where
  confirmed := confirmed
  stable := stable
  block := block
  opening := fun _ => True

/-- Largest fixed grid level no greater than the observed support. -/
def roundedLevel (p : Params) (h : Nat) : Nat :=
  gridLevel p.n p.grid h

/-- Paper constants, including K = the number of distinct grid levels. -/
def gridConstants (p : Params) (G : Time) : Constants where
  θ := p.θ_R
  θrec := 1 / 2
  recoveryFull := false
  η := p.η
  D_c := 6 * p.Δ
  D_s := 6 * p.Δ
  D_f := 6 * p.Δ
  armingLag := 4 * p.Δ
  fastArmingLag := 4 * p.Δ
  budget := min p.η (lifetime p)
  recoveryBound := (p.grid.card : Time) * (lifetime p + p.Δ) + G + 10 * p.Δ
  proposerGap := G

end Shared

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- The Draft 4.3 contract statement for this instance. -/
def GridContract {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (G : Time) (E : Env V) : Prop :=
  E.Δ = p.Δ ∧
    AvailableChain (gridCO p) E (gridInterface p) (gridConstants p G)

end AvailableChain.GridCO
end
