module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Chains
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Structural transport of node outputs to engine chains -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} {S : Setup}
  {rho : Model.Run (compiled (goldilocks S)) E} {hn : 1 ≤ Fintype.card V}
  {tr : GoldilocksTrace (S.params (pubOf E) hn) (S.ro _)} {ι : Nat → Nat}

omit [DecidableEq V] in
/-- The honest engine reader's key is honest in its simulating run. -/
theorem honest_ownKey {v : V} (hv : v ∉ rho.faultyAt 0) :
    rho.ownKey v ∈ honestKeys S rho := by
  simpa only [mem_honestKeys_iff, Model.Run.ownKey, Equiv.apply_symm_apply] using hv

end Consensus.Goldilocks.Simulation

end
