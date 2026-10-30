module
public import ConsensusLean.Instances.Goldilocks.Statements.Refinement
@[expose] public section

/-! # Witnesses for the Goldilocks refinement statements

Labelled by kind (CONTRIBUTING "Statements"):

* (a) `selIs_selValid`: a run's selection that realizes the setup's schedule (`SelIs`) and takes
  everyone in the poll role is admitted by the engine (`SelValid`), so the simulation hypothesis
  `SelIs` of `EngineSimulatesNode` and `FinalizedAccountable` is satisfiable together with
  `ExecutionValid.selValid`: the skeleton's `proposerSel := .sized 1` admits the singleton
  `{proposer s}` (`card = min 1 n` for `n ≥ 1`), `pollSel := .fixed univ` admits `univ`, and
  there are no committee kinds. -/

namespace Consensus.Goldilocks.Refinement.Test

open Shape
open Consensus.Model (pubOf SelSpec)

variable {V : Type} [Fintype V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- A selection realizing the setup's schedule with everyone polling is admissible. -/
theorem selIs_selValid (hsel : SelIs S rho hn) (hpoll : rho.sel .poll = Finset.univ) :
    rho.SelValid := by
  intro r
  cases r with
  | proposer s =>
    change (SelSpec.sized 1).Admits _
    rw [SelSpec.Admits, hsel s, Nat.min_eq_left hn]
    exact Finset.card_singleton _
  | duty _ k => exact k.elim
  | poll =>
    change (SelSpec.fixed Finset.univ).Admits _
    rw [SelSpec.Admits, hpoll]

end Consensus.Goldilocks.Refinement.Test
