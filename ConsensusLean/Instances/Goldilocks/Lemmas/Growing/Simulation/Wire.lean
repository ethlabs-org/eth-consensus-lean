module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Groups
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.WireGroup

public section

/-! # Wire checks for the growing canonical trace

Wire decoding is independent of signer honesty; the latter is needed separately for
unforgeability. We recover the canonical event at each group and preserve that separation.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

private theorem group_of_cut (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} {k : Nat} (hnode : (simTrace S rho hn).node k = y)
    (hl : (simTrace S rho hn).label k ≠ none) :
    ∃ j0 t e,
      (simTrace S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho) y j0 t e ∧ j0 ≤ k ∧
      k < j0 + (Node.exec (runProposer S rho hn) (digestOf S rho)
        y ((simTrace S rho hn).state y j0) t e).2.length ∧ WireOK (digestOf S rho) e := by
  obtain ⟨r, i, ev, -, he, h1, h2, -, hn', -, -, -⟩ := simTrace_cut S rho hn hl
  have hy' := hn'.symm.trans hnode
  cases ev with
  | tick v t =>
    change rho.ownKey v = y at hy'
    subst hy'
    by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
    · obtain ⟨hg, hlen⟩ := simTraceAt_tick_public_group S rho hn hv he hp
      rw [simTraceAt_eq] at hg hlen
      exact ⟨_, t, _, hg, h1, by omega, trivial⟩
    · have hlen := cutMap_succ S rho hn i
      rw [eventCuts_tick_other S rho hn i v t he hp, List.length_nil] at hlen
      omega
  | deliver v o t =>
    change rho.ownKey v = y at hy'
    subst hy'
    have hseq := simTraceAt_deliver S rho hn hv he
    rw [simTraceAt_eq] at hseq
    obtain ⟨-, hcov⟩ := deliverSeq_cover hseq
    obtain ⟨j0, e, o', ho, hce, hg, h3, h4⟩ := hcov k h1 h2
    exact ⟨j0, t, e, hg, h3, h4, wireOK_of_delivered S rho hn o ho hce⟩
  | restart v t =>
    change rho.ownKey v = y at hy'
    subst hy'
    obtain ⟨hg, hlen⟩ := simTraceAt_restart S rho hn hv he
    rw [simTraceAt_eq] at hg hlen
    exact ⟨_, t, _, hg, h1, by omega, trivial⟩

/-- Every canonical handler group passes wire checks, independently of later compromise. -/
theorem simTraceAt_wire (hv : rho.ExecutionValid) :
    ∀ y j t e,
      (simTraceAt S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho) y j t e →
      WireOK (digestOf S rho) e := by
  rw [simTraceAt_eq]
  intro y j t e hg
  exact wireOK_of_group_cut hg (group_of_cut S rho hn hv)

end Consensus.Goldilocks.Simulation
