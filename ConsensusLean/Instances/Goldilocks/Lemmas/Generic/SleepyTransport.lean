module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.SleepyLayer1
import ConsensusLean.Lemmas.Problem.Facts.Regimes

public section

/-! # Independent retention-window transports

Earlier retention charges keep more ready validators and fewer faulty validators.
Population and committee windows are transported separately.
-/

namespace Consensus.Goldilocks.Generic.SleepyLayer1

open Shape Blocks

variable {P : Params} {A : NodeAC P}
  {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V} {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}

theorem committee_transport (M : RunMap rho payload)
    (C : ACCorrectLocal A M.signer) : CommitteeTransport M C := by
  intro p b c W _ hc hW h0 h1 h t d ht htd hdb hne
  have hcount := h t ht (htd.trans (hdb.trans (min_le_left _ _))) hne
  simp only [le_refl, ↓reduceIte] at hcount
  exact p.ready_inter_lt_of_retain _ (by rw [← hW]; exact hdb.trans (min_le_right _ _)) hc h1 h0
    hcount

theorem population_transport (M : RunMap rho payload)
    (C : ACCorrectLocal A M.signer) : PopulationTransport M C := by
  intro p b c W _ hc hW h0 h1 h t d ht htd hdb
  have hcount := h t ht (htd.trans (hdb.trans (min_le_left _ _)))
  have he : d ≤ p.lookAhead W t := by rw [← hW]; exact hdb.trans (min_le_right _ _)
  change C.θ * (((p.retain (p.lookAhead W t)).readyAt c t).card +
    ((p.retain (p.lookAhead W t)).faultyAt t).card : ℚ) < _ at hcount
  change C.θ * (((p.retain d).readyAt C.catchUp t).card + (p.faultyAt d).card : ℚ) < _
  simpa only [Finset.inter_univ, Nat.cast_add] using p.ready_inter_lt_of_retain Finset.univ he hc
    h1 h0 (by simpa only [Finset.inter_univ, Nat.cast_add] using hcount)

end Consensus.Goldilocks.Generic.SleepyLayer1

end
