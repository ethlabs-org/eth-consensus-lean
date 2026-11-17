module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.EngineTransport

@[expose] public section

/-! # Progress budgets and actual final-production interfaces

These are open supplier contracts, not proofs. Every advertised progress form is retained.
The narrow single-pattern healing transport is unchanged. No constant FrameWindow is produced:
the concrete final-window source instead uses reset and shared healing premises.
-/

set_option autoImplicit false

namespace Consensus.Goldilocks.Generic

open Shape Blocks
open SA (gbar)
open Healing (cutZ)

variable {P : Params} {A : NodeAC P} {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V} {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}

/-- The population FG needs a fault fraction at most a third; committee counts
use the separate contract fraction `βK`. -/
def HealthyBetaFit (K : Contract ProgressReq) : Prop := K.params.β ≤ 1 / 3

/-- The committee reduction uses a fault fraction at most a half. This is an
instance fit, not a restriction on admissible correctness contracts. -/
def CommitteeHalfFit (K : Contract ProgressReq) : Prop := K.params.βK ≤ 1 / 2

/-- Four actual anchors with exact spacing and final publication slack. No constant-frame
premise is hidden in this data. Acceptance/height/processing are separate open suppliers. -/
structure FinalProductionWindow (M : RunMap rho payload) (catchUp hold : Time)
    (query deadline : Time) where
  start : Nat
  gap : Nat
  gap_two : 2 ≤ gap
  gap_span : 3 * gap ≤ P.δt
  block : Fin 4 → A.Blk
  cut : Fin 4 → Nat
  slots : ∀ a, (block a).slot = start + a.val * gap
  proposals : ∀ a, M.trace.ProposesAt (block a).proposer (cut a) (block a)
  ready : ∀ a, ReadyCut M.trace M.honest catchUp (block a).proposer (cut a)
  honest_hold : ∀ a, (block a).proposer ∈ M.honest (M.trace.time (cut a) + hold)
  fresh : query < M.trace.time (cut 0)
  ordered : StrictMono cut
  bounded : ∀ a, M.trace.time (cut a) ≤ deadline
  publication : M.trace.time (cut 3) + P.Δ ≤ deadline

/-- Actual acceptance, chaining and three own-reader height increases of one selected
window. This predicate is evidence to be supplied jointly with that window, not a law for
arbitrary windows. FrameWindow is not manufactured. -/
def FinalHeightSupply (M : RunMap rho payload) (catchUp hold query deadline : Time)
    (W : FinalProductionWindow M catchUp hold query deadline) : Prop :=
  (∀ a, M.trace.AcceptAt (W.block a).proposer (W.cut a) (W.block a)) ∧
  (∀ a b, a ≤ b → Anc (M.trace.HonestBlocksAt M.honest) (W.block a) (W.block b)) ∧
  ∀ a : Fin 3, ∃ z i j, z ∈ M.honest (M.trace.time i) ∧ z ∈ M.honest (M.trace.time j) ∧
    W.block a.castSucc ∈ (M.trace.state z i).fg.tree ∧
    W.block a.succ ∈ (M.trace.state z j).fg.tree ∧
    ((M.trace.state z i).fg.σ (W.block a.castSucc).root).h + 1 ≤
      ((M.trace.state z j).fg.σ (W.block a.succ).root).h

/-- All-form joint final production at the advertised query/deadline and actual FG delay.
The same selected window has a non-genesis first anchor whose proposer is ready at its cut, and
actual acceptance, chaining and height evidence. No gap or latency is enlarged here. -/
def FinalWindowSupply (M : RunMap rho payload) (K : Contract ProgressReq)
    (catchUp hold : Time) : Prop :=
  rho.ExecutionValid → ¬ rho.HashCollision → ∀ idx g t,
    (Sys F V).Healthy (shapeProgress F V).toExternal K g ⟨E, rho⟩ →
    (Sys F V).prog (shapeProgress F V) K .final idx ((Sys F V).ready K g ⟨E, rho⟩)
      rho.horizon ⟨E, rho⟩ →
    (Sys F V).heal K .final idx g ⟨E, rho⟩ ≤ t →
    t + (K.params.latency .final idx : Time) * E.ΔAC ≤ rho.horizon →
    (∃ v, rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) v
      (t + (K.params.latency .final idx : Time) * E.ΔAC)) →
    ∃ W : FinalProductionWindow M catchUp hold t
        (t + (K.params.latency .final idx : Time) * E.ΔAC),
      (W.block 0).root ≠ P.genesisRoot ∧
      rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩)
        (M.validator (W.block 0).proposer) (M.trace.time (W.cut 0)) ∧
      FinalHeightSupply M catchUp hold t
        (t + (K.params.latency .final idx : Time) * E.ΔAC) W

end Consensus.Goldilocks.Generic

end
