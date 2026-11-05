module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealedSafety
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NonfinalEndpoints
public import ConsensusLean.Instances.Goldilocks.AsChainShape
public import ConsensusLean.Spec.Shape.Obligations
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Recovery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.WindowAnchorRoute
public import Mathlib.Data.Fin.VecNotation

public section

/-! # Goldilocks Obligations: the final query and its window data

The `FinalQuery` and the `FinalWindowData` of the route-A final window, with the window
predicates `AnchorRun`, `AnchorSteps` and `CacheCoverage`. They are in this module, not in
Concrete.lean, so that the window assembly (FinalWindowAssembly.lean, CarrierProcessed.lean)
comes before Concrete.lean, and the leaf `final_window_extract` is proved from it. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- A single reader-conditional final query, with the original engine-scaled latency.
No supplier conclusion is a new premise of Healthy. -/
structure FinalQuery where
  run : (Sys (goldilocks S) V).Run
  hn : 1 ≤ Fintype.card V
  index : (K S A).Idx
  gst : Time
  query : Time
  valid : (Sys (goldilocks S) V).Valid run
  noCollision : ¬ run.2.HashCollision
  healthy : (Sys (goldilocks S) V).Healthy (K S A) gst run
  progress : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) .final index
    ((Sys (goldilocks S) V).ready (K S A) gst run) run.2.horizon run
  mature : (Sys (goldilocks S) V).heal (K S A) .final index gst run ≤ query
  bounded : query + ((K S A).params.latency .final index : Time) * run.1.ΔAC ≤ run.2.horizon
  reader : ∃ v, run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) run) v
    (query + ((K S A).params.latency .final index : Time) * run.1.ΔAC)

namespace FinalQuery

variable {S A V}

abbrev params (Q : FinalQuery S A V) := S.params (Model.pubOf Q.run.1) Q.hn
noncomputable abbrev trace (Q : FinalQuery S A V) := simTrace S Q.run.2 Q.hn
noncomputable abbrev deadline (Q : FinalQuery S A V) : Time :=
  Q.query + ((K S A).params.latency .final Q.index : Time) * Q.run.1.ΔAC

end FinalQuery

/-- Operational window witnesses only. The processing field is an OPEN endpoint-specific
transport budget, not acceptance or a freely chosen output delay. Route A (`docs/decisions.md`
§"Final liveness"): four honest anchors at the slots `start + [0, c, 2c, 3c]` for the anchor gap
`c = gap`, with `2 ≤ c` and the span `3c ≤ δt` (the gap
`c = 2` is the current instance). -/
structure FinalWindowData (Q : FinalQuery S A V) where
  start : Nat
  /-- The anchor gap `c`. -/
  gap : Nat
  gap_two : 2 ≤ gap
  /-- The window spans at most `δt` slots. -/
  gap_span : 3 * gap ≤ S.δt
  block : Fin 4 → SA.Blk Q.params.n (List (FG.Att Q.params.n))
  cut : Fin 4 → Nat
  slots : ∀ a, (block a).slot = start + (![0, gap, 2 * gap, 3 * gap] a)
  proposals : ∀ a, Q.trace.ProposesAt (block a).proposer (cut a) (block a)
  accepted : ∀ a, Q.trace.AcceptAt (block a).proposer (cut a) (block a)
  ready : ∀ a, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
    ((Sys (goldilocks S) V).cDur (K S A) Q.run) (block a).proposer (Q.trace.time (cut a))
  fresh : Q.query < Q.trace.time (cut 0)
  ordered : StrictMono cut
  bounded : ∀ a, Q.trace.time (cut a) ≤ Q.deadline
  chain : ∀ a b, a ≤ b → Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (block a) (block b)
  /-- Actual canonical processing before the exact query deadline; deriving sufficient slack
  from the jointly chosen contract_latency remains OPEN. No acceptance is assumed here. -/
  carrierProcessed : ∀ y, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
    ((Sys (goldilocks S) V).cDur (K S A) Q.run) y Q.deadline →
    ∃ j, Q.trace.BlockCallAt y j (block 3) ∧ Q.trace.time j ≤ Q.deadline

namespace FinalWindowData

variable {S A V} {Q : FinalQuery S A V} (W : FinalWindowData S A V Q)

/-- Use the actual last anchor's store, not an independently chosen chain-state map. -/
noncomputable abbrev store := (Q.trace.post (W.cut 3)).fg
noncomputable abbrev state (B : SA.Blk Q.params.n (List (FG.Att Q.params.n))) := W.store.σ B.root
abbrev Extends (_W : FinalWindowData S A V Q)
    (B C : SA.Blk Q.params.n (List (FG.Att Q.params.n))) : Prop :=
  Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) B C


/-- **Route-A run premises** for the window (`cacheCoverage_of_anchor_window_upTo`,
WindowAnchorRoute.lean): reset premises through a horizon `b`, catch-up `2Δ`, the four anchors
are honest proposals at the window slots `start + [0, c, 2c, 3c]` (`c = W.gap`), the drain time
is before the first anchor, and the last anchor is before `b`. -/
def AnchorRun : Prop :=
  ∃ (proposer : Nat → Fin Q.params.n)
    (dg : Digest (List (FG.Att Q.params.n)) (SA.Payload Q.params.n)) (g ΔF a b : Time),
    Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2) proposer dg g ΔF a b ∧
    Healing.CatchRun Q.trace (honestKeys S Q.run.2) g (2 * Q.params.Δ) ∧
    (∀ i, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2) proposer
      (W.start + ![0, W.gap, 2 * W.gap, 3 * W.gap] i) (W.block i)) ∧
    Healing.drainTime Q.params a ≤ Q.params.ts W.start ∧
    Q.params.ts (W.start + 3 * W.gap) ≤ b

/-- **Route-A anchor steps**: `σ[P_i].h + 1 ≤ σ[P_{i+1}].h` for the three gap-`c` steps, read at
honest stores (`AnchorStep`): attestations by `row_of_report`,
or a crossing above the previous anchor; step 0 from the seed `h₀ ≥ HZ+2`. -/
def AnchorSteps : Prop :=
  ∀ i : Fin 3, AnchorStep Q.trace (honestKeys S Q.run.2) (W.block i.castSucc) (W.block i.succ)

/-- Actual cache acceptance and persistence at the original endpoint, not mere delivery. -/
def CacheCoverage : Prop :=
  ∀ y t j, Q.deadline ≤ t → t ≤ Q.run.2.horizon →
    Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
      ((Sys (goldilocks S) V).cDur (K S A) Q.run) y t → Regimes.CutAfter Q.trace j t →
    W.Extends (W.block 0) (Q.trace.state y j).fg.F

/-- `AnchorRun` unfolded (the definition is not exposed outside this module). -/
theorem anchorRun_iff : W.AnchorRun ↔
    ∃ (proposer : Nat → Fin Q.params.n)
      (dg : Digest (List (FG.Att Q.params.n)) (SA.Payload Q.params.n)) (g ΔF a b : Time),
      Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2) proposer dg g ΔF a b ∧
      Healing.CatchRun Q.trace (honestKeys S Q.run.2) g (2 * Q.params.Δ) ∧
      (∀ i, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2) proposer
        (W.start + ![0, W.gap, 2 * W.gap, 3 * W.gap] i) (W.block i)) ∧
      Healing.drainTime Q.params a ≤ Q.params.ts W.start ∧
      Q.params.ts (W.start + 3 * W.gap) ≤ b :=
  Iff.rfl

/-- `AnchorSteps` unfolded (the definition is not exposed outside this module). -/
theorem anchorSteps_iff : W.AnchorSteps ↔
    ∀ i : Fin 3, AnchorStep Q.trace (honestKeys S Q.run.2) (W.block i.castSucc) (W.block i.succ) :=
  Iff.rfl

/-- `CacheCoverage` unfolded (the definition is not exposed outside this module). -/
theorem cacheCoverage_iff : W.CacheCoverage ↔
    ∀ y t j, Q.deadline ≤ t → t ≤ Q.run.2.horizon →
      Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
        ((Sys (goldilocks S) V).cDur (K S A) Q.run) y t → Regimes.CutAfter Q.trace j t →
      W.Extends (W.block 0) (Q.trace.state y j).fg.F :=
  Iff.rfl

end FinalWindowData

end Consensus.Goldilocks.Obligations

end
