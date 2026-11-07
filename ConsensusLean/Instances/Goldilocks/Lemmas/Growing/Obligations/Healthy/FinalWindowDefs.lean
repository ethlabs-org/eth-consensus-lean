module
public import Mathlib.Data.Fin.VecNotation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation

public section

/-! # Final window witnesses under growing faults

The witnesses retain the actual proposal and observation cuts. Honesty is checked independently
at each observation, rather than requiring an origin to remain honest at the window endpoint.
-/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}

/-- One height step, observed at two cuts of a node honest at each observation. -/
def AnchorStepAt (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (A X : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∃ z j j', z ∈ H (tr.time j) ∧ z ∈ H (tr.time j') ∧
    A ∈ (tr.state z j).fg.tree ∧ X ∈ (tr.state z j').fg.tree ∧
    ((tr.state z j).fg.σ A.root).h + 1 ≤ ((tr.state z j').fg.σ X.root).h

/-- The observations witnessing an anchor step, without exposing the definition's body. -/
theorem anchorStepAt_iff {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}
    {A X : SA.Blk sp.n (List (FG.Att sp.n))} :
    AnchorStepAt tr H A X ↔
      ∃ z j j', z ∈ H (tr.time j) ∧ z ∈ H (tr.time j') ∧
        A ∈ (tr.state z j).fg.tree ∧ X ∈ (tr.state z j').fg.tree ∧
        ((tr.state z j).fg.σ A.root).h + 1 ≤ ((tr.state z j').fg.σ X.root).h := Iff.rfl

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The first seed slot after the reset's drain. -/
noncomputable abbrev finalSeedMinAt (Q : FinalQueryAt S A V) (a : Time) : Nat :=
  Q.params.slot a + 2 * Q.params.k + 5

/-- The slot grid of the query's protocol instance. -/
noncomputable abbrev finalGridAt (Q : FinalQueryAt S A V) : TimeGrid :=
  (goldilocks S (Model.pubOf Q.run.1)).skel.grid

/-- Four actual honest anchors and processing of the last one by the original deadline. -/
structure FinalWindowDataAt (Q : FinalQueryAt S A V) where
  start : Nat
  gap : Nat
  gap_two : 2 ≤ gap
  gap_span : 3 * gap ≤ S.δt
  block : Fin 4 → SA.Blk Q.params.n (List (FG.Att Q.params.n))
  cut : Fin 4 → Nat
  slots : ∀ a, (block a).slot = start + (![0, gap, 2 * gap, 3 * gap] a)
  proposals : ∀ a, Q.trace.ProposesAt (block a).proposer (cut a) (block a)
  accepted : ∀ a, Q.trace.AcceptAt (block a).proposer (cut a) (block a)
  ready : ∀ a, Regimes.Growing.ReadyAt Q.trace Q.keys
    ((Sys (goldilocks S) V).cDur (K S A) Q.run) (block a).proposer (Q.trace.time (cut a))
  fresh : Q.query < Q.trace.time (cut 0)
  ordered : StrictMono cut
  bounded : ∀ a, Q.trace.time (cut a) ≤ Q.deadline
  chain : ∀ a b, a ≤ b → Anc (Q.trace.HonestBlocksAt Q.keys) (block a) (block b)
  carrierProcessed : ∀ y, Regimes.Growing.ReadyAt Q.trace Q.keys
    ((Sys (goldilocks S) V).cDur (K S A) Q.run) y Q.deadline →
    ∃ j, Q.trace.BlockCallAt y j (block 3) ∧ Q.trace.time j ≤ Q.deadline

namespace FinalWindowDataAt

variable {S A V} {Q : FinalQueryAt S A V} (W : FinalWindowDataAt S A V Q)

noncomputable abbrev store := (Q.trace.post (W.cut 3)).fg
noncomputable abbrev state (B : SA.Blk Q.params.n (List (FG.Att Q.params.n))) := W.store.σ B.root
abbrev Extends (_W : FinalWindowDataAt S A V Q)
    (B C : SA.Blk Q.params.n (List (FG.Att Q.params.n))) : Prop :=
  Anc (Q.trace.HonestBlocksAt Q.keys) B C

/-- Per-cut reset premises, catch-up, and honest anchors of the same window. -/
def AnchorRun : Prop :=
  ∃ (proposer : Nat → Fin Q.params.n)
    (dg : Digest (List (FG.Att Q.params.n)) (SA.Payload Q.params.n)) (g ΔF a b : Time),
    Healing.Growing.ResetPremisesUpTo Q.trace Q.keys proposer dg g ΔF a b ∧
    Healing.Growing.CatchRun Q.trace Q.keys g (2 * Q.params.Δ) ∧
    (∀ i, Healing.Growing.HonestProposalRun Q.trace Q.keys proposer
      (W.start + ![0, W.gap, 2 * W.gap, 3 * W.gap] i) (W.block i)) ∧
    Healing.drainTime Q.params a ≤ Q.params.ts W.start ∧
    Q.params.ts (W.start + 3 * W.gap) ≤ b

/-- Three successive height steps, without freezing the honest set. -/
def AnchorSteps : Prop :=
  ∀ i : Fin 3, AnchorStepAt Q.trace Q.keys (W.block i.castSucc) (W.block i.succ)

/-- Actual finalized-cache coverage at every later ready read. -/
def CacheCoverage : Prop :=
  ∀ y t j, Q.deadline ≤ t → t ≤ Q.run.2.horizon →
    Regimes.Growing.ReadyAt Q.trace Q.keys
      ((Sys (goldilocks S) V).cDur (K S A) Q.run) y t → Regimes.CutAfter Q.trace j t →
    W.Extends (W.block 0) (Q.trace.state y j).fg.F

theorem anchorRun_iff : W.AnchorRun ↔
    ∃ (proposer : Nat → Fin Q.params.n)
      (dg : Digest (List (FG.Att Q.params.n)) (SA.Payload Q.params.n)) (g ΔF a b : Time),
      Healing.Growing.ResetPremisesUpTo Q.trace Q.keys proposer dg g ΔF a b ∧
      Healing.Growing.CatchRun Q.trace Q.keys g (2 * Q.params.Δ) ∧
      (∀ i, Healing.Growing.HonestProposalRun Q.trace Q.keys proposer
        (W.start + ![0, W.gap, 2 * W.gap, 3 * W.gap] i) (W.block i)) ∧
      Healing.drainTime Q.params a ≤ Q.params.ts W.start ∧
      Q.params.ts (W.start + 3 * W.gap) ≤ b := Iff.rfl

theorem anchorSteps_iff : W.AnchorSteps ↔
    ∀ i : Fin 3, AnchorStepAt Q.trace Q.keys (W.block i.castSucc) (W.block i.succ) := Iff.rfl

theorem cacheCoverage_iff : W.CacheCoverage ↔
    ∀ y t j, Q.deadline ≤ t → t ≤ Q.run.2.horizon →
      Regimes.Growing.ReadyAt Q.trace Q.keys
        ((Sys (goldilocks S) V).cDur (K S A) Q.run) y t → Regimes.CutAfter Q.trace j t →
      W.Extends (W.block 0) (Q.trace.state y j).fg.F := Iff.rfl

end FinalWindowDataAt

end Consensus.Goldilocks.Obligations.Growing

end
