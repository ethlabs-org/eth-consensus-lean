module
public import ConsensusLean.Statements.Review
public import ConsensusLean.Main
public import ConsensusLean.Proofs.RegimesRealizable.Main
public import ConsensusLean.Proofs.Faithful.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.FGSafety.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.ACSteps.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.FGStore.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.ACBase.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.ComposeAnyAC.Main

@[expose] public section

/-! # Proofs of the review statements

Each statement of `ConsensusLean/Statements/Review.lean` is proved by the existing theorem whose
type it is, so the kernel checks the statement against that theorem's type; each finished instance
milestone is proved by its milestone proof. This module is the comparator's solution module
(`comparator.json`). -/

namespace Consensus.Review

theorem acceptedGood : AcceptedGood := @Consensus.Shape.Accepted.good

theorem regimesRealizable : RegimesRealizable := @Consensus.Shape.regimes_realizable

theorem logFaithful : LogFaithful := @Consensus.Model.sysOf_log_faithful

theorem heldIffServed : HeldIffServed := @Consensus.Model.Run.held_iff_served

end Consensus.Review

/-! The finished instance milestones: each statement is the milestone definition itself. -/

/-- Goldilocks M₁, FG safety. -/
theorem Consensus.Goldilocks.FG.fGSafety : Consensus.Goldilocks.FG.FGSafety :=
  Consensus.Goldilocks.FG.fg_safety

/-- Goldilocks ACSteps, the AC step lemmas. -/
theorem Consensus.Goldilocks.SA.aCSteps : Consensus.Goldilocks.SA.ACSteps :=
  Consensus.Goldilocks.SA.acSteps

/-- Goldilocks FGStore, part 1: one FG store. -/
theorem Consensus.Goldilocks.Store.fGStoreLocal : Consensus.Goldilocks.Store.FGStoreLocal :=
  Consensus.Goldilocks.Store.fg_store_local

/-- Goldilocks FGStore, part 2 so far: FG traces (G1.4, the core of G1.10). -/
theorem Consensus.Goldilocks.Store.fGStoreTrace : Consensus.Goldilocks.Store.FGStoreTrace :=
  Consensus.Goldilocks.Store.fg_store_trace

/-- Goldilocks ACBase, the AC interface and the SA's foundations. -/
theorem Consensus.Goldilocks.SA.aCBase : Consensus.Goldilocks.SA.ACBase :=
  Consensus.Goldilocks.SA.acBase

/-- Goldilocks ACBase: the AC trace contract gives reachable states. -/
theorem Consensus.Goldilocks.localRunReachable : Consensus.Goldilocks.LocalRunReachable :=
  Consensus.Goldilocks.localRun_reachable

/-- Goldilocks FGStore, part 3: the FG service lemmas (G1.6–G1.8, G1.9 (a)). -/
theorem Consensus.Goldilocks.Store.fGStoreService : Consensus.Goldilocks.Store.FGStoreService :=
  Consensus.Goldilocks.Store.fg_store_service

/-- Goldilocks Compose/AnyAC: the interface statements (C0.1, C0.3), for any AC. -/
theorem Consensus.Goldilocks.Compose.composeInterfaceStatements :
    Consensus.Goldilocks.Compose.ComposeInterfaceStatements :=
  Consensus.Goldilocks.Compose.compose_interface_statements

/-- Goldilocks Compose/AnyAC: the node statements (C0.2, C0.4, C0.5), for any AC. -/
theorem Consensus.Goldilocks.Compose.composeNodeStatements :
    Consensus.Goldilocks.Compose.ComposeNodeStatements :=
  Consensus.Goldilocks.Compose.compose_node_statements

end
