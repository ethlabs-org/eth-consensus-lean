module
public import ConsensusLean.Statements.Review
public import ConsensusLean.Instances.Goldilocks.Statements.FGSafety
public import ConsensusLean.Instances.Goldilocks.Statements.AC.Steps
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Local
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Trace
public import ConsensusLean.Instances.Goldilocks.Statements.AC.Base
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Service
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Interface
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Node
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Persist
public import Solution

@[expose] public section

/-! Negative fixture for check.sh step 9 (challenge_ok; never built): the challenge imports more than the statements module. -/

theorem Consensus.Review.acceptedGood : Consensus.Review.AcceptedGood := sorry
theorem Consensus.Review.regimesRealizable : Consensus.Review.RegimesRealizable := sorry
theorem Consensus.Review.logFaithful : Consensus.Review.LogFaithful := sorry
theorem Consensus.Review.heldIffServed : Consensus.Review.HeldIffServed := sorry
theorem Consensus.Goldilocks.FG.fGSafety : Consensus.Goldilocks.FG.FGSafety := sorry
theorem Consensus.Goldilocks.SA.aCSteps : Consensus.Goldilocks.SA.ACSteps := sorry
theorem Consensus.Goldilocks.Store.fGStoreLocal : Consensus.Goldilocks.Store.FGStoreLocal := sorry
theorem Consensus.Goldilocks.Store.fGStoreTrace : Consensus.Goldilocks.Store.FGStoreTrace := sorry
theorem Consensus.Goldilocks.SA.aCBase : Consensus.Goldilocks.SA.ACBase := sorry
theorem Consensus.Goldilocks.localRunReachable : Consensus.Goldilocks.LocalRunReachable := sorry
theorem Consensus.Goldilocks.Store.fGStoreService : Consensus.Goldilocks.Store.FGStoreService := sorry
theorem Consensus.Goldilocks.Compose.composeInterfaceStatements : Consensus.Goldilocks.Compose.ComposeInterfaceStatements := sorry
theorem Consensus.Goldilocks.Compose.composeNodeStatements : Consensus.Goldilocks.Compose.ComposeNodeStatements := sorry
theorem Consensus.Goldilocks.Compose.eventOrder : Consensus.Goldilocks.Compose.EventOrder := sorry
theorem Consensus.Goldilocks.Compose.readyImpliesJoined : Consensus.Goldilocks.Compose.ReadyImpliesJoined := sorry
theorem Consensus.Goldilocks.Compose.aCProjection : Consensus.Goldilocks.Compose.ACProjection := sorry
theorem Consensus.Goldilocks.Compose.fGProjection : Consensus.Goldilocks.Compose.FGProjection := sorry
theorem Consensus.Goldilocks.Compose.goldilocksACProjection : Consensus.Goldilocks.Compose.GoldilocksACProjection := sorry
theorem Consensus.Goldilocks.Compose.groupStatesReachable : Consensus.Goldilocks.Compose.GroupStatesReachable := sorry
theorem Consensus.Goldilocks.Compose.syncProjection : Consensus.Goldilocks.Compose.SyncProjection := sorry
theorem Consensus.Goldilocks.Compose.joinedProjection : Consensus.Goldilocks.Compose.JoinedProjection := sorry
theorem Consensus.Goldilocks.Compose.honestFastConfirmationsPersist : Consensus.Goldilocks.Compose.HonestFastConfirmationsPersist := sorry
theorem Consensus.Goldilocks.Compose.recentSourceNextVote : Consensus.Goldilocks.Compose.RecentSourceNextVote := sorry

end
