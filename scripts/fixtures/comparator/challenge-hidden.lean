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

@[expose] public section

/-! Negative fixture for check.sh step 9 (challenge_ok; never built): a declaration between two
comments on one line. -/

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
/- harmless -/ axiom extra : False /- harmless -/

end
