module
public import ConsensusSpec.Problem.Basic
public import ConsensusSpec.Problem.Network
public import ConsensusSpec.Problem.Properties
public import ConsensusSpec.Problem.Regimes
public import ConsensusSpec.Problem.Good
public import ConsensusSpec.Model.Objects
public import ConsensusSpec.Model.Protocol
public import ConsensusSpec.Model.Run
public import ConsensusSpec.Model.Conditions
public import ConsensusSpec.Model.System
public import ConsensusSpec.Model.Served
public import ConsensusSpec.Blocks.TimeGrid
public import ConsensusSpec.Blocks.Progress
public import ConsensusSpec.Blocks.Chains
public import ConsensusSpec.Blocks.Payload
public import ConsensusSpec.Shape.Shape
public import ConsensusSpec.Shape.Compile
public import ConsensusSpec.Shape.Run
public import ConsensusSpec.Shape.Claims
public import ConsensusSpec.Shape.ProgressFit
public import ConsensusSpec.Shape.Active
public import ConsensusSpec.Shape.Accepted
public import ConsensusSpec.Statements

/-! The trusted surface: the definitions of the consensus problem (L0, `Problem`), the
execution model (L1, `Model`), the building blocks (`Blocks`) and the protocol shape (L2, `Shape`),
with the acceptance endpoint `Shape.Accepted` and the review statements (`Statements`). Imports
only; owns no declaration. Every module under `ConsensusSpec/` imports only `ConsensusSpec` modules,
Mathlib and Lean. -/
