module
public import ConsensusSpec.Shape.Shape
public import ConsensusSpec.Shape.Compile
public import ConsensusSpec.Shape.Run
public import ConsensusSpec.Shape.Claims
public import ConsensusSpec.Shape.ProgressFit
public import ConsensusSpec.Shape.Active
public import ConsensusSpec.Shape.Accepted
public import ConsensusProofs.Problem
public import ConsensusProofs.Model
public import ConsensusProofs.Blocks.Facts
public import ConsensusProofs.Shape.Payload
public import ConsensusProofs.Shape.Refinement
public import ConsensusProofs.Shape.Realizable
public import ConsensusProofs.Shape.Accepted
public import ConsensusProofs.Shape.Service

/-! Layer 2 (L2), proofs: the shape definitions (`ConsensusSpec/Shape`) with the payload facts
(`Payload`), the refinement to the L0 behaviour (`Refinement`), coverage, the extremal selection and
generic realizability (`Realizable`), the acceptance theorems (`Accepted`, with `Accepted.good`) and
the corollary `Accepted.activeService` (`Service`). Imports only. -/
