module
public import ConsensusShape.Shape
public import ConsensusShape.Compile
public import ConsensusShape.Run
public import ConsensusShape.Claims
public import ConsensusShape.Payload
public import ConsensusShape.Refinement
public import ConsensusShape.Realizable
public import ConsensusShape.Accepted
public import ConsensusShape.Values.Goldilocks
public import ConsensusShape.Values.GoldilocksSheet

/-! Layer 2 (L2), the protocol shape: generic chain shapes over the building
blocks (`Shape`), their compilation to the model (`Compile`), the shape
vocabulary and progress reader over compiled runs (`Run`), the shape claims
(`Claims`), the payload facts (`Payload`), the refinement to the L0 behaviour
(`Refinement`), coverage, the extremal selection and generic realizability
(`Realizable`), the acceptance endpoint (`Accepted`, with `Accepted.good`),
and the Goldilocks value (with its properties sheet, `GoldilocksSheet`;
`Values`). Streamlet and Tendermint are test values
(`ConsensusShapeTests/Values.lean`). -/
