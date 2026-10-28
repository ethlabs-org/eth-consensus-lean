module
public import ConsensusShape.Shape
public import ConsensusShape.Compile
public import ConsensusShape.Run
public import ConsensusShape.Claims
public import ConsensusShape.Payload
public import ConsensusShape.Refinement
public import ConsensusShape.Realizable
public import ConsensusShape.Accepted
public import ConsensusShape.Values.Common
public import ConsensusShape.Values.Goldilocks
public import ConsensusShape.Values.Streamlet
public import ConsensusShape.Values.Tendermint

/-! Layer 1, the protocol shape: generic chain shapes over the building
blocks (`Shape`), their compilation to the model (`Compile`), the shape
vocabulary over compiled runs (`Run`), the shape claims (`Claims`), the payload
facts (`Payload`), the refinement to the problem claims (`Refinement`),
coverage and joint realizability (`Realizable`), the acceptance endpoint
(`Accepted`), and the Goldilocks,
Streamlet and Tendermint values (`Values`). -/
