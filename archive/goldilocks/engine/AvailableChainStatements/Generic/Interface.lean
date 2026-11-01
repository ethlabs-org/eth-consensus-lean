module
public import AvailableChainModel.Generic.Run
public import AvailableChainModel.Objects.Blocks

@[expose] public section

namespace AvailableChain.Statements.Generic

open AvailableChain

variable {V : Type} [DecidableEq V] {n : Nat}

/-- What an instance exposes. The proposal schedule (`proposalTime`,
`slotsAt`) is part of the protocol; the proposer of a slot is run data
(`Run.proposerOf`). There is no committee field: every label has a committee of
all `n` seats, assigned by the run. -/
structure Interface (P : AvailableChain.Generic.ProtocolSpec n) where
  /-- The two user-facing outputs, as getters on the node state. -/
  confirmed : P.State → Block
  stable : P.State → Block
  /-- The block that a proposal payload proposes. -/
  block : P.Payload → Option Block
  /-- Slots at which a period opens. This is used only by the recurrence
  premise. -/
  opening : Slot → Prop

abbrev Output {n : Nat} (P : AvailableChain.Generic.ProtocolSpec n) :=
  P.State → Block

/-- The output `g` read at node `v` and time `t`. -/
def readAt (P : AvailableChain.Generic.ProtocolSpec n)
    (rho : AvailableChain.Generic.Run V P) (g : Output P)
    (v : V) (t : Time) : Block :=
  g (AvailableChain.Generic.Run.readAt P rho t v)

end AvailableChain.Statements.Generic

end
