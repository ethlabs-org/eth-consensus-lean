module
public import AvailableChainModel.Objects.Blocks
public import AvailableChainModel.Objects.Time

@[expose] public section

/-! Generic time observations. GLY `claude-files/a0/generic-layer.md`:
1709–1711 gives this module and requires an optional proposed block.
S3c `tip-stability/codex/scratch/a0-s3c-read-layer-fit.md`:935 lists
the observations. Step-2 item I25, D17. The v1 bridge waits for 2b. -/

-- Register the namespaces for the V2 open list without an engine import.
namespace AvailableChain.V2.Engine
end AvailableChain.V2.Engine

namespace AvailableChain.Gen.V2

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

/-- DESIGNED from GLY:1709–1711 and S3c:935: observations for one selected
output. Consumer: the time instance of the property kernel for SA
(GLY:1541–1546), with `N := O.honest` and `out := O.out`.
Use one record per output. This keeps the output type independent of the
engine state. The other fields support the inclusion and liveness reads
of I-4. An adapter must supply the observations and prove its read laws.
DC: Interface.lean:64–67; same: Require out = readAt; GLY r3.19 S102. -/
structure Obs (V : Type) where
  honest : Set V
  horizon : Time
  /-- Public reads after all events up to and including the given time. -/
  out : Time → V → Block
  proposalTime : Slot → Time
  proposer : Slot → V
  /-- The observed proposal, if present. Slot 0 need not have one. -/
  proposed : Slot → Option Block
  awake : V → Time → Prop
  opening : Set Slot

end AvailableChain.Gen.V2
