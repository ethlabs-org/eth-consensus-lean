module
public import AvailableChainLStar.Statements.Contract
public meta import AvailableChainLStar.Model.Protocol
public meta import AvailableChainModel.Objects.Blocks

@[expose] public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.LStar.Tests

open AvailableChain
open AvailableChain.Generic
open AvailableChain.LStar

def smokeParams : Params where
  Δ := 2
  L := 10
  η := 8
  deltaPos := by norm_num
  lockLong := by norm_num
  etaNonneg := by norm_num
  lockPhase := by decide

def honestNodes : List (Fin 4) := [0, 1, 2]

def smokeEnv : Env (Fin 4) where
  Δ := 2
  Δ_pos := by norm_num
  t_GST := 0
  t_GST_nonneg := by norm_num
  awake := fun _ _ => true

def smokeProposalMsg : Msg 4 :=
  (propose smokeParams (clock smokeParams (initial 4) 8) 1).getD (.head .genesis)

def smokeProposalBlock : Block := (block smokeProposalMsg).getD .genesis

def smokeProposal : Wire 4 := ⟨.proposer 1, smokeProposalMsg⟩

def smokeHeadMsg : Msg 4 :=
  let st := process smokeParams (clock smokeParams (initial 4) 8) smokeProposal
  (act smokeParams (clock smokeParams st 10) 1).getD (.head .genesis)

def smokeHeads : List (Wire 4) :=
  honestNodes.map (fun i => ⟨.seat 1 i, smokeHeadMsg⟩)

def ticks (t : Time) : List (Event (Fin 4) (Wire 4)) :=
  honestNodes.map (fun v => .tick v t)

def smokeEvents : List (Event (Fin 4) (Wire 4)) :=
  ticks 6 ++ ticks 8 ++
  honestNodes.map (fun v => .deliver v smokeProposal 9) ++
  ticks 10 ++
  honestNodes.flatMap (fun v => smokeHeads.map (fun o => .deliver v o 11)) ++
  ticks 12 ++ ticks 20

/-- Three awake seats receive the honest slot-1 proposal and all three
HEADs before the early cutoff. Seat 3 is faulty and silent. -/
def smokeRun : Run (Fin 4) (lstar smokeParams 4) where
  honest := {0, 1, 2}
  horizon := 20
  events := smokeEvents
  seatOf := fun _ => Equiv.refl (Fin 4)
  proposerOf := fun _ => 0

def smokeOutputs : List (Block × Block) :=
  honestNodes.map (fun v =>
    let st := Run.readAt (lstar smokeParams 4) smokeRun 20 v
    (stable st, confirmed st))

def smokePass : Bool :=
  smokeProposalBlock != Block.genesis &&
    honestNodes.all (fun v =>
      let st := Run.readAt (lstar smokeParams 4) smokeRun 20 v
      Block.preceq smokeProposalBlock (stable st) &&
        Block.preceq smokeProposalBlock (confirmed st))

/-- E4 second-wire test: after the slot-1 proposal is stored, a second
well-formed wire with the same block and another raw view is excluded. Before
the block is stored, that wire is not excluded. -/
def smokeStored : State 4 :=
  process smokeParams (clock smokeParams (initial 4) 8) smokeProposal

def smokeSecondWire : Wire 4 :=
  ⟨.proposer 1, .proposal smokeProposalBlock [⟨.seat 0 3, .genesis⟩] []⟩

def smokeSecondWirePass : Bool :=
  wellFormed smokeProposal && wellFormed smokeSecondWire &&
    smokeSecondWire != smokeProposal &&
    decide (smokeProposalBlock ∈ smokeStored.blocks) &&
    excludes smokeStored smokeSecondWire &&
    !excludes smokeStored smokeProposal &&
    !excludes (clock smokeParams (initial 4) 8) smokeSecondWire

-- `#guard` fails the build if the test fails; `#eval` does not.
set_option linter.hashCommand false in
#guard smokeSecondWirePass

/-- The honest slot-1 proposal has body 0. Each honest reader outputs it as
stable and confirmed at time 20. The run stores one block besides genesis, so
no output depends on a root order. -/
example : smokeProposalBlock = .node .genesis 1 (nodeRoot Block.genesis.root 1 0) 0 := by decide
example : smokeOutputs = List.replicate 3 (.node .genesis 1 (nodeRoot Block.genesis.root 1 0) 0,
    .node .genesis 1 (nodeRoot Block.genesis.root 1 0) 0) := by
  decide
example : smokePass = true := by decide
example : honestNodes.all (fun v => smokeEnv.awake v 10) = true := by decide

end AvailableChain.LStar.Tests
end
