module
public import AvailableChainModel.Objects.Blocks
public import AvailableChainEngineV2.Engine.Run

@[expose] public section

/-! The interface of an instance, the output reader and the root condition
over v2 runs (plan 2a, Task 5). The texts of `Interface`, `Output`, the output
reader, `BlockInRun`, `RootInjective` and the root premise are the shared v1
texts (`AvailableChainStatements/Generic/Interface.lean`,
`AvailableChainStatements/Generic/Conditions.lean`,
`AvailableChainKit/Roots.lean`) over v2 runs. The v1 output reader `readAt` is
`outputAt` here, because `Run.readAt` is the world reader (DC N9). -/

namespace AvailableChain.V2

open AvailableChain

variable {V : Type} {In : Type} {P : ProtocolSpec In}

/-- What an instance exposes. There is no proposal schedule field and no
proposer field: the proposal duty of slot `s` is the label `propLabel s`,
which has one seat (`propLabel_single`) and belongs to no other slot
(`propLabel_injective`). Its act time is the proposal time
(`proposalTime`), and the holder of its seat is run data (`proposerOf`). -/
structure Interface (P : ProtocolSpec In) where
  /-- The two user-facing outputs, as getters on the node state. -/
  confirmed : P.State → Block
  stable : P.State → Block
  /-- The block that a proposal payload proposes. -/
  block : P.Payload → Option Block
  /-- Slots at which a period opens. This is used only by the recurrence
  premise. -/
  opening : Slot → Prop
  /-- The proposal duty of a slot. -/
  propLabel : Slot → P.Label
  /-- A proposal duty has one seat. -/
  propLabel_single : ∀ s, P.seats (propLabel s) = 1
  /-- Each slot has its own proposal duty, as each slot had its own
  `Auth.proposer s` in v1. So the seat maps of distinct slots are independent
  run data, and the proposers of distinct slots vary independently over
  runs. -/
  propLabel_injective : Function.Injective propLabel

/-- The proposal time of slot `s`: the act time of its proposal duty. -/
def proposalTime (I : Interface P) (s : Slot) : Time :=
  P.actTime (I.propLabel s)

/-- The one seat of the proposal duty of slot `s`. -/
def propSeat (I : Interface P) (s : Slot) : Fin (P.seats (I.propLabel s)) :=
  Fin.cast (I.propLabel_single s).symm 0

/-- The proposer of slot `s` in this run: the holder of the one seat of its
proposal duty. -/
def proposerOf (rho : Run V P) (I : Interface P) (s : Slot) : V :=
  rho.seatOf (I.propLabel s) (propSeat I s)

/-- Every seat of a proposal duty is its one seat. -/
theorem eq_propSeat (I : Interface P) (s : Slot) (i : Fin (P.seats (I.propLabel s))) :
    i = propSeat I s := by
  have hi : i.val < 1 := I.propLabel_single s ▸ i.isLt
  exact Fin.ext (by simp [propSeat]; omega)

/-- The holder of any seat of a proposal duty is the proposer. -/
theorem holder_propLabel (rho : Run V P) (I : Interface P) (s : Slot)
    (i : Fin (P.seats (I.propLabel s))) :
    Run.holder rho (.seat (I.propLabel s) i) = some (proposerOf rho I s) := by
  rw [eq_propSeat I s i]; rfl

/-- An output: a getter on the node state. -/
abbrev Output (P : ProtocolSpec In) :=
  P.State → Block

variable [DecidableEq V]

/-- The output `g` read at node `v` and time `t`, after every event up to and
including time `t` (`Run.readAt`). -/
def outputAt (E : Generic.Env V) (rho : Run V P) (g : Output P) (v : V) (t : Time) :
    Block :=
  g (Run.readAt E rho t v)

/-- Genesis and every ancestor (including the tip itself) of a block
named by `I.block` in a delivered or emitted payload. -/
def BlockInRun (E : Generic.Env V) (I : Interface P) (rho : Run V P) (B : Block) : Prop :=
  B = .genesis ∨ ∃ v o t tip,
    (Run.processes rho v o t ∨ Run.emits E rho v o t) ∧
    I.block o.payload = some tip ∧ Block.Preceq B tip

/-- Injectivity of block roots on genesis and the ancestors of all blocks
named by this run. ROOT-DIGEST W1 keeps this explicit DC-style scope premise. -/
def RootInjective (E : Generic.Env V) (I : Interface P) (rho : Run V P) : Prop :=
  ∀ B C, BlockInRun E I rho B → BlockInRun E I rho C →
    B.root = C.root → B = C

end AvailableChain.V2

end
