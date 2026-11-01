module
public import AvailableChainModel.Objects.Blocks
public import AvailableChainEngineV2.Engine.Duty.Run

@[expose] public section

namespace AvailableChain.V2.D

open AvailableChain

variable {V : Type} {In : Type} {P : ProtocolSpecD In}

structure Interface (P : ProtocolSpecD In) where

  confirmed : P.State → Block
  stable : P.State → Block

  block : P.Payload → Option Block

  opening : Slot → Prop

  propLabel : Slot → P.Label
  propDuty : Slot → P.Duty
  propDuty_label : ∀ s, P.signLabel (propDuty s) = propLabel s

  propLabel_single : ∀ s, P.seats (propLabel s) = 1

  propLabel_injective : Function.Injective propLabel

def proposalTime (I : Interface P) (s : Slot) : Time :=
  P.actTime (I.propDuty s)

def propSeat (I : Interface P) (s : Slot) : Fin (P.seats (I.propLabel s)) :=
  Fin.cast (I.propLabel_single s).symm 0

def proposerOf (rho : Run V P) (I : Interface P) (s : Slot) : V :=
  rho.seatOf (I.propLabel s) (propSeat I s)

theorem eq_propSeat (I : Interface P) (s : Slot) (i : Fin (P.seats (I.propLabel s))) :
    i = propSeat I s := by
  have hi : i.val < 1 := I.propLabel_single s ▸ i.isLt
  exact Fin.ext (by simp [propSeat]; omega)

theorem holder_propLabel (rho : Run V P) (I : Interface P) (s : Slot)
    (i : Fin (P.seats (I.propLabel s))) :
    Run.holder rho (.seat (I.propLabel s) i) = some (proposerOf rho I s) := by
  rw [eq_propSeat I s i]; rfl

abbrev Output (P : ProtocolSpecD In) :=
  P.State → Block

variable [DecidableEq V]

def outputAt (E : Generic.Env V) (rho : Run V P) (g : Output P) (v : V) (t : Time) :
    Block :=
  g (Run.readAt E rho t v)

def BlockInRun (E : Generic.Env V) (I : Interface P) (rho : Run V P) (B : Block) : Prop :=
  B = .genesis ∨ ∃ v o t tip,
    (Run.processes rho v o t ∨ Run.emits E rho v o t) ∧
    I.block o.payload = some tip ∧ Block.Preceq B tip

def RootInjective (E : Generic.Env V) (I : Interface P) (rho : Run V P) : Prop :=
  ∀ B C, BlockInRun E I rho B → BlockInRun E I rho C →
    B.root = C.root → B = C

end AvailableChain.V2.D

end
