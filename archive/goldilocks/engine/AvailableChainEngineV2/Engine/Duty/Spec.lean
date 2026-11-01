module
public import AvailableChainModel.Objects.Time
public import AvailableChainEngineV2.Engine.Objects

@[expose] public section

namespace AvailableChain.V2

open AvailableChain

/-- A protocol with separate action duties and signing labels. -/
structure ProtocolSpecD (In : Type) where
  State : Type

  Label : Type
  Duty : Type
  signLabel : Duty → Label

  seats : Label → Nat

  Payload : Type

  Durable : Type
  init : State

  clock : State → Time → State

  actTime : Duty → Time

  duties : Time → List Duty
  duties_spec : ∀ ℓ t, ℓ ∈ duties t ↔ actTime ℓ = t
  duties_nodup : ∀ t, (duties t).Nodup

  act : State → Duty → In → Option Payload

  gossip : State → Time → List Payload

  process : State → Signed Label seats Payload → State

  selfVisible : Label → Bool

  recordOwn : State → Signed Label seats Payload → State

  durable : State → Durable

  restore : Durable → Time → State

  wellFormed : Signed Label seats Payload → Bool

  depsPresent : State → Signed Label seats Payload → Bool

  processed : State → Signed Label seats Payload → Bool

  excludes : State → Signed Label seats Payload → Bool

  handles : State → Signed Label seats Payload → Signed Label seats Payload → Prop

  carries : Signed Label seats Payload → Signed Label seats Payload → Prop

namespace ProtocolSpecD

variable {In : Type}

abbrev Object (P : ProtocolSpecD In) : Type :=
  Signed P.Label P.seats P.Payload

def objSelfVisible (P : ProtocolSpecD In) (o : P.Object) : Bool :=
  match o.auth with
  | .seat ℓ _ => P.selfVisible ℓ
  | .none => false

end ProtocolSpecD

end AvailableChain.V2

end
