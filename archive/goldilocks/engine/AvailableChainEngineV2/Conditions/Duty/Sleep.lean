module
public import AvailableChainEngineV2.Engine.Duty.Run
public import AvailableChainEngineV2.Conditions.Sleep -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.V2.D

open AvailableChain

variable {V In : Type} {P : ProtocolSpecD In}

def Wakes (E : Generic.Env V) (v : V) (t : Time) : Prop :=
  E.awake v t = true ∧ E.awake v (t - 1) = false

def AwakeOn (E : Generic.Env V) (v : V) (a b : Time) : Prop :=
  ∀ u, a ≤ u → u < b → E.awake v u = true

def AwakeOnClosed (E : Generic.Env V) (v : V) (a b : Time) : Prop :=
  ∀ u, a ≤ u → u ≤ b → E.awake v u = true

structure SleepWellFormed (E : Generic.Env V) (rho : Run V P) : Prop where
  tick_awake : ∀ v t, Event.tick v t ∈ rho.events → E.awake v t = true
  deliver_awake : ∀ v o t, Event.deliver v o t ∈ rho.events → E.awake v t = true
  restart_awake : ∀ v t, Event.restart v t ∈ rho.events → E.awake v t = true
  wake_restart : ∀ v ∈ rho.honest, ∀ t, 0 < t → t ≤ rho.horizon →
    Wakes E v t → Event.restart v t ∈ rho.events

def RestartsAtWakes (E : Generic.Env V) (rho : Run V P) : Prop :=
  ∀ v t, Event.restart v t ∈ rho.events → 0 < t ∧ Wakes E v t

def NoRestartOn (rho : Run V P) (v : V) (a b : Time) : Prop :=
  ∀ (i : Nat) t, rho.events[i]? = some (.restart v t) → a < t → t < b → False

def NoRestartAfter (rho : Run V P) (v : V) (a : Time) : Prop :=
  ∀ (i : Nat) t, rho.events[i]? = some (.restart v t) → t ≤ a

set_option linter.unusedVariables false in
def LinkReadyOn (E : Generic.Env V) (rho : Run V P)
    (src dst : V) (a d : Time) : Prop :=
  AwakeOn E dst a d

end AvailableChain.V2.D

end
