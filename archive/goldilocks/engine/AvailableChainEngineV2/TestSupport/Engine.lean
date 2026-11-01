module
public import AvailableChainEngineV2.Engine.Run -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.V2.Tests

open AvailableChain AvailableChain.V2

/-- The duties of `specA`: label `false` at time 0, label `true` at time 1. -/
def dutiesA (t : Time) : List Bool :=
  if t = 0 then [false] else if t = 1 then [true] else []

/-- Two labels with one seat each. The state is a number. Every label's
payload is the state. Label `true` is self-visible, and its record adds 10. A
delivery adds the payload plus 1. -/
abbrev specA : ProtocolSpec Unit where
  State := Nat
  Label := Bool
  seats := fun _ => 1
  Payload := Nat
  Durable := Unit
  init := 0
  clock := fun s _ => s
  actTime := fun b => if b then 1 else 0
  duties := dutiesA
  duties_spec := by
    intro ℓ t
    cases ℓ <;> by_cases h0 : t = 0 <;> by_cases h1 : t = 1 <;>
      simp [dutiesA, h0, h1, eq_comm]
  duties_nodup := by
    intro t
    unfold dutiesA
    split_ifs <;> simp
  act := fun s _ _ => some s
  gossip := fun _ _ => []
  process := fun s o => s + o.payload + 1
  selfVisible := fun b => b
  recordOwn := fun s _ => s + 10
  durable := fun _ => ()
  restore := fun _ _ => 0
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ o o' => o = o'
  carries := fun _ _ => False

end AvailableChain.V2.Tests

end
