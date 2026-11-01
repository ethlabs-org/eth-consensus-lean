module
public import AvailableChainEngineV2.TestSupport.Engine

@[expose] public section

namespace AvailableChain.V2.Tests.Sleep

open AvailableChain

/-- A clock and a receipt list. Restart clears receipts and sets the exact time. -/
abbrev toy : ProtocolSpec Unit :=
  { Tests.specA with
    State := Time × List Nat
    Durable := Unit
    init := (0, [])
    clock := fun st t => (t, st.2)
    act := fun _ _ _ => none
    gossip := fun st _ =>
      if st.1 = 0 then [1] else if st.1 = 4 then [2] else []
    process := fun st o => (st.1, o.payload :: st.2)
    recordOwn := fun st _ => st
    durable := fun _ => ()
    restore := fun _ t => (t, [])
    processed := fun st o => decide (o.payload ∈ st.2)
    depsPresent := fun _ _ => true
    excludes := fun _ _ => false
    handles := fun _ o o' => o = o' }

def first : toy.Object := ⟨.none, 1⟩
end AvailableChain.V2.Tests.Sleep

end
