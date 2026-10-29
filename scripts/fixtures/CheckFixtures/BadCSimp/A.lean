module

@[expose] public section

namespace CheckFixtures.BadCSimp

def f (n : Nat) : Nat := n

def g (n : Nat) : Nat := n

@[csimp] theorem f_eq : @f = @g := rfl

end CheckFixtures.BadCSimp
