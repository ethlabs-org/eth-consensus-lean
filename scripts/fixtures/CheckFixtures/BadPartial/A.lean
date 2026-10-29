module

@[expose] public section

namespace CheckFixtures.BadPartial

partial def loop (n : Nat) : Nat := loop (n + 1)

end CheckFixtures.BadPartial
