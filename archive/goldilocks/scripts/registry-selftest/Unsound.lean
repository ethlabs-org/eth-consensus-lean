import AvailableChainRegistry
import AvailableChainGridCO.Tests.Smoke
import AvailableChainSA.Tests.Smoke
import AvailableChainSAPC.Tests.Smoke

/-! Self-test of `scripts/Registry.lean` with `sorry` (see `README.md`). Not a
Lake library; the registry scan does not read it. The `sorry` is on purpose:
the script must show the row as `UNSOUND`. -/

namespace RegistrySelfTest

open AvailableChain.Framework AvailableChain.Framework.Catalog
open AvailableChain.Registry

/-- A family row with `sorry`: `UNSOUND(sorryAx) (family)`. -/
theorem sorryFamily (p : AvailableChain.GridCO.Params) :
    ac43.holdsAt (GridCO.gridInst p) (AvailableChain.GridCO.gridConstants p 1) :=
  sorry

/-- A witness with `sorry`, for the bad-axiom witness test in `README.md`. -/
def badWitness : AvailableChain.SA.Params := sorry

/-- An `unsafe` witness, for the unsafe-witness test in `README.md`. -/
unsafe def unsafeWitness : AvailableChain.SA.Params := unsafeWitness

end RegistrySelfTest
