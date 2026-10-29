module
public meta import Lean.Elab.Command

@[expose] public section

namespace CheckFixtures.BadMetaThm

/-- A legitimate definition, parent of the injected `Foo._proof_99`. -/
def Foo : Nat := 0

end CheckFixtures.BadMetaThm

open Lean Elab Command in
run_cmd liftTermElabM do
  let mk (n : Name) : Declaration :=
    .thmDecl { name := n, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro }
  -- a theorem without a declaration range
  addDecl (mk `CheckFixtures.BadMetaThm.sneaky)
  -- a fake generated auxiliary, not reachable from `Foo`
  addDecl (mk `CheckFixtures.BadMetaThm.Foo._proof_99)
