module
public meta import Lean.Elab.Command

@[expose] public section

namespace CheckFixtures.BadMetaThm

/-- A legitimate definition, parent of the injected `Foo._proof_99`. -/
def Foo : Nat := 0

/-- A legitimate definition; `Foo2._proof_1` (injected, no range) is reachable only through the
hand-written companion `Foo2._sunfold` below, which is not a starting point of the reachability walk. -/
def Foo2 : Nat := 0

/-- An inductive type, parent of injected lemmas of the wrong kind. -/
inductive Col where
  | r
  | g

end CheckFixtures.BadMetaThm

open Lean Elab Command in
run_cmd liftTermElabM do
  let mk (n : Name) : Declaration :=
    .thmDecl { name := n, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro }
  -- a theorem without a declaration range
  addDecl (mk `CheckFixtures.BadMetaThm.sneaky)
  -- a fake generated auxiliary, not reachable from `Foo`
  addDecl (mk `CheckFixtures.BadMetaThm.Foo._proof_99)
  -- structural suffixes on a definition parent: `injEq` is a constructor lemma; `eq_1` does not
  -- mention its parent
  addDecl (mk `CheckFixtures.BadMetaThm.Foo.injEq)
  addDecl (mk `CheckFixtures.BadMetaThm.Foo.eq_1)
  -- every suffix tied to its parent's kind, each forged on a wrong parent (no ranges)
  for s in ["sizeOf_spec", "inj", "_flat_ctor", "ofNat_ctorIdx", "_sizeOf_1_eq", "_default", "splitter",
      "eq_def", "eq_unfold", "congr_simp"] do
    addDecl (mk (.str `CheckFixtures.BadMetaThm.Foo s))
  for s in ["injEq", "eq_1", "_default", "_proof_1"] do
    addDecl (mk (.str `CheckFixtures.BadMetaThm.Col s))
  -- a reachable auxiliary under a nested namespace of its parent `Bar` (both without ranges)
  let pf := `CheckFixtures.BadMetaThm.Bar.Inner._proof_1
  addDecl (mk pf)
  let nat := mkConst ``Nat
  let pred := mkLambda `n .default nat (mkConst ``True)
  let sub := mkApp2 (mkConst ``Subtype [1]) nat pred
  let val (p : Name) := mkApp4 (mkConst ``Subtype.mk [1]) nat pred (mkConst ``Nat.zero) (mkConst p)
  addDecl (.defnDecl (mkDefinitionValEx `CheckFixtures.BadMetaThm.Bar [] sub (val pf) .abbrev .safe []))
  -- the auxiliary reached only through a forged companion
  addDecl (mk `CheckFixtures.BadMetaThm.Foo2._proof_1)

/-- A hand-written "companion" (it has a declaration range) that makes `Foo2._proof_1` reachable. -/
def CheckFixtures.BadMetaThm.Foo2._sunfold : {n : Nat // True} :=
  ⟨0, CheckFixtures.BadMetaThm.Foo2._proof_1⟩
