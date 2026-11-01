import AvailableChainRegistry
import AvailableChainGridCO.Tests.Smoke
import AvailableChainSA.Tests.Smoke
import AvailableChainSAPC.Tests.Smoke

/-! Self-test of the family rule and the instance column of
`scripts/Registry.lean`. Not a Lake library; the registry scan does not read it.
Run it with `--selftest` (see `README.md`). Each `neg*` row must be
CONDITIONAL, each `unsafe*` row `UNSOUND(unsafe)`, each `pos*` row a family. -/

namespace RegistrySelfTest

open AvailableChain.Framework AvailableChain.Framework.Catalog
open AvailableChain.Registry

abbrev GP := AvailableChain.GridCO.Params
abbrev Sm := AvailableChain.GridCO.Tests.smokeParams

/-- A data type with a `False` field (Astra). -/
structure HiddenAssumption : Type where
  proof : False

/-! Binders that are not an allowed data binder. -/

theorem negEmpty (e : Empty) :
    ac43.holdsAt (GridCO.gridInst Sm) (AvailableChain.GridCO.gridConstants Sm 1) :=
  e.elim

theorem negPLiftFalse (h : PLift False) :
    ac43.holdsAt (GridCO.gridInst Sm) (AvailableChain.GridCO.gridConstants Sm 1) :=
  h.down.elim

theorem negHidden (h : HiddenAssumption) :
    ac43.holdsAt (GridCO.gridInst Sm) (AvailableChain.GridCO.gridConstants Sm 1) :=
  h.proof.elim

theorem negHiddenFun (h : Nat → HiddenAssumption) :
    ac43.holdsAt (GridCO.gridInst Sm) (AvailableChain.GridCO.gridConstants Sm 1) :=
  (h 0).proof.elim

/-- An implicit binder counts as a binder. -/
theorem negImplicit {h : PLift False} :
    ac43.holdsAt (GridCO.gridInst Sm) (AvailableChain.GridCO.gridConstants Sm 1) :=
  h.down.elim

/-- A `Prop` behind an `abbrev`. -/
abbrev FalseP : Prop := False
theorem negFalsePropAbbrev (h : FalseP) :
    ac43.holdsAt (GridCO.gridInst Sm) (AvailableChain.GridCO.gridConstants Sm 1) :=
  h.elim

/-- `Empty` behind an `abbrev`. -/
abbrev E := Empty
theorem negEmptyAbbrev (e : E) :
    ac43.holdsAt (GridCO.gridInst Sm) (AvailableChain.GridCO.gridConstants Sm 1) :=
  nomatch e

/-! Two binders, or a family binder on a kind other than `profile-holds`. -/

theorem negTwoParams (p _q : GP) :
    ac43.holdsAt (GridCO.gridInst p) (AvailableChain.GridCO.gridConstants p 1) :=
  GridCO.grid_holds p

theorem negParamsAndProp (p : GP) (_h : True) :
    ac43.holdsAt (GridCO.gridInst p) (AvailableChain.GridCO.gridConstants p 1) :=
  GridCO.grid_holds p

/-- FAMILY is for `profile-holds` only. -/
def negCert (_p : AvailableChain.GridCO.Params) :
    Cert safeConfirmed Counter.counterInst :=
  Counter.certSafeConfirmed

/-! Types built from the allowed type. The match is syntactic, so each one is
CONDITIONAL, also when it is definitionally equal to an allowed type. -/

theorem negAlias (p : GP) :
    ac43.holdsAt (GridCO.gridInst p) (AvailableChain.GridCO.gridConstants p 1) :=
  GridCO.grid_holds p

theorem negSubtype (q : {_p : AvailableChain.GridCO.Params // False}) :
    ac43.holdsAt (GridCO.gridInst q.1) (AvailableChain.GridCO.gridConstants q.1 1) :=
  q.2.elim

theorem negPLift (q : PLift AvailableChain.GridCO.Params) :
    ac43.holdsAt (GridCO.gridInst q.down) (AvailableChain.GridCO.gridConstants q.down 1) :=
  GridCO.grid_holds q.down

@[reducible] def HidArg (_n : Nat) : Type := AvailableChain.GridCO.Params
theorem negHidArg (q : HidArg 0) :
    ac43.holdsAt (GridCO.gridInst q) (AvailableChain.GridCO.gridConstants q 1) :=
  GridCO.grid_holds q

@[reducible] def Sel : Bool → Type
  | true => AvailableChain.GridCO.Params
  | false => Empty
theorem negSelTrue (q : Sel true) :
    ac43.holdsAt (GridCO.gridInst q) (AvailableChain.GridCO.gridConstants q 1) :=
  GridCO.grid_holds q
theorem negSelFalse (q : Sel false) :
    ac43.holdsAt (GridCO.gridInst Sm) (AvailableChain.GridCO.gridConstants Sm 1) :=
  nomatch q

theorem negOptParam (q : AvailableChain.GridCO.Params := Sm) :
    ac43.holdsAt (GridCO.gridInst q) (AvailableChain.GridCO.gridConstants q 1) :=
  GridCO.grid_holds q

/-! `unsafe` self-references: they prove any type without an axiom. -/

unsafe def unsafeClosed :
    ac43.holdsAt (GridCO.gridInst Sm) (AvailableChain.GridCO.gridConstants Sm 1) :=
  unsafeClosed

unsafe def unsafeFamily (q : AvailableChain.GridCO.Params) :
    ac43.holdsAt (GridCO.gridInst q) (AvailableChain.GridCO.gridConstants q 1) :=
  unsafeFamily q

/-- The binder does not reach the instance: a row at one parameter record, so
CONDITIONAL, and its instance column is the closed term (final review F2). -/
theorem negFamLeak (_p : AvailableChain.GridCO.Params) :
    ac43.holdsAt (GridCO.gridInst Sm) (AvailableChain.GridCO.gridConstants Sm 1) :=
  GridCO.grid_holds _

/-! Closed rows at one parameter record: `holds`, on the MATRIX line of the
closed instance term, not on the `gridInst` line. -/

theorem closedOne :
    ac43.holdsAt (GridCO.gridInst Sm) (AvailableChain.GridCO.gridConstants Sm 1) :=
  GridCO.grid_holds _

theorem closedSapc :
    strong1.holdsAt (SAPC.sapcInst AvailableChain.SAPC.Tests.p)
      (AvailableChain.SAPC.sapcConstants AvailableChain.SAPC.Tests.p 1,
        AvailableChain.SAPC.sapcStrongConstants AvailableChain.SAPC.Tests.p) :=
  SAPC.sapc_holds_strong1 _

/-- A claim outside the catalog: no MATRIX cell. -/
def nonCatalog : RefutationFamily Tests.testStrongSafe Tests.badStrong :=
  Tests.refutedBadStrong

/-! Families. -/

theorem posGrid (p : AvailableChain.GridCO.Params) :
    ac43.holdsAt (GridCO.gridInst p) (AvailableChain.GridCO.gridConstants p 1) :=
  GridCO.grid_holds p

-- An instance binder of an allowed type is the one binder.
set_option checkBinderAnnotations false in
theorem posInstBinder [q : AvailableChain.GridCO.Params] :
    ac43.holdsAt (GridCO.gridInst q) (AvailableChain.GridCO.gridConstants q 1) :=
  GridCO.grid_holds q

theorem posSA (p : AvailableChain.SA.Params) :
    core.holdsAt (SA.saInst p) (AvailableChain.SA.saConstants p 1).D_c :=
  SA.sa_holds_core p

/-- Through `toInstance`: the instance column is `sapcInst`. -/
theorem posSapc (p : AvailableChain.SAPC.Params) :
    ac43.holdsAt (SAPC.sapcInst p).toInstance (AvailableChain.SAPC.sapcConstants p 1) :=
  SAPC.sapc_holds_ac43 p

/-! The instance column looks through a parent projection only. -/

structure TwoInst where
  a : Instance
  b : Instance

def two : TwoInst := ⟨Counter.counterInst, Counter.counterInst⟩

/-- `two.a` is not a parent projection: the column is `TwoInst.a`. -/
def fieldCert : Cert safeConfirmed two.a :=
  Counter.certSafeConfirmed

end RegistrySelfTest
