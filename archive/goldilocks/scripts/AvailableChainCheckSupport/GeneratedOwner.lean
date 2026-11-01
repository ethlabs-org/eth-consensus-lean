module
public import Lean -- shake: keep (re-export)

@[expose] public section

/-! The owner of a generated constant, for the check scripts
(`scripts/CheckFGSARunAxioms.lean`, `scripts/CheckFGSALease.lean`,
`scripts/CheckFGSARunLease.lean`).

Lean realizes a generated constant (an equation, a matcher splitter or
congruence equation, a sparse `casesOn` and its fallback equation) in the first
module that needs it, possibly as a private copy, for example the matcher
equation `_private.M.0.X.match_1.eq_2`. So the module of a generated constant
does not tell where its definition is; its owner does. The rule has no list of
names.

This library imports only `Lean`. No protocol library may import it
(`scripts/check-fgsa.sh`). -/

namespace AvailableChainCheckSupport

open Lean

/-- A last name component that Lean generates for a definition: an equation
(`eq_<k>`, `eq_def`), a matcher splitter or congruence equation (`splitter`,
`congr_eq_<k>`), or a sparse `casesOn` and its fallback equation
(`_sparseCasesOn_<k>`, `else_eq`). -/
def generatedSuffix (s : String) : Bool :=
  let numbered (pre : String) :=
    s.startsWith pre && !(s.drop pre.length).isEmpty && (s.drop pre.length).all Char.isDigit
  s == "eq_def" || s == "splitter" || s == "else_eq" || numbered "eq_" ||
    numbered "congr_eq_" || numbered "_sparseCasesOn_"

/-- The declared constant `n`, or the declared constant of the user name of
the private name `n`. -/
def declaredName (env : Environment) (n : Name) : Option Name :=
  if env.contains n then some n else
    match privateToUserName? n with
    | some u => if env.contains u then some u else none
    | none => none

/-- The owner of a generated constant: strip one generated last component at a
time (`generatedSuffix`) until the name is a declared constant (directly, or
through the user name of a private name). `none` if the last component of `n`
is not generated, or if no owner is found. -/
def generatedOwner (env : Environment) : Name → Option Name
  | .str pre s =>
      if generatedSuffix s then
        match declaredName env pre with
        | some o => some o
        | none => generatedOwner env pre
      else none
  | _ => none

/-- The owner of a generated constant is a definition. -/
def ownerIsDefn (env : Environment) (o : Name) : Bool :=
  env.find? o matches some (.defnInfo _)

/-- The owner of `n` if `n` is a generated constant of a definition outside
the scope `inScope` (a module test on the owner). A check skips such a
constant as a checked constant: it states the body of its owner, which is not
a declaration of the checked library. -/
def generatedOfOther (env : Environment) (inScope : Name → Bool) (n : Name) : Option Name :=
  match generatedOwner env n with
  | some o => if ownerIsDefn env o && !inScope o then some o else none
  | none => none

end AvailableChainCheckSupport

end
