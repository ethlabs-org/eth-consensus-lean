module
public import Lean
@[expose] public section

/-! # Review guard

The statement guard of `ConsensusTests/ReviewAxioms.lean`, shared with its negative fixtures
(`scripts/fixtures/Review*.lean`) so that they run the same code: a review statement must be
*the* type of its source theorem up to the names of bound variables. `Expr` `==` (`Expr.eqv`) is
alpha-equality but ignores binder annotations, so the guard also compares the binder kinds (`{}`,
`()`, `[]`, `⦃⦄`) of the two terms, binder for binder; `Expr.equal` would also compare binder
names (too strict). `checkComplete` requires a pair for every statement of a module, whatever its
namespace or name. -/

open Lean Meta

namespace Consensus.ReviewGuard

/-- The binder kinds of all binders (`∀`, `fun`) of `e`, in pre-order. -/
meta def binderInfos : Expr → Array BinderInfo → Array BinderInfo
  | .forallE _ d b i, acc => binderInfos b (binderInfos d (acc.push i))
  | .lam _ d b i, acc => binderInfos b (binderInfos d (acc.push i))
  | .letE _ t v b _, acc => binderInfos b (binderInfos v (binderInfos t acc))
  | .app f a, acc => binderInfos a (binderInfos f acc)
  | .mdata _ e, acc => binderInfos e acc
  | .proj _ _ e, acc => binderInfos e acc
  | _, acc => acc

/-- Throws unless, for each pair `(s, t)`, the body of the definition `s` is alpha-equal to the
type of the theorem `t` with the same binder kinds. -/
meta def check (pairs : List (Name × Name)) : MetaM Unit := do
  for (s, t) in pairs do
    let some v := (← getConstInfo s).value? | throwError "{s} is not a definition"
    let ty := (← getConstInfo t).type
    unless v == ty do
      throwError "{s} is not alpha-equal to the type of {t}"
    unless binderInfos v #[] == binderInfos ty #[] do
      throwError "{s} does not have the binder kinds of the type of {t}"

/-- Throws unless every constant declared in module `mod` (the current file if `mod` is its main
module) that is neither a proof nor a matcher is the statement of some pair, so a statement
cannot be added to, or a pair dropped from, the pinned list unnoticed. Membership is by owning
module, not by namespace or name: a statement in another namespace, with an internal-looking name
(`_x`, `eq_1`) or `private` (the caller must `import all` the module to see it) is listed too.
Proofs (theorems, generated equation lemmas) are recognised by their type being a proposition,
not by their declaration kind, which the module system may change for imported theorems; review
statements are `Prop` definitions, whose type `Prop` is not a proposition. Matchers (`match_<n>`,
generated for definitions by pattern matching) are the only generated non-proof constants
exempted; any other constant of the module needs a pair, so the module holds only statements. -/
meta def checkComplete (mod : Name) (pairs : List (Name × Name)) : MetaM Unit := do
  let env ← getEnv
  let idx? ← if mod == env.mainModule then pure none else
    match env.getModuleIdx? mod with
    | some i => pure (some i)
    | none => throwError "module {mod} is not imported"
  let members := env.constants.fold (init := #[]) fun acc c info =>
    if env.getModuleIdxFor? c == idx? && !isMatcherCore env c && !pairs.any (·.1 == c) then
      acc.push (c, info.type)
    else acc
  let mut missing := #[]
  for (c, ty) in members do
    unless ← isProp ty do missing := missing.push c
  unless missing.isEmpty do
    let names := (missing.qsort Name.lt).toList.map toString
    throwError "no review pair for [{", ".intercalate names}]"

end Consensus.ReviewGuard
