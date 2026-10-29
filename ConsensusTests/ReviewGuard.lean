module
public import Lean
@[expose] public section

/-! # Review guard

The statement guard of `ConsensusTests/ReviewAxioms.lean`, shared with its negative fixtures
(`scripts/fixtures/Review*.lean`) so that they run the same code: a review statement must be *the* type of its source theorem up to the names of
bound variables. `Expr` `==` (`Expr.eqv`) is alpha-equality but ignores binder annotations, so the
guard also compares the binder kinds (`{}`, `()`, `[]`, `⦃⦄`) of the two terms, binder for binder;
`Expr.equal` would also compare binder names (too strict). `checkComplete` requires a pair for
every statement of a namespace. -/

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

/-- Throws unless every non-internal constant in namespace `ns` that is not a proof (its type is
not a proposition: the review statements are `Prop` definitions, their proofs are theorems) is the
statement of some pair, so a statement cannot be added to, or a pair dropped from, the pinned list
unnoticed. Proofs are recognised by their type, not their declaration kind, which the module
system may change for imported theorems. -/
meta def checkComplete (ns : Name) (pairs : List (Name × Name)) : MetaM Unit := do
  let members := (← getEnv).constants.fold (init := #[]) fun acc c info =>
    if ns.isPrefixOf c && !c.isInternalDetail && !pairs.any (·.1 == c) then acc.push (c, info.type)
    else acc
  let mut missing := #[]
  for (c, ty) in members do
    unless ← isProp ty do missing := missing.push c
  unless missing.isEmpty do
    throwError "no review pair for {missing.qsort Name.lt}"

end Consensus.ReviewGuard
