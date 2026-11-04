module
public import ConsensusLean.Init
public meta import Mathlib.Tactic.Linarith

/-!
# `linarith` and `nlinarith` without the Nat preprocessing first

Mathlib's `linarith` runs its `natToInt` preprocessor on every hypothesis in the context: each `ℕ`
comparison is cast to `ℤ` (one `push_cast` per hypothesis) and every `ℕ` atom gets a nonnegativity
fact. The Goldilocks proofs carry large contexts full of `ℕ` indices and slots, while their
arithmetic is almost always over `Time = ℤ`, so that preprocessing was a quarter of all `linarith`
time (`docs/build-speed.md`).

Importing this module makes plain `linarith` and `nlinarith` (with optional extra terms, no `!`, no
`only`, no configuration) first run without `natToInt`. If that fails, the tactic framework
restores the state and tries the next elaborator of the same syntax, Mathlib's own, so the call
then runs exactly Mathlib's tactic (a failing call runs twice; its error is Mathlib's). The cheap
attempt's time and heartbeats count against the declaration's limit before fallback, so a proof
near that limit can run out of heartbeats sooner. A proof found either way is an ordinary
`linarith` certificate checked by the kernel; the optimization does not change what is provable.
Every other form of the tactic is Mathlib's, unchanged.
-/

public meta section

open Lean Meta Elab Tactic Mathlib.Tactic

namespace Consensus.Tactic.Linarith

/-- Mathlib's configuration, with the products of `nlinarith` when `nl`. -/
def fullConfig (nl : Bool) : Linarith.LinarithConfig :=
  let cfg : Linarith.LinarithConfig := {}
  if nl then { cfg with preprocessors := cfg.preprocessors.concat Linarith.nlinarithExtras }
  else cfg

/-- The same configuration without the `natToInt` preprocessor. -/
def cheapConfig (nl : Bool) : Linarith.LinarithConfig :=
  let cfg := fullConfig nl
  let keep (p : Linarith.GlobalBranchingPreprocessor) : Bool := p.name != ``Linarith.natToInt
  { cfg with preprocessors := cfg.preprocessors.filter keep }

/-- Run without `natToInt`. On failure the error propagates, and `evalTactic` falls back to the
next elaborator of the syntax, Mathlib's rule (this module's rules are newer, so tried first). -/
def run (nl : Bool) (args : List Expr) (g : MVarId) : MetaM Unit :=
  Linarith.linarith false args (cheapConfig nl) g

end Consensus.Tactic.Linarith

open Consensus.Tactic.Linarith in
elab_rules : tactic
  | `(tactic| linarith $[!%$bang]? $cfg:optConfig $[only%$o]? $[[$args,*]]?) => withMainContext do
    if bang.isSome || o.isSome || !cfg.raw[0].getArgs.isEmpty then throwUnsupportedSyntax
    let args ← ((args.map (Syntax.TSepArray.getElems)).getD {}).mapM
      (elabTermWithoutNewMVars `linarith)
    commitIfNoEx do liftMetaFinishingTactic <| run false args.toList

open Consensus.Tactic.Linarith in
elab_rules : tactic
  | `(tactic| nlinarith $[!%$bang]? $cfg:optConfig $[only%$o]? $[[$args,*]]?) => withMainContext do
    if bang.isSome || o.isSome || !cfg.raw[0].getArgs.isEmpty then throwUnsupportedSyntax
    let args ← ((args.map (Syntax.TSepArray.getElems)).getD {}).mapM
      (elabTermWithoutNewMVars `nlinarith)
    commitIfNoEx do liftMetaFinishingTactic <| run true args.toList
