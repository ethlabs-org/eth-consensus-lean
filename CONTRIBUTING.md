# Contributing

How to add statements, proofs and instances. The working rules for agents (worktrees, jobs, PRs, reviews)
are in `AGENTS.md` and apply to everyone. The layout and its import rules are in README "Layout" and
`scripts/boundaries.toml`; what is trusted is in `TRUST.md`. The rules below come from the adopted foundation
plan (design record: `docs/decisions.md`); section numbers (§) refer to it.

## Statements (plan §4)

A milestone statement is a `Prop` in `ConsensusLean/Statements/<M>.lean` (generic) or
`ConsensusLean/Instances/<P>/Statements/<M>.lean` (instance, with one bundled parameter structure). It imports
only Core, Spec and generic Statements (an instance's also its own Spec and, once it exists,
`Refinement/Defs`; `scripts/boundaries.toml` is authoritative), so nothing proof-side changes how it
elaborates. Write it at full strength: never a weaker version to be strengthened later.

Each statement comes with:

1. **A mapping entry** in `docs/<P>-mapping.md` (for Goldilocks: `docs/goldilocks-mapping.md`): reference →
   definition → milestone → Lean name, plus what the model leaves out. Write every Lean name fully qualified and
   list it in `ConsensusLeanTest/Index.lean` (``` example := ``Name ```): check.sh step 12 checks every
   `Consensus.`-prefixed token of the file, prose or code, so a rename fails the build. Only declarations can be
   cited this way: name a namespace without the prefix (the `Shape` namespace).
2. **A fidelity read-back** (before the statement lands): the Lean read back into prose (a subagent that did not write the
   statement does this well) and compared with the reference. Check quantifier order, strict versus non-strict bounds, and empty inputs
   (no validators, empty windows, zero thresholds).
3. **Witnesses** in `ConsensusLeanTest/`, each labelled by kind: (a) the hypotheses are jointly satisfiable;
   (b) an existential reachability example (e.g. one finalizing run with an admissible adversary); (c) only
   when a threshold is claimed to be necessary, a counterexample just beyond it. One witness does not show
   progress against every adversary.
4. **For the first slice of an instance, one finite model** that states every bound (validators, slots,
   messages, history, scheduler) and what is checked (bounded safety, reachability or bounded liveness), checked
   by exhaustive `decide`. Random testing (Plausible) is not a model check.

Statements land as labelled trusted-surface commits (a `Trusted-surface:` line; `AGENTS.md`, "Trusted surface"),
recorded on #129, before proofs start. A commit that changes a statement and its proof together says so.

## Proofs (plan §4, §5)

- A milestone's proofs live in `ConsensusLean/Proofs/<M>/` (or `Instances/<P>/Proofs/<M>/`) and end in
  `Main.lean`, which proves the statement. Files import downward and siblings of the same milestone; a helper
  two files share moves to `Lemmas/`.
- If milestone M needs N, M's `Main` proves `Stmt_N → Stmt_M` and imports `Statements.N`, not N's proofs.
  The top-level `Main` (or `Instances/<P>/Main`) composes the milestones. Chains inside a milestone are fine.
- `sorry` only under `Lemmas/` and `Proofs/`; never an axiom. A milestone joins `Main` and `Solution` only
  when its closure is free of `sorry` (check.sh step 3b).
- Files stay under 1,500 lines (Mathlib's soft bound, `linter.style.longFile`); an exception is a
  `set_option linter.style.longFile N` with a comment giving the reason.
- Heartbeats: the defaults. Profile before raising them; a raise is a scoped `set_option maxHeartbeats N in`
  with a comment.
- Once a proof works, make it short: `simp only [...]` for intermediate steps, plain `simp` only to close a
  goal; no `unfold`/`change` through another module's definition (use its characterising lemmas, `AGENTS.md`
  "Visibility").

## Style (plan §7, §8)

- **Naming and docstrings:** Mathlib's conventions: theorems in `snake_case`, named after their conclusion;
  types and `Prop`s in `UpperCamelCase`; other terms in `lowerCamelCase`. Every file starts with a module docstring
  (`/-! # Title … -/`). Every definition and statement in Spec and Statements has a docstring that says what it
  means, not how it is proved.
- **Attributes:** global attributes (`@[simp]`, `instance`, `@[ext]`, priorities) live in Spec, Lemmas or
  ToMathlib. Proof files use `local`/`scoped` attributes or `simp [h]`. `attribute [simp] x in` is global: do
  not use it in proof files.
- **Typeclass assumptions:** minimal, on each declaration; no blanket section `variable`s that every declaration
  inherits.
- **Generic proofs never unfold instance definitions**; the import matrix makes this structural.
- **`ToMathlib/`** holds general lemmas staged for upstreaming; files there import only Mathlib.
- **Deprecations:** a renamed public declaration keeps a `@[deprecated (since := "YYYY-MM-DD")]` alias; old
  aliases are removed periodically.

## Upgrades (plan §9)

One upgrade owner, claude-ethlabs, runs toolchain and Mathlib bumps: `lean-toolchain`, the Mathlib `rev` in
`lakefile.toml`, `lake-manifest.json`, `scripts/pins.toml` and the table in `TRUST.md`, in one PR. The toolchain
and manifest are on the trusted surface, so a bump's commits carry a `Trusted-surface:` line. A bump runs the full
tier on the box before merge (cold build, rebuild canary, replay, `lake check`, paranoid comparator): ask the
box watcher owner for an exact-commit run and verify its result on #63. GitHub Actions is disabled; do not
dispatch `full.yml` or create a GitHub CI subscription (README "Verification").

## License

Apache-2.0 (`LICENSE`), as the Verified-zkEVM Lean libraries (ArkLib, CompPoly, VCVio) and Mathlib, CSLib, FLT
and Carleson. Vendored copies keep their own licences (`scripts/LICENSE.EthLib`, `scripts/LICENSE.axiom-audit`).
