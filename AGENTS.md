# Agents

Rules for AI agents and humans changing this repository. `CLAUDE.md` is a symlink to this file.

Read first: `README.md` (the review statement), `TRUST.md` (what is trusted and what each check
does), `CONTRIBUTING.md` (how to write statements and proofs, style), `docs/roadmap.md` (milestones and their
status) and `docs/decisions.md` (the design rationale). Checks and CI tiers: `docs/checks.md`.

## Working on this repository

- **One task per branch and worktree.** Work on a `work/<task>` branch in your own worktree. No
  `git checkout <path>`, `git restore`, `git stash` or `git reset` that discards or hides work: commit first.
- **Iterate locally:** `lake env lean <file>` for one file (its imports built), or
  `turbo-lean check <file> --decl <name>` for a single declaration only. `lake build` stays the gate.
  `lake build` builds only `ConsensusLean` by default; `lake test` builds `ConsensusLeanTest`
  (the lakefile's `testDriver`, not a default target).
  A single-module build does **not** check downstream callers after an interface change: use
  `scripts/check-changed.sh` for that. Concurrent Lake invocations sharing one output directory are not
  established safe; do not do that.
- **Generated roots:** `ConsensusLean.lean` and `ConsensusLeanTest.lean` import every module of
  their library. Regenerate with `lake exe mk_all --lib ConsensusLean --module` and
  `lake exe mk_all --lib ConsensusLeanTest --module`; `check-boundaries.py` fails on an unlisted file.
- **Import boundaries:** the layer matrix in `scripts/boundaries.toml` (`docs/layout.md`); check it in about
  2 s, no build: `python3 -I scripts/check-boundaries.py`. A needed deviation is a reviewed `[[exception]]`.
- **Before committing:** `RUN_DIR="$(mktemp -d)" scripts/check-changed.sh [<base>]`. It builds the downstream
  cone of the changed modules and runs the fast checks restricted to what changed; read its `SKIP` lines to see
  what it did not check. A change to `scripts/` or the build configuration runs the whole fast mode with the
  self-tests. `scripts/check.sh` refuses to start without `RUN_DIR` (a scratch directory) or `CI`.
- **Land on main** with `scripts/push-main.sh`, never a bare `git push` to `main`: after rebasing on
  `origin/main` and committing everything, it runs `scripts/check.sh --changed origin/main` (the change's cone;
  the whole fast mode with self-tests for a `scripts/` change), `scripts/review-boundary.sh` and
  `scripts/check-commit-emails.py`, and pushes a fast-forward only if all pass. If `main` moves during the
  check it takes the landing lock (the remote branch `push-main-lock`), rebases and checks again. The pre-push
  hook `scripts/hooks/pre-push` refuses a push to `main` of a commit the script did not check; enable it once
  per clone with `git config core.hooksPath scripts/hooks`. A red `main` is reverted at once by whoever pushed
  it, then fixed. A pull request is the alternative for contributors who cannot run the checks
  (`CONTRIBUTING.md`).
- **CI** is GitHub Actions: `.github/workflows/ci.yml` (`check`) runs the fast tier and the review boundary on
  every pull request and every push to `main`; `full.yml` (`full`) runs the full tier (kernel replay,
  `lake check`, `lake comparator --paranoid`, the rebuild canary) nightly, on `milestone*`/`release*` tags and on
  demand (`gh workflow run full.yml --ref <ref>`; run it for milestones and toolchain or Mathlib bumps). Green
  CI means the GitHub check of the commit: `check` for a pull request or a main head, `full` for full
  certification.
- **Commit messages** state the reason if the change makes build or CI time worse, and name the declarations
  added or changed, their assumptions, every open `sorry`, and the commands actually run with their result.
  Never claim a check you did not run. Two requirements are checked: a `Trusted-surface:` line in every
  non-merge commit that touches the trusted surface (below), and author, committer and `Co-authored-by:`
  addresses on the public allowlist `scripts/commit-emails.toml` (`scripts/check-commit-emails.py`, in `check` and push-main).
- **Trusted surface** (`ConsensusLean/{Init,Core,Spec,Statements,ToMathlib}` as `X.lean` and `X/**`,
  `Challenge.lean`, `comparator.json`, `lean-toolchain`, `lake-manifest.json`,
  `ConsensusLeanTest/Review{Axioms,Guard}.lean`, and for every protocol instance `<P>` the files
  `Instances/<P>/{Spec,Statements}` and `Instances/<P>/AsChainShape.lean`): the list is `trusted_paths` in
  `scripts/boundaries.toml` (united with the list at the base). A change to it is **recorded, not gated**: every
  non-merge commit that touches a trusted path carries a line `Trusted-surface: <what changes and why>` in its
  message; `scripts/review-boundary.sh` fails without it and records each commit's trusted paths in the summary of its
  `check` run. A statement change gets a fidelity read-back before landing (the Lean read back into prose and
  compared with the reference), recorded as a line `Fidelity read-back: PASS` in its commit message; the
  snapshots (step 4) are regenerated and committed.
- **Check infrastructure** (`scripts/**`, `.github/**`, the lakefile) is not on the trusted surface: a change to
  what a trust check checks comes with fixtures that show the new verdicts; a pure speedup shows that every
  check's verdict is unchanged (the same pass/fail on the fixtures; `TRUST.md`).
- **Visibility:** no `@[expose]` in `Lemmas/`, `Proofs/`, `Main` or `ToMathlib/` (check-boundaries.py
  fails on it): public theorems, private helpers, and no exported bodies, so a proof edit or the body edit of a
  `Prop`-valued or noncomputable definition leaves the public `.olean` unchanged and rebuilds no importer (a
  computable definition still exports its compiled code: a body edit that changes the code rebuilds importers). A
  definition another module reasons about gets characterising lemmas next to it (`foo_iff`, `foo_eq`, field
  `@[simp]` lemmas; proved `by rfl` or `Iff.rfl`, since a `:= rfl` term needs an exposed body; such lemmas are not
  `dsimp` lemmas, which is the price, not a reason to expose), and users `rw`/`simp only` with them instead of
  `unfold`/`change` through the body. Use them in the defining file too: `simp [foo]` or `unfold foo` there stores
  `foo.eq_1`, whose statement is the body, in the public `.olean`. `abbrev` and instances of non-`Prop`
  classes export their bodies anyway (not checked): use them for notation-like definitions only.
- **Where a new lemma goes:** a new public declaration changes its module's interface and rebuilds every
  importer. Put a helper that only a new file needs into that file (or into a new module importing what it
  needs), not into a widely imported module: of 40 replayed main commits, the 4 that added a helper to
  `AC/Steps/Nodes`, `AC/Steps/Core` or `Compose/Sleepy/Served` rebuilt 136–164 modules each (3 min on 4
  cores), 62% of the rebuild time of all 40; the median commit rebuilt in 9 s (`docs/notes/build-speed.md`).
  If the helper needs a hub's private lemmas, move those lemmas to the hub's internal module instead
  of adding the helper to the hub.
- **Unfinished proofs:** `sorry` only under `Lemmas/` and `Proofs/` (the `sorry = true` layers of
  `scripts/boundaries.toml`), never in Spec, Statements, Main, instances, tests or `Solution`, and never an axiom.
  `lake build --wfail` ignores it (`warn.sorry = false`) but fails on every other warning. The closure of
  `Solution` (today `Main` and the obligations endpoint), of each `proved_milestone_modules` entry (the other
  finished milestones) and of every test must be free of it, also through imports (check.sh step 3b); a new
  milestone stays out of `Main`/`Solution`/`proved_milestone_modules` until it is finished. Tests are named theorems, not
  proof `example`s (step 7: an example never enters the environment, so no check sees its proof; the name index's
  ``` example := ``Name ``` lines carry no proof and are exempt). Step 3b's
  report lists what is unfinished.
- **Spec snapshot:** a Spec change fails step 4 until `scripts/spec-snapshot.txt` is regenerated
  (`scripts/check.sh --update-snapshot`, which then fails on purpose) and the diff is committed for review. So
  does a change of an instance Spec/Statements module or another module of the protected surface (TRUST.md), with
  `scripts/instance-spec-snapshot.txt`.
- **Cited names:** every `Consensus.`-prefixed token in `docs/roadmap.md` and `docs/goldilocks-mapping.md`
  (`doc_name_files` in `scripts/boundaries.toml`) is a fully qualified declaration name listed in
  `ConsensusLeanTest/Index.lean` (``` example := ``Name ```), whose build checks that it exists (check.sh step 12).
  Renaming a cited declaration means updating the docs and the index; no `@[deprecated]` alias (nothing outside
  the repository uses these names, and `--wfail` makes any use of one an error).
- **No internal provenance** in files or commit messages: no person names, dated decision history, issue
  numbers or links to private repositories. State the current rule or modelling choice and its reason; cite the
  spec (`specs/goldilocks/tex/…`) or `docs/decisions.md` by section.

## Statements first, then proofs

- **Two phases.** Milestone statements are written at full strength and read back before proofs start. Never
  weaken a statement to make it provable and never drop a rejection test. A proof change does not edit
  statements, except a correction landed as a labelled trusted-surface commit (above; `CONTRIBUTING.md`
  "Statements").
- **A statement you believe is false:** report it with a counterexample (a named theorem proving the negation,
  or a concrete instance) and stop; do not change the statement.
- **Search before adding a lemma** (Mathlib, `Lemmas/`, `ToMathlib/`, `exact?`): duplicates cost review.
- **Task size:** one cohesive change per commit (one milestone file, one lemma area).
- **Names** describe the mathematics: no provenance (issue number, `_v2`, `_new`) in declaration names.
- Once a proof works, make it compact and robust (`CONTRIBUTING.md` "Proofs").
