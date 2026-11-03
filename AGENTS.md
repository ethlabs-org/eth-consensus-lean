# Agents

Rules for AI agents (and humans) working on this repo. `CLAUDE.md` is a symlink to this file.

Read first: README "What this is" (the review statement), `TRUST.md` (what is trusted and what each check
does), `CONTRIBUTING.md` (how to write statements and proofs, style), `docs/roadmap.md` (milestones and
their status). Coordination (claiming issues, branches, PRs, reviews): GitHub issue #2; pointers and
decisions: #17. Design decisions: `docs/decisions.md`. Checks and CI tiers: README "Verification".

## Working on this repo

- **Worktree per task.** Work on `work/<agent>/<task>` in your own worktree; never in a tree another
  agent uses. On the shared box, seed a fresh worktree (no `.lake` yet) from a quiescent warm checkout:
  `python3 -I scripts/worktree-setup.py <warm-source> <wt>` (run the script from a checkout that has it).
  The toolchain, manifest and Lake configuration must match. This reuses packages **and project build
  artifacts**: hard-links only the Lean outputs Lake v4.35 unlinks before rebuilding; copies mutable
  traces, hashes, setup files, native outputs, package sources and Git metadata. Do not use `cp -al`
  on an entire writable `.lake`: Lake overwrites some bookkeeping in place. Never seed from a live
  watcher/build tree, edit shared outputs in place, or run `lake clean`/cache maintenance on the source
  during setup. Do not edit linked artifacts manually; use Lake to rebuild. Re-audit the helper on a
  Lean upgrade. No `lake exe cache get` on the box; normal builds use `LAKE_RESTORE_ARTIFACTS=true`.
  Warm seeding is not a guaranteed setup speedup (measurements: `docs/box-capacity.md`).
  No `git checkout <path>`, `git restore`, `git stash` or `git reset` that discards or hides work (plan §7):
  commit first, or ask.
- **Every build in a job** (shared memory pool; OOM kills hit everyone):
  from your worktree, agent builds and checks use
  `scripts/agent-job.py <unique-name> -- bash -lc 'LAKE_RESTORE_ARTIFACTS=true <cmd>'`.
  It waits through the per-user FIFO (two agent slots), delegates to `job --mem 16G --cpus 8
  consensus-lean`, and returns the job's exit status. Landings and CI stay on `job`, outside this queue.
  One build at a time per agent; reviewers never build.
- **Iterate locally:** `lake env lean <file>` for one file (its imports built), or
  `turbo-lean check <file> --decl <name>` for a single declaration only. `lake build` stays the gate.
  `lake build` builds only `ConsensusLean` by default; `lake test` builds `ConsensusLeanTest`
  (the lakefile's `testDriver`, not a default target).
  A single-module build does **not** check downstream callers after an interface change: use
  `scripts/check-changed.sh` for that. Budget 16G/8 CPU per build; at most two concurrent agent builds
  across the box while reserving another 16G/8 CPU for CI. Check `jobs-all` and available memory first;
  do not infer spare capacity from warm cgroup accounting of shared pages. Concurrent Lake invocations
  sharing one output directory are not established safe; do not do that. One build per agent still
  applies. Measurements behind these numbers: `docs/box-capacity.md`.
- **Generated roots:** `ConsensusLean.lean` and `ConsensusLeanTest.lean` import every module of
  their library. Regenerate with `lake exe mk_all --lib ConsensusLean --module` and
  `lake exe mk_all --lib ConsensusLeanTest --module`; `check-boundaries.py` fails on an unlisted file.
- **Import boundaries:** the layer matrix in `scripts/boundaries.toml` (README "Layout"); check it in about
  2 s, no build: `python3 -I scripts/check-boundaries.py`. A needed deviation is a reviewed `[[exception]]`.
- **Before committing:** `scripts/check-changed.sh` (in a job). It builds the downstream cone of the
  changed modules and runs the fast checks restricted to what changed; read its `SKIP` lines to see
  what it did not check. A change to `scripts/` or the build configuration runs the whole fast mode.
- **Land on main (trunk-based, owner 2026-10-30, #2)** with `scripts/push-main.sh`, never a bare `git push` to
  `main`: after rebasing on `origin/main` and committing everything, it runs `scripts/check.sh --changed
  origin/main` (the change's cone; the whole fast mode with self-tests for a `scripts/` change) and
  `scripts/review-boundary.sh`, and pushes only if both pass, printing the check's result line. If main moves during the check, it takes the landing
  lock (the remote branch `push-main-lock`), rebases and checks again; other landers wait for the lock instead of
  checking in vain (#50). Never create or delete that branch by hand except to clear a dead lock (it also expires). The pre-push hook
  `scripts/hooks/pre-push` refuses a push to `main` of a commit the script did not check; enable it once per clone
  with `git config core.hooksPath scripts/hooks` (`.agents/setup` does it in orbs). No PR; observed main heads run
  the selected box CI tier; a red `main` is reverted at once by whoever
  pushed it, then fixed. **GitHub Actions is disabled by owner decision (2026-10-31, #50)** because billing
  prevents jobs from starting; workflow files remain for reference and reversible re-enablement. Do not create
  GitHub CI subscriptions, dispatch Actions, or report the known billing failures. **Green CI means the box
  result on [#63](https://github.com/ethlabs-org/consensus-lean/issues/63)**, not a GitHub check badge.
  `scripts/orb-ci.sh` runs as systemd user services on `ethlabs-box`, with checks inside `job`: fast tier and
  review-boundary for observed main/non-draft PR heads, docs-only `--changed`, and full tier nightly, on tags
  and manually (kernel replay, `lake check`, `lake comparator --paranoid`). Polling can coalesce intermediate
  heads: ask the box watcher owner to queue an exact SHA when its row is missing. Failures go to #17 or the PR.
  Request full checks for milestones and toolchain/Mathlib bumps from the box watcher owner; see README
  "Verification" for manual commands. A PR is optional (for collaborators who cannot run the checks:
  `CONTRIBUTING.md` "Working together"), also for a trusted-surface change (below). The commit message (or PR body) ends with a cost line
  (`Cost: <agent-h> agent-h, <models>, <CPU-h> CPU-h`) and states the reason if the change makes build or CI
  time worse. An agent's commit also names the model in a trailer after the cost line,
  `Model: <provider/model>` (one line per model that did material work, e.g. `Model: openai/gpt-6-astra`).
  The agent itself is named by the harness's own trailers: Amp adds `Amp-Thread-ID` and, when a person is
  the author, `Co-authored-by: Amp <amp@ampcode.com>` (do not write these by hand; Amp refuses the commit);
  another harness adds its own co-author trailer, or the agent writes it.
- **Trusted surface** (`ConsensusLean/{Init,Core,Spec,Statements,ToMathlib}` as `X.lean` and `X/**`,
  `Challenge.lean`, `comparator.json`, `lean-toolchain`, `lake-manifest.json`,
  `ConsensusLeanTest/Review{Axioms,Guard}.lean`, and since #38 the instance files
  `Instances/<P>/{Spec,Statements}` and `Instances/<P>/Refinement/Defs.lean`, and `Lemmas/Problem/Derived.lean`): the list is `trusted_paths` in `scripts/boundaries.toml`,
  (united with the list at the base). Such a change is **recorded, not gated** (owner, 2026-11-01: the
  `spec-approved` tag is retired while the work is active): it lands through `scripts/push-main.sh` like any
  other change; every commit that touches a trusted path carries a line `Trusted-surface: <what changes and
  why>` in its message (`scripts/review-boundary.sh` fails without it), and push-main comments the landing on
  [#129](https://github.com/ethlabs-org/consensus-lean/issues/129). For a statement change, do a fidelity
  read-back (a subagent, in your own session) before landing and say so in the commit; the spec snapshot
  (step 4) still has to be regenerated and committed. Nothing waits for anyone.
- **Check infrastructure** (`scripts/**`, `.github/**`, the lakefile) is not on the trusted surface; its author is
  responsible for it: a change to what a trust check checks comes with fixtures that show the new verdicts and a
  pointer on #17; a pure speedup shows that every check's verdict is unchanged (same pass/fail on the
  fixtures) (`TRUST.md`).
- **Visibility (plan §3):** no `@[expose]` in `Lemmas/`, `Proofs/`, `Main` or `ToMathlib/` (check-boundaries.py
  fails on it): public theorems, private helpers, and no exported bodies, so a proof edit or the body edit of a
  `Prop`-valued or noncomputable definition leaves the public `.olean` unchanged and rebuilds no importer (a
  computable definition still exports its compiled code: a body edit that changes the code rebuilds importers). A
  definition another module reasons about gets characterising lemmas next to it (`foo_iff`, `foo_eq`, field
  `@[simp]` lemmas; proved `by rfl` or `Iff.rfl`, since a `:= rfl` term needs an exposed body; such lemmas are not
  `dsimp` lemmas, which is the price, not a reason to expose), and users `rw`/`simp only` with them instead of
  `unfold`/`change` through the body. Use them in the defining file too: `simp [foo]` or `unfold foo` there stores
  `foo.eq_1`, whose statement is the body, in the public `.olean`. `abbrev` and instances of non-`Prop`
  classes export their bodies anyway (not checked): use them for notation-like definitions only.
- **Unfinished proofs:** `sorry` only under `Lemmas/` and `Proofs/` (the `sorry = true` layers of
  `scripts/boundaries.toml`), never in Spec, Statements, Main, instances, tests or `Solution`, and never an axiom.
  `lake build --wfail` ignores it (`warn.sorry = false`) but fails on every other warning. The closure of
  `Solution` (today `Main` and every milestone) and every test must be free of it, also through imports (check.sh
  step 3b); a new milestone stays out of `Main`/`Solution` until it is finished. Tests are named theorems, not
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

## Statements first, then proofs

- **Two phases** (plan §4, §7). Milestone statements are written at full strength and read back before proofs
  start. Never weaken a statement to make it provable and never drop a rejection test. A proof change does not
  edit statements, except a correction landed as a labelled trusted-surface commit (above; `CONTRIBUTING.md`
  "Statements").
- **A statement you believe is false:** open an issue with a counterexample (a named theorem proving the
  negation, or a concrete instance) and stop; do not change the statement.
- **A lemma you need from another agent's area** becomes a `sorry` lemma in your own file (under `Lemmas/` or
  `Proofs/` only), listed in your handoff; whoever merges deduplicates it or moves it to `Lemmas/`.
- **Search before adding a lemma** (Mathlib, `Lemmas/`, `ToMathlib/`, `exact?`): duplicates cost review.
- **Task size:** one cohesive change per commit (one milestone file, one lemma area).

## Reviews and handoffs

- **Nothing blocks on the owner, and there are no review gates between agents** (owner, #2, 2026-10-30). He
  gives input and asks questions; agents own every decision and record it where the work is (PR body, issue).
  There is no approval step. The author owns the change. A subagent pass (the fidelity read-back of a statement
  change, a skeptical read of a tricky trust-check change) is a tool used inside the author's own
  session, not a waiting step.
- **Handoffs, commit messages and PR bodies** name the declarations added or changed, their assumptions, every open `sorry`, and
  the commands actually run with their result. Never claim a check you did not run.
- **Names** describe the mathematics: no provenance (agent, issue number, `_v2`, `_new`) in declaration names.
- Once a proof works, make it compact and robust (`CONTRIBUTING.md` "Proofs").
