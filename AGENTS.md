# Agents

Rules for AI agents (and humans) working on this repo. `CLAUDE.md` is a symlink to this file.

Read first: README "What this is" (the review statement), `TRUST.md` (what is trusted and what each check
does), `CONTRIBUTING.md` (how to write statements and proofs, style), `docs/roadmap.md` (milestones and
their status). Coordination (claiming issues, branches, PRs, reviews): GitHub issue #2; pointers and
decisions: #17. Design decisions: `docs/decisions.md`. Checks and CI tiers: README "Verification".

## Working on this repo

- **Worktree per task.** Work on `work/<agent>/<task>` in your own worktree; never in a tree another
  agent uses. On the shared box, hard-link the packages instead of fetching them:
  `mkdir -p <wt>/.lake && cp -al <main>/.lake/packages <wt>/.lake/packages`.
  No `git checkout <path>`, `git restore`, `git stash` or `git reset` that discards or hides work (plan §7):
  commit first, or ask.
- **Every build in a job** (shared memory pool; OOM kills hit everyone):
  `job --mem 16G --cpus 8 consensus-lean <unique-name> -- bash -lc "cd <worktree> && LAKE_RESTORE_ARTIFACTS=true <cmd>"`,
  then wait for it (`/srv/status/<user>.<unit>.json`, `journalctl --user -u <unit>`). One build at a time;
  reviewers never build.
- **Iterate locally:** `lake env lean <file>` for one file (its imports built), or
  `turbo-lean check <file> --decl <name>` for a single declaration only. `lake build` stays the gate.
  `lake build` builds only `ConsensusLean` by default; `lake test` builds `ConsensusLeanTest`
  (the lakefile's `testDriver`, not a default target).
- **Generated roots:** `ConsensusLean.lean` and `ConsensusLeanTest.lean` import every module of
  their library. Regenerate with `lake exe mk_all --lib ConsensusLean --module` and
  `lake exe mk_all --lib ConsensusLeanTest --module`; `check-boundaries.py` fails on an unlisted file.
- **Import boundaries:** the layer matrix in `scripts/boundaries.toml` (README "Layout"); check it in about
  2 s, no build: `python3 -I scripts/check-boundaries.py`. A needed deviation is a reviewed `[[exception]]`.
- **Before committing:** `scripts/check-changed.sh` (in a job). It builds the downstream cone of the
  changed modules and runs the fast checks restricted to what changed; read its `SKIP` lines to see
  what it did not check. A change to `scripts/` or the build configuration runs the whole fast mode.
- **Open a PR when ready.** Pushes to `work/*` without a PR run no CI. A PR runs the fast tier
  (`scripts/check.sh --fast`, about 10–13 minutes; 17 with self-tests; a docs-only PR runs `--changed`);
  kernel replay, `lake check` and `lake comparator --paranoid` run nightly (`full.yml`) or on demand
  (`gh workflow run full.yml --ref <branch>`). CI must be green to merge. The PR body ends with a cost line
  (`Cost: <agent-h> agent-h, <models>, <CPU-h> CPU-h`) and states the reason if the change makes build, CI
  or review time worse.
- **Trusted surface** (`ConsensusLean/{Init,Core,Spec,Statements,ToMathlib}` as `X.lean` and `X/**`,
  `Challenge.lean`, `comparator.json`, `lean-toolchain`, `lake-manifest.json`,
  `ConsensusLeanTest/Review{Axioms,Guard}.lean`): the list is `trusted_paths` in `scripts/boundaries.toml`,
  and CI also checks the list at the tag. CI's `review-boundary` fails until the `spec-approved` tag covers
  the change. Say in the PR that it needs approval; only the owner, or an agent he explicitly authorizes
  (never the PR's author on its own), moves the tag.
- **Check infrastructure** (`scripts/**`, `.github/**`, the lakefile) is reviewed by agents, not through the
  tag (Code Owner review is not enforced): a change to what a trust check checks needs two independent
  reviews linked in its PR and a pointer on #17, other changes one; a pure speedup also shows that every check's
  verdict is unchanged (same pass/fail on the fixtures) (`TRUST.md`, issue #21).
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
  proof `example`s (step 7: an example never enters the environment, so no check sees its proof). Step 3b's
  report lists what is unfinished.
- **Spec snapshot:** a Spec change fails step 4 until `scripts/spec-snapshot.txt` is regenerated
  (`scripts/check.sh --update-snapshot`, which then fails on purpose) and the diff is committed for review.
- **Cited names:** every `Consensus.`-prefixed token in `docs/roadmap.md` and `docs/goldilocks-mapping.md`
  (`doc_name_files` in `scripts/boundaries.toml`) is a fully qualified declaration name listed in
  `ConsensusLeanTest/Index.lean` (``` example := ``Name ```), whose build checks that it exists (check.sh step 12).
  Renaming a cited declaration means updating the docs and the index and adding a `@[deprecated]` alias
  (`CONTRIBUTING.md`).

## Statements first, then proofs

- **Two phases** (plan §4, §7). Milestone statements are written at full strength, reviewed, and approved by the
  owner before proofs start. Never weaken a statement to make it provable and never drop a rejection test. A
  proof PR does not edit statements, except a correction the owner approves (`CONTRIBUTING.md` "Statements").
- **A statement you believe is false:** open an issue with a counterexample (a named theorem proving the
  negation, or a concrete instance) and stop; do not change the statement.
- **A lemma you need from another agent's area** becomes a `sorry` lemma in your own file (under `Lemmas/` or
  `Proofs/` only), listed in your handoff; whoever merges deduplicates it or moves it to `Lemmas/`.
- **Search before adding a lemma** (Mathlib, `Lemmas/`, `ToMathlib/`, `exact?`): duplicates cost review.
- **Task size:** one cohesive, reviewable change per PR (one milestone file, one lemma area).

## Reviews and handoffs

- Reviews are local (#2): independent model instances that did not write the change (e.g. Codex gpt-6-astra
  read-only and a separate Claude subagent). Statement fidelity (does the Lean say what the reference says?)
  and engineering (layout, speed, style) are reviewed separately. A reviewer never edits the change or reruns
  the gates in the author's tree; it reports findings.
- **Handoffs and PR bodies** name the declarations added or changed, their assumptions, every open `sorry`, and
  the commands actually run with their result. Never claim a check you did not run.
- **Names** describe the mathematics: no provenance (agent, issue number, `_v2`, `_new`) in declaration names.
- Once a proof works, make it compact and robust (`CONTRIBUTING.md` "Proofs").
