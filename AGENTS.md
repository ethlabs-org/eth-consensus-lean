# Agents

Coordination (claiming issues, branches, PRs): GitHub issue #2. Trust boundary: `TRUST.md`.
Checks and CI tiers: README "Verification".

## Working on this repo

- **Worktree per task.** Work on `work/<agent>/<task>` in your own worktree; never in a tree another
  agent uses. On the shared box, hard-link the packages instead of fetching them:
  `mkdir -p <wt>/.lake && cp -al <main>/.lake/packages <wt>/.lake/packages`.
- **Every build in a job** (shared memory pool; OOM kills hit everyone):
  `job --mem 16G --cpus 8 consensus-lean <unique-name> -- bash -lc "cd <worktree> && LAKE_RESTORE_ARTIFACTS=true <cmd>"`,
  then wait for it (`/srv/status/<user>.<unit>.json`, `journalctl --user -u <unit>`).
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
  (`scripts/check.sh --fast`, about 10–13 minutes; 17 with self-tests); kernel replay, `lake check` and
  `lake comparator --paranoid` run nightly (`full.yml`) or on demand (`gh workflow run full.yml --ref <branch>`).
  CI must be green to merge.
- **Trusted surface** (`ConsensusLean/{Init,Core,Spec,Statements,ToMathlib}` as `X.lean` and `X/**`,
  `Challenge.lean`, `comparator.json`, `lean-toolchain`, `lake-manifest.json`,
  `ConsensusLeanTest/Review{Axioms,Guard}.lean`): the list is `trusted_paths` in `scripts/boundaries.toml`,
  and CI also checks the list at the tag. CI's `review-boundary`
  fails until the `spec-approved` tag covers the change. Never create or move the tag; say in the PR that it
  needs approval. `scripts/**`, `.github/**` and the lakefile are owner-reviewed via CODEOWNERS.
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
