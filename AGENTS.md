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
- **Before committing:** `scripts/check-changed.sh` (in a job). It builds the downstream cone of the
  changed modules and runs the fast checks restricted to what changed; read its `SKIP` lines to see
  what it did not check. A change to `scripts/` or the build configuration runs the whole fast mode.
- **Open a PR when ready.** Pushes to `work/*` without a PR run no CI. A PR runs the fast tier
  (`scripts/check.sh --fast`, about 10–13 minutes; 17 with self-tests); kernel replay, `lake check` and
  `lake comparator --paranoid` run nightly (`full.yml`) or on demand (`gh workflow run full.yml --ref <branch>`).
  CI must be green to merge.
- **Trusted surface** (`ConsensusSpec/**`, `ConsensusSpec.lean`, `ConsensusChallenge.lean`, `comparator.json`,
  `lean-toolchain`, `lake-manifest.json`, `ConsensusTests/Review{Axioms,Guard}.lean`): CI's `review-boundary`
  fails until the `spec-approved` tag covers the change. Never create or move the tag; say in the PR that it
  needs approval. `scripts/**`, `.github/**` and the lakefile are owner-reviewed via CODEOWNERS.
- **Spec snapshot:** a Spec change fails step 4 until `scripts/spec-snapshot.txt` is regenerated
  (`scripts/check.sh --update-snapshot`, which then fails on purpose) and the diff is committed for review.
