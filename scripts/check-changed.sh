#!/usr/bin/env bash
# Local incremental check before a commit or PR: `scripts/check.sh --changed [<base>]` (see its header).
# <base> defaults to the merge-base of HEAD with origin/main; uncommitted and untracked files count.
# It builds the changed modules' downstream cone, runs check-decls on the affected libraries, the Spec
# surface only if a Spec module changed and the grep backstop on the changed files, and prints every
# step as PASS, FAIL or SKIP (with the reason). A change of scripts/ or of the build configuration falls
# back to `check.sh --fast` (with the self-tests for scripts/). On the shared box run it in a job:
#   job --mem 16G --cpus 8 consensus-lean <name> -- bash -lc "cd <worktree> && scripts/check-changed.sh"
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
(($# <= 1)) || { echo "usage: scripts/check-changed.sh [<base>]" >&2; exit 2; }
exec scripts/check.sh --changed "$@"
