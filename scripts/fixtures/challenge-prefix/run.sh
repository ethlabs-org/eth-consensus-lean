#!/usr/bin/env bash
# Fixture for CheckConsensusAxioms.lean's exclusion of `ConsensusChallenge.lean` (exact name only).
# Compiles ConsensusChallengeExtra.lean (holds `axiom bad`) into a temporary directory next to a
# ConsensusChallenge.lean (excluded, never compiled or imported) and runs the audit there; the
# audit must exit 1 and report `bad`. Run from the repository root: `lake env bash <this file>`.
set -euo pipefail
root=$(pwd)
here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cp "$here/ConsensusChallengeExtra.lean" "$tmp/"
printf 'theorem excluded : False := sorry\n' > "$tmp/ConsensusChallenge.lean"
(cd "$tmp" && LEAN_PATH="$tmp:${LEAN_PATH:-}" lean -o ConsensusChallengeExtra.olean ConsensusChallengeExtra.lean)
set +e
out=$(cd "$tmp" && LEAN_PATH="$tmp:${LEAN_PATH:-}" lean --run "$root/CheckConsensusAxioms.lean" 2>&1)
rc=$?
set -e
echo "$out"
if [ "$rc" -eq 1 ] && grep -q 'Unexpected axiom: .* uses CheckFixtures.ChallengePrefix.bad' <<<"$out" \
    && grep -q 'across 1 modules' <<<"$out"; then
  echo "challenge-prefix fixture: OK (prefix module audited, ConsensusChallenge.lean excluded)"
else
  echo "challenge-prefix fixture: FAILED (rc=$rc)"; exit 1
fi
