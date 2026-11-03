#!/usr/bin/env bash
# Baseline waivers of check-decls (scripts/check_decls_baseline.txt) are per declaration and per kind: a
# reaches-opaque entry waives its own declaration only, and an entry of the wrong kind waives nothing and
# is reported stale. Ours (scripts/test_check_decls.sh is EthLib's, vendored verbatim and pinned); uses the
# same planted fixtures (scripts/CheckDeclsTest). Run from anywhere.
set -uo pipefail
cd "$(dirname "$0")/.."
FAIL=0
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

if ! lake build CheckDeclsTest >"$WORK/build" 2>&1; then
  echo "FAIL: the fixtures do not build"; cat "$WORK/build"; exit 1
fi
check() { lake exe check-decls --scope CheckDeclsTest "$@" CheckDeclsTest; }

# Every planted finding, as check-decls reports it with an empty baseline.
check --baseline /dev/null >"$WORK/out"
grep -vE '^(check-decls:|stale )' "$WORK/out" | cut -d: -f1 | LC_ALL=C sort -u >"$WORK/expected"
if ! grep -qx 'reaches-opaque CheckDeclsTest.Bad.countdown' "$WORK/expected" \
   || [ "$(grep -c '^reaches-opaque ' "$WORK/expected")" -lt 2 ]; then
  echo "FAIL: the fixtures do not plant two reaches-opaque findings"; cat "$WORK/expected"; exit 1
fi
# Positive control: exact waivers for all findings pass; an always-failing checker must fail this test.
if check --baseline "$WORK/expected" >"$WORK/out"; then
  echo "ok:   a complete, exact baseline passes"
else
  echo "FAIL: exact waivers do not pass"; cat "$WORK/out"; FAIL=1
fi
# A waiver covers its own declaration only: dropping one reaches-opaque entry fails the check on exactly
# that declaration, while its siblings of the same kind stay waived.
grep -vx 'reaches-opaque CheckDeclsTest.Bad.countdown' "$WORK/expected" >"$WORK/partial"
if ! check --baseline "$WORK/partial" >"$WORK/out"; then
  grep -vE '^(check-decls:|stale )' "$WORK/out" | cut -d: -f1 | LC_ALL=C sort -u >"$WORK/unwaived"
  if [ "$(cat "$WORK/unwaived")" = "reaches-opaque CheckDeclsTest.Bad.countdown" ]; then
    echo "ok:   an entry waives only its own declaration (an unlisted reaches-opaque still fails)"
  else
    echo "FAIL: dropping one entry unwaived something else:"; cat "$WORK/unwaived"; FAIL=1
  fi
else
  echo "FAIL: a baseline missing one reaches-opaque entry passes"; FAIL=1
fi

# A waiver covers its own kind only: the same declaration under another kind waives nothing, fails the
# check, and is reported stale.
sed 's/^reaches-opaque CheckDeclsTest.Bad.countdown$/opaque CheckDeclsTest.Bad.countdown/' "$WORK/expected" \
  >"$WORK/wrongkind"
if ! check --baseline "$WORK/wrongkind" >"$WORK/out" \
   && grep -q '^reaches-opaque CheckDeclsTest.Bad.countdown' "$WORK/out" \
   && grep -qx 'stale baseline entry, no longer found: opaque CheckDeclsTest.Bad.countdown' "$WORK/out"; then
  echo "ok:   an entry of the wrong kind waives nothing and is reported stale"
else
  echo "FAIL: a wrong-kind entry is not rejected"; cat "$WORK/out"; FAIL=1
fi

exit "$FAIL"
