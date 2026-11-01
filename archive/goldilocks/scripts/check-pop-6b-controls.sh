#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

# Standalone generic event-fold controls; every Lean invocation keeps throttling enabled.
mkdir -p .lake/build/lib/lean/tests
for control in POP6bMixedFixture POP6bMixedFacts POP6bMixedControl; do
  lake env lean -DwarningAsError=true \
    -o ".lake/build/lib/lean/tests/${control}.olean" "tests/${control}.lean"
done
lake env lean -DwarningAsError=true tests/POP6bMixedNegative.lean
lake env lean -DwarningAsError=true tests/POP6bFrozenControl.lean
