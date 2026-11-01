# FG finality P4b

Move commit: `ce44f50d`. Lean commit: `d7be08b9`. The helper text is unchanged.

Laws: `fgsaSafetyWireLaws`, `fgsaSafetyClientLaws` (including `tick_rows`), and `fgsaSafetyUnitLaws`.

Height line: `height AvailableChain.FGSA.Run.fgsaSafetyClientLaws`. The lead approved its reason on 2026-10-07. J6 removes it.

slashes-read moved to P10 (lead 2026-10-07)

No guard edits. All required pre-commit checks passed: builds with `--wfail`, `check-build.sh`, layers, GLY, full `check-fgsa.sh`, `NEG=0` claims, proof coverage, and axioms. `CheckProofEqns` is clean. The laws use only standard Lean axioms.
