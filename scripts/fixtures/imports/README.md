# Header-only import trees for `scripts/check-imports.py --self-test` (never built).
# Each case has its own boundaries.toml and lakefile.toml; the expected tag is in check-imports.py CASES.
# `Good`: one certified lib `Fx` (groups `spec` = Fx.Spec, `impl` = Fx.Impl + Fx.Proofs), a test lib `FxTest`
# (may import the root `Fx`), a single-module lib `FxSol`, a fixture lib `FxFix`; each other case changes one
# thing (an import, a root listing, a config entry or a lakefile entry).
