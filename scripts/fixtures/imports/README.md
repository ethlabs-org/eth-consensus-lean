# Header-only import trees for `scripts/check-imports.py --self-test` (never built).
# Each case has its own boundaries.toml and lakefile.toml; the expected tag is in check-imports.py CASES.
`LakefileLean` (an empty lakefile.lean next to lakefile.toml), `ShadowBase` (a lib whose root is
`Mathlib.Shadow`), `ShadowGlob` (a one-module glob `Mathlib.Shadow`, no file: the module-prefix rule
alone), `ShadowTop` (a file `Mathlib/Shadow.lean` in a fixture lib's srcDir: the file/directory rule alone) and
`UnknownTarget` (a lakefile lib that is not configured) must give FAIL[config].
