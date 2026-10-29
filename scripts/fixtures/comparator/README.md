# Fixtures for the comparator-config glue of scripts/check.sh (step 9).
# `statements.txt` stands in for SpecSurface `statements`; config-good.json passes,
# every other config must be rejected (config-multi: two JSON objects; config-empty with statements-empty.txt).
`challenge-{import,weaker,extra,hidden}.lean` (header-only, never built) are rejected by `challenge_ok`: an import
besides the review statements module, a theorem whose statement is not its Prop definition, an extra declaration, a
declaration between two comments on one line.
