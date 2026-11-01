# Goldilocks archive (reference only)

A snapshot of the old Goldilocks Lean model and its spec (`spec/`, the LaTeX sources), copied without history
from `ethlabs-org/goldilocks-archive` (branch `sync/fradamt-agent-main`, the old `fradamt-agent/goldilocks`
`main`) at
[`23f5fdaa`](https://github.com/ethlabs-org/goldilocks-archive/tree/23f5fdaa232f06d9c8c01eb02830f5cfc3976b7d).

- **Never built here.** It targets Lean `v4.34.1` (its own `lean-toolchain`, `lakefile.toml` and
  `lake-manifest.json` are kept for reference only); it is not part of consensus-lean's lakefile, and
  `ConsensusLean` does not import it.
- **Not checked.** No step of `scripts/check.sh` reads it, and its own scripts are not run.
- **Not edited**, except to resync it from the archive repository.

Omitted (generated dumps and logs; they are at the link above):

- files over 1 MB: `docs/internal/api/{compose-api,fgsa-claims-api,legacy-api,fgsa-deep,pcsa-deep,gen-deep,v2-deep}.json`,
  `docs/internal/FGSA-PORT-CHANGES.json`, `docs/internal/FGSA-PORT-PCSA-BASELINE.json`,
  `docs/internal/FGCOMPOSE-RELEASE-LEDGER.md`, `docs/internal/FGSA-SEMANTIC-LEDGER-stage4.md`;
- the agent audit transcripts `docs/internal/audit/*.log` (10 files);
- the compressed blobs `docs/internal/lock-log/root-digest-2/*.gz` (4 files);
- `.agents/setup` (orb configuration).

Citations elsewhere in this repository: docstrings under `ConsensusLean/` cite `fradamt-agent/goldilocks` files at
pinned commits (for example `00df7945`, `5ae87546`, `a470648c`). Every such commit is in the history of `23f5fdaa`,
so `ethlabs-org/goldilocks-archive` has it, and the files it names are here in their latest form. `goldilocks#N`
issue references point to the issues of `fradamt-agent/goldilocks`.
