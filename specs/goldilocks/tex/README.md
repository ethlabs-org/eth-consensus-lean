# Goldilocks spec (LaTeX, live)

The live LaTeX spec of Goldilocks: the protocol, its claims and the notes on the Lean model. It is
**edited here**, in consensus-lean, and new citations name a consensus-lean commit of this folder.

Provenance: copied byte-identically from
[`ethlabs-org/goldilocks-archive`](https://github.com/ethlabs-org/goldilocks-archive) at
[`23f5fdaa`](https://github.com/ethlabs-org/goldilocks-archive/tree/23f5fdaa232f06d9c8c01eb02830f5cfc3976b7d)
(`spec/`, the history of `fradamt-agent/goldilocks`). The frozen copy of that snapshot is
[`archive/goldilocks/spec/`](../../../archive/goldilocks/spec/), which is not edited; older pins (for example
"CLAIMS at goldilocks `c4928a76`") refer to that history.

| File | Title | What |
| --- | --- | --- |
| `goldilocks-spec.tex` | Goldilocks | the protocol (SPEC), with loose BJ (goldilocks#14) and weakened E1 (goldilocks#15) |
| `shared/composition.tex`, `shared/fg.tex` | | the node composition and the finality gadget, `\input` by `goldilocks-spec.tex` |
| `goldilocks-claims.tex` | Goldilocks: claims and proof architecture | the claims and proof DAG (CLAIMS) that the instance statements transcribe |
| `goldilocks-spec-lean-notes.tex` | Goldilocks specification: relation to the Lean model and claims | how the spec maps to the old Lean model; cited by the claims ("lean notes") |
| `goldilocks-round-model.tex` | Goldilocks: the round-model protocol (historical baseline) | historical round-model protocol text, the source of the baseline's numbers; not the current FG (no loose BJ) |
| `flatten.py` | | inlines `\input{shared/…}`, for pins |

Not copied (they stay in the archive only): `pcsa-spec.tex` and `pcsa-spec-lean-notes.tex` (PC-SA), and
`sa-protocol.tex` (slow arming on its own), which the live files do not cite.

Build: `latexmk -pdf <file>.tex` (or `tectonic <file>.tex`) for each of `goldilocks-spec.tex`,
`goldilocks-claims.tex`, `goldilocks-spec-lean-notes.tex` and `goldilocks-round-model.tex` (each builds
standalone). Build output is not tracked (`.gitignore`).

Names: the archive and the older pins call these files `fgsa-spec.tex`, `fgsa-spec-lean-notes.tex` and
`fgsa-protocol.tex` (the protocol was once named FG-SA); they were renamed here on 2026-11-03.

Pins: a pin is the SHA-256 of the flattened text (`python3 flatten.py <file>.tex | shasum -a 256`), so splitting
a section into `shared/` does not change it.
