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
| `fgsa-spec.tex` | Goldilocks | the protocol (SPEC): FG-SA with loose BJ (goldilocks#14) and weakened E1 (goldilocks#15) |
| `shared/composition.tex`, `shared/fg.tex` | | the node composition and the finality gadget, `\input` by `fgsa-spec.tex` |
| `goldilocks-claims.tex` | Goldilocks: claims and proof architecture | the claims and proof DAG (CLAIMS) that the instance statements transcribe |
| `fgsa-spec-lean-notes.tex` | FG-SA specification: relation to the Lean model and claims | how the spec maps to the old Lean model; cited by the claims ("lean notes") |
| `fgsa-protocol.tex` | FG-SA: complete protocol | historical round-model protocol text, the source of the baseline's numbers; not the current FG (no loose BJ) |
| `flatten.py` | | inlines `\input{shared/…}`, for pins |

Not copied (they stay in the archive only): `pcsa-spec.tex` and `pcsa-spec-lean-notes.tex` (PC-SA), and
`sa-protocol.tex` (slow arming on its own), which the live files do not cite.

Build: `latexmk -pdf <file>.tex` for each of `fgsa-spec.tex`, `goldilocks-claims.tex`,
`fgsa-spec-lean-notes.tex` and `fgsa-protocol.tex` (each builds standalone). Build output is not tracked
(`.gitignore`).

Pins: a pin is the SHA-256 of the flattened text (`python3 flatten.py <file>.tex | shasum -a 256`), so splitting
a section into `shared/` does not change it.
