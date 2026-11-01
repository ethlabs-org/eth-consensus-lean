# Spec

LaTeX sources of the protocols that this repository formalizes. They moved here on
2026-10-27 from the research folder `async-resilient-committees/tip-stability/spec/`
(last change there: 2026-10-21). Their earlier history, the archived old versions and
the change notes are in the private archive (`fradamt/archive`, folder `research/`).

| File | Title | What |
| --- | --- | --- |
| `fgsa-spec.tex` | Goldilocks | FG-SA specification; the spec work since 2026-10-12 is here |
| `fgsa-protocol.tex` | FG-SA: complete protocol | historical round-model protocol text; the Lean authority pins it (below). Not the current FG: no loose BJ; the current FG rules are in `shared/fg.tex` |
| `fgsa-spec-lean-notes.tex` | FG-SA: relation to the Lean model and claims | how the spec maps to the Lean model |
| `pcsa-spec.tex` | PC-Goldilocks | PC-SA specification (stage 2) |
| `pcsa-spec-lean-notes.tex` | PC-SA: relation to the stage-2 Lean model | how the spec maps to the Lean model |
| `sa-protocol.tex` | Slow arming (SA): complete protocol | the SA available chain on its own |
| `shared/fg.tex`, `shared/composition.tex` | | sections shared by the specs (`\input`) |

Build: `latexmk -pdf <file>.tex` (all six build standalone). Build output is not tracked.

Pins: a pin is the SHA-256 of the flattened text (`python3 flatten.py <file>.tex | shasum -a 256`),
so splitting a section into `shared/` does not change it. `docs/internal/ARCHITECTURE.md` pins
`fgsa-protocol.tex` at `59bb0dda` (2026-10-01); the file here is at `e86980ff` (later edits; the last, 2026-10-30, adds a scope notice: the text does not specify loose BJ).
The pinned version is in the archive history.
