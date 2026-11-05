# Goldilocks spec (LaTeX, live)

The live LaTeX spec of Goldilocks: the protocol, its claims and the notes on the Lean model. It is
**edited here**, in this repository, and new citations name a commit of this folder.

| File | Title | What |
| --- | --- | --- |
| `goldilocks-spec.tex` | Goldilocks | the protocol (SPEC), with loose BJ and weakened E1 |
| `shared/composition.tex`, `shared/fg.tex` | | the node composition and the finality gadget, `\input` by `goldilocks-spec.tex` |
| `goldilocks-claims.tex` | Goldilocks: claims and proof architecture | the claims and proof DAG (CLAIMS) that the instance statements transcribe |
| `goldilocks-spec-lean-notes.tex` | Goldilocks specification: relation to the Lean model and claims | how the spec maps to the old Lean model; cited by the claims ("lean notes") |
| `flatten.py` | | inlines `\input{shared/…}`, for pins |

Build: `latexmk -pdf <file>.tex` (or `tectonic <file>.tex`) for each of `goldilocks-spec.tex`,
`goldilocks-claims.tex` and `goldilocks-spec-lean-notes.tex` (each builds standalone). Build output is not
tracked (`.gitignore`).

Names: older texts call these files `fgsa-spec.tex` and `fgsa-spec-lean-notes.tex` (the protocol was once named
FG-SA).

Pins: a pin is the SHA-256 of the flattened text (`python3 flatten.py <file>.tex | shasum -a 256`), so splitting
a section into `shared/` does not change it.
