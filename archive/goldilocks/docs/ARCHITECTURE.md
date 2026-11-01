# Architecture

Lake declares 25 production libraries and four overlapping audit targets. The five folders
organize navigation. They preserve every production Lean file's bytes and every module name.
For example, `AvailableChainFGSAClaims.FGSAClaims` now comes from
[fgsa/AvailableChainFGSAClaims/FGSAClaims.lean](../fgsa/AvailableChainFGSAClaims/FGSAClaims.lean).
Compiled output still lives at `.lake/build/lib/lean/AvailableChainFGSAClaims/FGSAClaims.olean`.

| Folder | Libraries, with the `AvailableChain` prefix omitted |
| --- | --- |
| [engine](../engine/) | Model, Statements, Witnesses, EngineV2, Framework, Registry |
| [generic](../generic/) | Kit, KitV2, Generic, KitFG, FGCompose |
| [fgsa](../fgsa/) | FGSA, FGSARun, FGSAClaims, FGSAProofs, FGSAInhabit |
| [pcsa](../pcsa/) | PCSA, PCSARun, PCSAClaims, PCSAProofs |
| [legacy](../legacy/) | SA, SAPC, GridCO, LStar, SimplexFG |

Each library has a facade beside its complete source subtree, including `Tests/`. The audit
targets have `roots = []` and build tests inside their owner's subtree; they have no separate
facade. CheckSupport remains in `scripts/` and is built by check drivers when needed.
[lakefile.toml](../lakefile.toml) is the sole mapping from module prefixes to source folders.
[scripts/source_layout.py](../scripts/source_layout.py) resolves current and historical layouts.

Folders do not impose new import permissions. Generic still depends on legacy foundations;
KitFG uses SimplexFG. FGCompose provides shared contracts and proofs, and FGSAProofs binds them
to the FG-SA run. Framework uses engine and generic infrastructure; Registry audits concrete
legacy instances. Existing import rules remain in [the checker](../scripts/check-layers.py).

FG-SA and its shared dependencies are active default targets. The four PC-SA libraries and
their proof tests remain deferred by [the UNPORTED switch](../scripts/unported-libraries.txt).
Their sources remain covered by source scanners. Old protocols are live dependencies;
`legacy/` does not imply that they can be removed.

The other reader docs describe [the protocol](PROTOCOL.md), [model choices](MODELING_CHOICES.md)
and [how to review](REVIEW_GUIDE.md). The earlier session architecture is preserved separately
in [internal/ARCHITECTURE.md](internal/ARCHITECTURE.md); archived coordinates are explained by
[internal/PATHS.md](internal/PATHS.md).
