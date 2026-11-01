# Current API snapshots

Run `python3 -B scripts/write-api-snapshots.py --write`, then review the diff.
Run the same command with `--check` to compare with the current compiled state.
PCSA's shallow document stays unchanged on this branch; the writer checks it.

Each graph uses format 2. Nodes have stable declaration names, kernel name bytes,
module, kind, direct dependencies, own SHA-256, and readable type/body lines.
Roots have module, kind, and full closure SHA-256. `node_order` records Lean's
`Name.lt` order. The validator recomputes each root digest from the named graph.
Toolchain and package pins are stable inputs. No HEAD or date enters equality.
Theorem proof values are excluded. Readable text is evidence; kernel bytes set
its digest. The pretty printer can omit proof arguments from readable bodies.

FGSA and PCSA deep roots equal their complete compiled shallow manifest scopes.
V2 and GEN use the same public scopes as their shallow manifests. Legacy covers
GridCO, SimplexFG, KitFG, and v1 Kit. Compose covers its public compiled scope.
The auxiliary `fgsa-claims-api.json` covers all FGSA public Statements and Claims,
public exports and assembly roots, and theorems in the blueprint map, including
its PCSA cross-references.
Private definitions reached from these roots remain in the node graph. Public
proof-test and Inhabit fixture names are not auxiliary review roots; the full
compiled audit inventories and proof checks still cover those source scopes.

`api-diff.py --base <commit> --target <commit> --snapshots <paths> --output <json>`
reads committed snapshots. It emits JSON plus readable Markdown, including the
union of changed roots, old/new statements, node changes, and both graph sides.
Its groups are navigation data. They do not suppress root or node rows.

For dry-run measurement, first use `api-snapshot.py --scope semantic --roots
<names.txt|roots.tsv|roots.json> --write --output <scratch.json>` on each source
state. This makes an auxiliary graph for named subjects, including V2 twins and
retained Generic PC declarations outside the FGSA manifest. Then use
`fgsa-deep.py --attribute --baseline <base.json> --snapshot <target.json> --roots
<list> --output <report.json>`. The report records through-root and shared-node
paths on each side. Missing planned subjects are explicit diagnostics. This
report is structural attribution; it does not measure one edit in isolation.
The roots input never grants an exception and cannot be used with deep --write.
