# P0 baseline

Recorded: 2026-10-11. Package: P0z0.
Base: `49ccd55d5b8c5294a8538e538497e556707d861d`.

These are the active committed comparison inputs at the approved base.
PC-SA is UNPORTED; its saved snapshots are not active baseline inputs.
P0z0 adds no Lean declaration and changes no snapshot. Candidates are generated
only in a temporary validation directory. The source files and dependency pins
must match this base when this record is reproduced.

## SHA-256 of file bytes

```text
┌────────────────┬──────────────────────────────────────────────────────────────────┐
│ Input          │ SHA-256                                                          │
├────────────────┼──────────────────────────────────────────────────────────────────┤
│ FG-SA shallow  │ 3813160f6f6cd6998c047d15436202e390b3f240060686f3113110fd849b7c5b │
│ FG-SA deep     │ 5a913032a1c07fb9866b4fb9b915f6e05726ee0b51846c58861c3897705571b9 │
│ FG-SA claims   │ e2ff227b7bbae75e9e0b6e7d193bbac7de5da834eea55a941dbf1f65a3f6dc36 │
│ Compose        │ 6edec2d4073c3090006917598e4533b2e203583d89a1552ba2077051f7694e8e │
│ Legacy         │ 17ddee91891fbd09daca0e0d39dc79d1e779c0360418deaf4154160c24fa000e │
│ V2 deep        │ 1efc8892c8682f3650344c717ef6b00d824859ec8546e730251310ea4fd02827 │
│ Generic deep   │ e83cd21525b53db73ea5d474967a4eb808a6735919995dd133f81af676a28cfc │
└────────────────┴──────────────────────────────────────────────────────────────────┘
```

Exact paths:

- FG-SA shallow: `docs/FGSA-API.md`.
- FG-SA deep: `docs/api/fgsa-deep.json`.
- FG-SA claims: `docs/api/fgsa-claims-api.json`.
- Compose: `docs/api/compose-api.json`.
- Legacy: `docs/api/legacy-api.json`.
- V2 deep: `docs/api/v2-deep.json`.
- Generic deep: `docs/api/gen-deep.json`.

## Reproduction

Run from the repository root with the pinned Lean toolchain and packages already
present. Use the normal Lean runtime slot wrapper. Do not update or fetch packages.
Build the unchanged base with DCK and the G2 combined targets first:

```sh
python3 -B scripts/dev-check.py --package P0z0
lake build --wfail AvailableChainFGSA AvailableChainFGSARun \
  AvailableChainFGSAClaims AvailableChainFGSAClaimsTests \
  AvailableChainFGSAProofs AvailableChainFGSAProofsTests \
  AvailableChainFGSAInhabit AvailableChainFGSAInhabitTests \
  AvailableChainFGCompose AvailableChainGridCO AvailableChainKit \
  AvailableChainSimplexFG AvailableChainKitFG \
  AvailableChainGridCO.Model.Legacy AvailableChainGridCO.Proofs.LegacyMode \
  AvailableChainGridCO.Tests.Axioms \
  AvailableChainGridCO.Proofs.LocalTransfer
```

Generate and compare all seven candidates. Every write has an explicit temporary
destination. `cmp` requires identical bytes; no committed FG-SA file is rewritten.
Keep the validation directory for the handoff.

```sh
set -eu
p0_validation=$(mktemp -d "$PWD/.lake/p0-baseline.XXXXXX")
lake env lean --run scripts/V2Manifest.lean --scope fgsa --write \
  --manifest "$p0_validation/FGSA-API.md"
lake env lean --run scripts/V2Manifest.lean --scope fgsa --deep --write \
  --manifest "$p0_validation/FGSA-API.md" \
  --snapshot "$p0_validation/fgsa-deep.json"
python3 -B scripts/api-snapshot.py --scope fgsa-claims --write \
  --output "$p0_validation/fgsa-claims-api.json"
python3 -B scripts/api-snapshot.py --scope compose --write \
  --output "$p0_validation/compose-api.json"
python3 -B scripts/api-snapshot.py --scope legacy --write \
  --output "$p0_validation/legacy-api.json"
python3 -B scripts/api-snapshot.py --scope v2 --write \
  --output "$p0_validation/v2-deep.json"
python3 -B scripts/api-snapshot.py --scope gen --write \
  --output "$p0_validation/gen-deep.json"
cmp docs/FGSA-API.md "$p0_validation/FGSA-API.md"
for p0_file in fgsa-deep.json fgsa-claims-api.json compose-api.json \
  legacy-api.json v2-deep.json gen-deep.json; do
  cmp "docs/api/$p0_file" "$p0_validation/$p0_file"
done
shasum -a 256 docs/FGSA-API.md docs/api/fgsa-deep.json \
  docs/api/fgsa-claims-api.json docs/api/compose-api.json \
  docs/api/legacy-api.json docs/api/v2-deep.json docs/api/gen-deep.json
shasum -a 256 "$p0_validation/FGSA-API.md" \
  "$p0_validation/fgsa-deep.json" "$p0_validation/fgsa-claims-api.json" \
  "$p0_validation/compose-api.json" "$p0_validation/legacy-api.json" \
  "$p0_validation/v2-deep.json" "$p0_validation/gen-deep.json"
```

## Comparison evidence

All seven compiled candidates matched the committed file bytes and the SHA-256
values above. Candidates were generated under `.lake/p0-baseline.SpBAak`; the
restored legacy candidate is `legacy-api-restored.json`. The other six candidates
have the filenames shown in the reproduction commands. Comparison data and logs
are in `.lake/p0-z0/`.

The first legacy comparison was rejected. Three theorem types came from an
October 2 cached `AvailableChainGridCO.Proofs.LocalTransfer.olean` that the facade
build did not select: `AvailableChain.GridCO.local_early_at_freeze`,
`AvailableChain.GridCO.local_transferReceipts`, and
`AvailableChain.GridCO.local_transfer_from_engine`. The source matched base
49ccd55d. Its SHA-256 is
`764476300c457859f1c38f6130a1a4d92abf19863c7edf2784d61ca0267a0303`.
Rebuilding that exact unchanged source with `--wfail` restored the committed types
and the legacy snapshot byte hash. No source, snapshot, policy, or exclusion was
changed to accept the candidate. The initial type diff is retained at
`.lake/p0-z0/legacy-initial-type.diff`. The reproduction build includes this target
and the three legacy inputs outside the facade selection.

For later packages, compare FG-SA shallow/deep/claims byte hashes with this record.
Keep V2 and Generic deep snapshots unchanged. Review only additive Compose and
legacy roots and dependencies. A change to an old entry or definition closure is
a STOP under plan section 6; do not write a replacement baseline to make it pass.
