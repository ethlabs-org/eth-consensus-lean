# FG finality P12 report

Branch: `fgfin-p12`. Base: `56e9a018`. No push.

All eight frozen fields are proved. The closed exports take only `p` outside
the frozen claim type. The run proofs cover every `m : FGMode`.
`pcsaSafetyFinalityClaims` supplies `PCSAClaims.finality` from
`AvailableChainPCSAProofs/Proofs/Assembly/Finality.lean`.

```text
┌──────────────────────────┬────────┐
│ Field                    │ Status │
├──────────────────────────┼────────┤
│ accountable              │ PROVED │
│ agreement                │ PROVED │
│ runAccountable           │ PROVED │
│ runAgreement             │ PROVED │
│ eventPrefixAgreement     │ PROVED │
│ finalizedMonotone        │ PROVED │
│ faultCountSlashableBound │ PROVED │
│ honestNeverSlashed       │ PROVED │
└──────────────────────────┴────────┘
```

No field is STOPPED.

Commits:

- `cee8a22e` — policy: allow exact PC-SA finality safety bridge edges.
- `c80c5c5b` — prove the PC read adapters and six run bodies.
- `a2013a69` — close the eight claim exports and assemble finality safety.
- The final documentation commit records this report.

The pure accountability proof uses KitFG certificate safety. Pure agreement
uses that result and excludes the slashable case. The six run bodies use
the PC law producers and the Compose proofs through one bridge.

The carriage adapter proves only `PCFinalityRowCarriage → safetyCarriage`.
The fault-count proof retains carriage of every run block, including ancestors.
Honest non-slashing uses P3 stored-row carriage and client safety.
Only monotonicity needs `NoRestart`. No time or event horizon was added.

Guard changes:

- `scripts/check-layers.py` adds four exact `COMPOSE_EDGES` pairs.
  Their importer is
  `AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyBridge`.
  Their targets are:
  `AvailableChainFGCompose.Proofs.SafetyAccountable`,
  `AvailableChainFGCompose.Proofs.SafetyCount`,
  `AvailableChainFGCompose.Proofs.SafetyMonotone`, and
  `AvailableChainFGCompose.Proofs.SafetySlashing`.
- The restricted PC set adds seven exact modules under
  `AvailableChainPCSAProofs.Proofs.Foundations`:
  `NamedScope`, `Proposals`, `TickOutput`, `FGSafetyScope`,
  `FGSafetyClientLaws`, `FGSafetyBridge`, and `FinalitySafety`.
  The FG-SA target exceptions remain `AvailableChainFGSA.Proofs.Carrier`
  and `AvailableChainFGSA.Proofs.StoreLaws`.
- `scripts/check-layers-selftest.sh` adds the bridge-to-
  `AvailableChainFGSARun.Proofs.Reachable` negative fixture. It expects `LANE`.
  The existing loops test each new positive pair and both `.Extra` neighbours.
- The audit adds explicit `#print axioms` lines for all 31 new public names.
  `check-proof-coverage.py --write` regenerates the coverage inventory.
  It contains 5,868 declarations across 13 audits.

Other guard, policy, and baseline edits: none. No stopped guard item.
No `laneUpstream` edit was needed. The first F-3 check rejected two pure
helpers with explicit `RootInjectiveOn` premises. Those helpers were removed.
The closed exports retain the frozen premises inside the claim types.

The PC Claims, Statements, and Model files have no diff from the base.
FG-SA and FGCompose files, frozen audits, and `docs/PCSA-API.md` have no diff.
The PC manifest check reports 421 entries in 21 modules; hashes match.
All 31 new names use only `propext`, `Classical.choice`, and `Quot.sound`.

All required validation commands pass (exit 0). The build uses the default
target. The layer selftest and full GLY check also run through `check-build.sh`.
The GLY check inherits `LC_ALL=C`. The Compose driver runs its full controls.

```text
┌─────────────────────────────────────────────────────────┬────────┐
│ Command                                                 │ Result │
├─────────────────────────────────────────────────────────┼────────┤
│ lake build --wfail                                      │ PASS   │
│ LC_ALL=C bash scripts/check-build.sh                    │ PASS   │
│ python3 scripts/check-layers.py                         │ PASS   │
│ bash scripts/check-layers-selftest.sh                   │ PASS   │
│ bash scripts/check-gly-rules.sh (LC_ALL=C)              │ PASS   │
│ LC_ALL=C python3 scripts/check-gly-rules.py --rule F-13 │ PASS   │
│ bash scripts/check-fg-compose.sh                        │ PASS   │
│ python3 scripts/check-fg-compose-controls.py            │ PASS   │
│ NEG=0 bash scripts/check-fgsa-claims.sh                 │ PASS   │
│ NEG=0 bash scripts/check-pcsa-manifest.sh               │ PASS   │
│ python3 scripts/check-proof-coverage.py --write         │ PASS   │
│ python3 scripts/check-proof-coverage.py                 │ PASS   │
│ bash scripts/check-fg.sh                                │ PASS   │
└─────────────────────────────────────────────────────────┴────────┘
```

The explicit axiom-line check passes for all 31 public names. Coverage adds
31 names and removes none. `git diff --check` passes. No push.
