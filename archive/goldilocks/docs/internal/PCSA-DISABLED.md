# PC-SA disabled for the sleep migration

Last green tag: `pcsa-pre-sleep` at `6c36d4810cb070655f2f4aadb3346db6c76aa0a3`.

The user selected engine-wide full sleep on 2026-10-09 (option 1). PC-SA breakage is
accepted. The source stays in the repository. `docs/PCSA-API.md` stays frozen.
Valid sleep runs will have no tick, delivery or restart while asleep. The old PC-SA
receiver contracts do not require receiver readiness. A receiver can sleep before
receipt and fail to hold the block. An awake quorum does not make every receiver awake.

The following contracts, and their public `_def` equations, need a sleep port:

```text
┌───────────────────┬───────────────────────────────────┐
│ Claims file       │ Contract                          │
├───────────────────┼───────────────────────────────────┤
│ PC.lean           │ PCDisseminationClaim              │
│ Clean.lean        │ PCSACleanInclusionClaim           │
│ Clean.lean        │ StrongIncludedClaim               │
│ Clean.lean        │ CleanBlockReceiptClaim            │
│ Outage.lean       │ ArmHealthyClaim                   │
│ Outage.lean       │ PCSASlowP1Claim                    │
│ StageTwo.lean     │ ArmHealthyStageTwoClaim            │
│ StageTwo.lean     │ StrongIncludedStageTwoClaim        │
└───────────────────┴───────────────────────────────────┘
```

Disabled compiled paths:

- Default targets: AvailableChainPCSA, AvailableChainPCSARun,
  AvailableChainPCSAClaims and AvailableChainPCSAProofs. Their Lake tables stay.
- Gate PC-SA manifest route, PCSACompose and PCSASafety audits, and their receipt names.
- Claims root coverage for PCSAProofs; proof coverage keys for its Axioms, FGCompose
  and FGSafety audits; the Compose adapter check; the compiled FaultXRoute scan.
- Blueprint oracle checks for the PC-SA safety section only. The nine clauses stay
  as source/map records. FG-SA rows keep full checks regardless of their module field.
- Default shake selection, including when PC-SA `.olean` files are present.
- The four PC-SA entries in `scripts/new-libraries.txt`.

Finality source coverage uses `scripts/pcsa-source-audit-coverage.txt` for PC-SA.
The active compiled inventory keeps every FG-SA and Compose requirement.

The PCSA-API trigger in `gate.sh` stays. Source checks still read PC-SA files through
Lake library tables. `check-sleep-scopes.py` checks the active import closure and
checks deferred PC-SA source for proof placeholders, project axioms and adapter
extensions. It also requires each PC-SA proof module to be reached from its source
facade. The FG-SA facade check stays in `check-fgsa-claims.sh`. PC-SA roots,
facades and Tests aggregators stay as source. No active facade imports them.
CheckGenFirst already excludes PC-SA. CatalogLock imports Framework only and has
no PC-SA roots; this package does not change the catalog. P-Da owns its regeneration
and the link from ARCHITECTURE.md.

To re-enable PC-SA, port it to the sleep engine, repair all eight receiver contracts
with reviewed premises, compile and audit all PC-SA targets, and pass its manifest
and controls. Regenerate PCSA-API under a separate approved exception. Restore the
compiled roots, inventories and gate routes together. P-Da completes this record.
