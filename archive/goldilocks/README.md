# Available chain / FG-SA

This repository is a Lean 4 formalization of FG-SA (“Goldilocks”): the SA available chain with a
finality gadget, in a sleepy model with committees. It includes the protocol model, claim
statements, proofs, and generic supporting libraries; it does not include a client implementation.

The headline theorem is `AvailableChain.FGSA.Run.fgsaClaims : FGSAClaims p`, assembled in
[Assembly.Root](fgsa/AvailableChainFGSAProofs/Proofs/Assembly/Root.lean).
Its claim types retain their regime premises; in particular, the output contract treats recovery as
a premise. The complete field definitions are in
[fgsa/AvailableChainFGSAClaims/FGSAClaims.lean](fgsa/AvailableChainFGSAClaims/FGSAClaims.lean):

- Inherited safety fields: `carrier`, `chainCertificates`, `store`, `activeView`, `leaseOrigins`,
  `reconcile`, `outputNesting`, `frame`, `clientSafety`, `clientSafetyBase`, `sourceDisciplineBase`,
  `sourceDiscipline`, `sameLabel`, `releaseStore`, `release`, `headReachesLo`, `cleanCut`,
  `cleanHistory`, `cleanPrefixTruncation`, `cleanSafety`.
- Additional fields: `finality`, `finalizedSafety`, `finalLock`, `outageCompat`, `fastP1`, `slowP1`,
  `exactProposal`, `cleanInclusionPostGate`, `cleanInclusion`, `firstFinalityRecFE`,
  `firstFinalityRecF4`, `finalityLivenessGSTRecFE`, `finalityLivenessGSTRecF4`,
  `proposalFinalGSTRecFE`, `proposalFinalGSTRecF4`, `aboveFrontierGSTRecFE`,
  `aboveFrontierGSTRecF4`, `availableGST`, `availableGrowthGST`, `cleanGrowth`,
  `weakContinuationLive`.
- The `finality` record contains `accountable`, `agreement`, `runAccountable`, `runAgreement`,
  `eventPrefixAgreement`, `faultCountSlashableBound`, `finalizedMonotone`, `honestNeverSlashed`.

The earlier model decisions in [docs/internal/CONTRACT.md §1](docs/internal/CONTRACT.md#1-decisions)
specify committees containing all `n` unit-weight seats, assigned to validators by a fresh hidden
bijection per label, with claims quantified over every assignment rather than sampling error.
Corruption is static: the faulty set is fixed for a run. That draft predates the current full-sleep
engine: valid runs have no tick, delivery or restart while asleep. Claim-specific readiness and
recovery premises are part of the current result. Sleepy regimes start at `GST = t₀ = 0`; a later
global stabilization time requires recovery. FG-SA's claim-specific assumptions are given by the
linked claim types and their imported statements.

The PC-SA libraries (`AvailableChainPCSA`, `AvailableChainPCSARun`, `AvailableChainPCSAClaims`,
`AvailableChainPCSAProofs`) are an older variant with preconfirmations. They are not ported to the
current sleep model, the checks skip them, and they are not part of the FG-SA result; see
[docs/internal/PCSA-DISABLED.md](docs/internal/PCSA-DISABLED.md). Earlier or auxiliary developments
remain: [docs/internal/SA-STATUS.md](docs/internal/SA-STATUS.md) records the SA contract and fast P1
as proved; [docs/internal/SAPC-STATUS.md](docs/internal/SAPC-STATUS.md) records the SA-PC base and
strong bundles as proved; [docs/internal/GRIDCO-STATUS.md](docs/internal/GRIDCO-STATUS.md) records
all Grid CO contract claims as proved. SAPC is distinct from the PC-SA libraries. For LStar,
[docs/internal/MAP.md](docs/internal/MAP.md#l-instance-definitions-and-statement-no-claim-proofs)
records model and contract definitions, hook proofs and smoke tests, with the general P1 proof
pending. The FG-SA blueprint's partial/open items are recorded separately in
[docs/internal/FGSA-BLUEPRINT-LEAN.json](docs/internal/FGSA-BLUEPRINT-LEAN.json) and
[docs/internal/FGSA-BLUEPRINT-OPEN.md](docs/internal/FGSA-BLUEPRINT-OPEN.md); the aggregate theorem
is not a claim that every blueprint item is closed.

## Repository map

Lake's `srcDir` groups the 25 production libraries under five folders. Module names,
namespaces and imports are unchanged; each facade and its tests stay with its library.

```text
┌──────────────────────┬──────────────────────────────────────────────────────────────┐
│ Group                │ Libraries (prefix AvailableChain)                            │
├──────────────────────┼──────────────────────────────────────────────────────────────┤
│ fgsa/ (start here)   │ FGSA (model, statements), FGSARun (run-level statements),    │
│                      │ FGSAClaims (the claims), FGSAProofs (the proofs; root        │
│                      │ theorem in Proofs/Assembly/Root.lean), FGSAInhabit           │
│                      │ (non-vacuity witnesses)                                      │
│ generic/             │ Generic, Kit, KitV2, KitFG (available-chain and finality     │
│                      │ building blocks), FGCompose (the finality-gadget results in  │
│                      │ a protocol-independent form)                                 │
│ engine/              │ EngineV2 (the execution model with sleep and duties), Model, │
│                      │ Statements, Witnesses, Framework, Registry                   │
│ legacy/              │ SA, SAPC, GridCO, LStar, SimplexFG                           │
│ pcsa/ (not ported)    │ PCSA, PCSARun, PCSAClaims, PCSAProofs                        │
└──────────────────────┴──────────────────────────────────────────────────────────────┘
```

Reader docs: [architecture](docs/ARCHITECTURE.md), [protocol](docs/PROTOCOL.md),
[modeling choices](docs/MODELING_CHOICES.md), and [review guide](docs/REVIEW_GUIDE.md).
`scripts/` holds checkers and gates; `docs/internal/` holds generated APIs, working maps,
blueprint snapshots and history. [PATHS](docs/internal/PATHS.md) maps old source coordinates.

A short reading path for FG-SA:
[fgsa/AvailableChainFGSAClaims/FGSAClaims.lean](fgsa/AvailableChainFGSAClaims/FGSAClaims.lean) (what
is claimed), then
[Assembly.Root](fgsa/AvailableChainFGSAProofs/Proofs/Assembly/Root.lean)
(how the claims are assembled), then the model under
[fgsa/AvailableChainFGSA/](fgsa/AvailableChainFGSA/).

## Build and checks

Use the version pinned in [lean-toolchain](lean-toolchain) (`leanprover/lean4:v4.34.1`):

```sh
lake exe cache get
lake build --wfail
lake build --wfail @ AvailableChainFGSAClaimsTests AvailableChainFGSAProofsTests \
  AvailableChainFGSAInhabitTests
```

The complete local gate entrypoint is `bash scripts/gate.sh --tier full --base <base> --neg`.
Run it under the repository's existing machine and memory workflow. The reorganized writer
runs the individual local checks; the lead owns the NUC FULL gate and its receipt.

After building, the main checks are:

```sh
bash scripts/precheck.sh .
python3 -B scripts/check-gly-rules.py
python3 -B scripts/check-layers.py
python3 -B scripts/check-module-headers.py
bash scripts/shake-report.sh --fail-on-new
lake build AvailableChainCheckSupport
LEAN_CAP_GB=12 lake env lean --run scripts/CheckProofEqns.lean \
  --baseline scripts/baselines/check-proof-eqns.txt
python3 -B scripts/check-proof-coverage.py
python3 -B scripts/check-fg-finality-coverage.py
python3 -B scripts/check-fg-compose-source.py
python3 -B scripts/api-snapshot.py --scope compose --check
bash scripts/check-fg-compose.sh
LEAN_CAP_GB=12 bash scripts/check-fgsa-claims.sh
```

Precheck enforces source policy before compilation. The GLY, layer and header scripts check
generic-library rules, import boundaries and module headers. Shake reports unused imports and
rejects new removal suggestions. `CheckProofEqns.lean` checks equation exports and
statement-definition backstops; the coverage scripts check owning axiom-audit inventories and public
finality-safety declarations. The Compose source check enforces its source/export policy, the API
check compares the compiled snapshot, and the two shell checks build and audit their declared scopes
and run controls. These are mechanical checks of their stated scopes, not proofs of
blueprint-to-Lean semantic equivalence (see
[scripts/check-fgsa-blueprint.py](scripts/check-fgsa-blueprint.py)).

Run the existing axiom audit, which includes `#print axioms AvailableChain.FGSA.Run.fgsaClaims` in
[fgsa/AvailableChainFGSAProofs/Tests/Axioms.lean](fgsa/AvailableChainFGSAProofs/Tests/Axioms.lean):

```sh
lake env lean fgsa/AvailableChainFGSAProofs/Tests/Axioms.lean
```

The licence is [CC0 1.0 Universal](LICENSE).
