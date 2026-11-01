# FG-SA port r2 — one h+i+j SWITCH

Basis: `318074ba78132f90c894e54dbbc18dd571b02b5b`, branch `port-switch`.
Plan: `docs/plans/fgsa-port-r2.md`, binding rulings A–G, and the 00b edge/consumer map.
Date: 2026-10-09. Status: **red window; TARGET evidence only**.
This commit must land with the later port repairs. It is not FULL or MERGE-green.

This is the one protocol-change record for h+i+j. The change excludes support and
proposal contributions below the local F, and uses only retained contest witnesses.
It does not change cumulative storage, H, justified-pair selection, root ambiguity,
confirmation, revocation, or the frozen support arm. It changes selected results through
those readers. The exact source and dependency hashes are in
[the measured diff](fgsa-port-switch-diff.json). No claim bound or read scope increases.

## Canonical and legacy names

All names below have prefix `AvailableChain.FGSA.`. Canonical signatures stay fixed.
The complete old chain remains in `Model/Legacy/Frame.lean`, under `FGSA.Legacy`.
That file does not import canonical Frame and has no change in this commit.
For each canonical reader below, `Legacy.<same name>` is its old reader.

- `controls`: `KitFG.treeStoreControlsView`; equal to `Next.controls`.
- `fullTree`: `KitFG.treeStoreFrameView` on cumulative TF; equal to `Next.fullTree`.
- `proposerSupport`: resolve in `actView`, then require F-prefix and the existing slot bound;
  equal to `Next.proposerSupportNext`. Raw proposer votes keep their order.
- `proposalsAt st s`: select slot-s proposals whose erased block is in TF above F;
  equal to `Next.proposalsAtNext p st s`. The signature still has no Params argument.
  A local filter gives the same tree without changing that signature.
- `voterBlocks`: filter `Next.tree p st`; the early arm and slot-s ancestor arm both
  use retained blocks. Equal to `Next.voterBlocksNext`.
- `headVotes`: unchanged frozen arm and ordered first-occurrence merge; its proposal
  reader now retains proposals above F. Equal to `Next.headVotesNext`.
- `headSupport`: unchanged frozen arm; resolve carried heads in the cumulative base,
  then require retained-tree membership and the slot bound. Equal to `Next.headSupportNext`.
- `headVote`: keep slot zero as genesis; use `KitFG.treeStoreFrameView` for the voter
  view, with the new merges. Equal to `Next.headVoteNext`.
- `liveRoot`, `eligible`, `headInTree`, `getHead`, `propose`, `fgHead`, `fgSource`,
  `fgInputs`, and `attest`: source bodies stay fixed and use the switched readers.
  Each equals the corresponding `Next.<name>Next` reader. The inline `fgHead` support
  filter stays fixed. Run duties follow their existing canonical calls.

A temporary Lean check proves all 17 equalities, including proposal selection and
carried support. It passes with `-DwarningAsError=true`. No repository proof is edited.

## Final frame surface

The seven added import edges are exactly the seven edges in the 00b report:

1. Model Frame imports Model FrameNext.
2. Run Model Protocol imports Model FrameNext.
3. ComposeStmt imports Statements FrameNext.
4. Claims Foundations imports Statements FrameNext.
5. Claims Foundations imports Statements ComposeNext.
6. Claims Clean imports Statements ComposeNext.
7. FGSAClaims imports Claims FrameNext.

`FGFoundation.frame` uses `RFrameExactNext`. `FrameAt` is the conjunction of
`RFrameExactNext` and `RFrameNext`; `FrameClaim` follows it. `FGFoundationClaim`
concludes `FGFoundationNext`. `CleanCutPosClaim` uses that Next foundation antecedent.
`FGSASafetyClaims.frame` uses `FrameClaimNext`, and
`FGSASafetyInterfaces.fgFoundation` uses `FGFoundationClaimNext`.

Ruling A and the 00b L rows require `ChannelProps.RFrameExact`, `RFrame`, and their
_equation exports_ to keep their text. That file is therefore unchanged. These are
legacy statement forms, not the active aggregate frame interface. Their compiled
closures still change through canonical readers and the run binder; this is class B.
No other statement text changes. `FullVoteService`, `TVote`, and `KernelACSideClaim_W`
keep their text. The aggregate binder and all 48 leaf fields keep their scope and bounds.

## Measured changes and exact exceptions

The accepted original, deep, and frame baseline files and checksums are unchanged.
The current API keeps all earlier exception notes and all 1,242 entry names.
The source-census match is exact: 876 old entries plus the 21 planned Next entries.

- Deep: 897 changed roots, comprising 153 A and 744 B; 345 unchanged roots.
  The original census contributes 144 A and 732 B. Next contributes nine A and 12 B.
- Frame: five changed shallow entries out of 43: `FGFoundation.mk`,
  `FGFoundation.frame`, `FGFoundationClaim`, `FrameAt`, and `FrameClaim`.
- Shallow API: 54 changed hashes. Every old/new hash and cause is in the measured diff.
  Existing shallow allowance reasons remain; changed pins record this SWITCH revision.
- Dependency nodes: 17 changed nodes and two nodes removed from the statement closure.
  The latter are `KitFG.storeControlsView` and `KitFG.storeFrameView`; their source is
  unchanged. The new tree functions were already in the Stage 0 closure.
  `headVotes` keeps its source body; its compiled node changes after `proposalsAt`
  changes, including the kernel reducibility height recorded by the deep format.
- The six local Next frame entries have identical deep digests, as 00b requires.

`scripts/fgsa-deep-allow.json` and `scripts/fgsa-frame-allow.json` contain exact old/new
hashes, cause, census class, and plan revision. Each changed root has a measured path
and changed-node digests in the diff. Class A uses the 00b same-event store transport
argument: fixed handlers and clock preserve Node.st; changed duties affect emissions
and records. This source argument is not a new general run-transport proof.

## Validation and limits

`lake --wfail build` passes for all 84 Model/Statements/Claims targets listed in the
measured diff, and for the `AvailableChainFGSAClaims` facade: 1,128 build jobs.
This covers all FGSA and Run model files, their statements, all claim statements,
and the final aggregate. Warnings are fatal at the Lake build level.

The full target attempt uses:

```sh
lake --wfail build AvailableChainFGSA AvailableChainFGSARun \
  AvailableChainFGSAClaims AvailableChainFGSAProofs \
  AvailableChainFGSA.Tests.PortResolution AvailableChainFGSA.Tests.PortMerge
```

It fails on these three proof modules, with these first errors:

- `AvailableChainFGSA.Proofs.Port.ContestFrame`, line 17: `Type mismatch`.
  The old comparison concludes tree controls equal old store controls; canonical
  controls now denote tree controls.
- `AvailableChainFGSA.Proofs.FrameViews`, line 24: `Type mismatch`.
  `storeControls_of_bridge` supplies the old store view, not the new canonical controls.
- `AvailableChainFGSA.Proofs.Port.Resolution`, line 206: `No goals to be solved`.
  The new canonical support body closes a goal before the old proof's next tactic.

Downstream proof families and proof-dependent fixtures are blocked by these failures.
This list is the observed build frontier, not a claim that all later proofs will pass.
No proof repair is included. In particular, the pre-SWITCH Legacy equality theorems
in Port VoteMerge must be handled by their later owner.

Ready fixture expectations change in `Tests/PortResolution`, `Tests/PortMerge`, and
`Tests/Smoke`: ancestor proposer support is omitted, off-F proposals do not supply
lists, off-F voter blocks are omitted, and the off-F carried support case is empty.
The two port fixture bodies pass in temporary files with model imports only.
Their repository imports are preserved, so this is partial fixture evidence.
The Smoke module remains blocked by its proof dependencies.

The normal `V2Manifest --scope fgsa --write` command cannot load the FGSA facade:
`AvailableChainFGSA.Proofs.Port.Resolution.olean` is absent after its failed build.
The measurement therefore uses the unchanged `scan`, `familyManifest`, and
`deepSnapshot` functions from V2Manifest in a temporary harness. It imports every
one of the 57 manifest source modules directly, after the target build. This does
not load an old proof object or alter a checker. Exact root-set equality is checked
against both the complete current manifest and the accepted deep baseline.
No theorem proof body enters the measurement.

The 00c Python deep check passes on that compiled snapshot: 1,242 roots, 3,663 nodes,
897 exact exceptions. Its frame check passes: 43 entries, five exact exceptions.
The unmodified shallow `--check-frozen` command passes. The generated entry sections
match the recorded current API byte for byte. The ordinary facade-based FGSA
manifest gate is still blocked in this red window; no full manifest-gate pass is claimed.

PC-SA: `NEG=0 bash scripts/check-pcsa-manifest.sh` passes: 424 entries in 21 modules.
`python3 scripts/record-fgsa-port-pcsa-baseline.py --check` also passes: 21 source
statement files, 424 compiled roots, 2,725 dependencies. No PC-SA source changes.
Shared KitFG, GridCO, SA, the four protected FGSA representations, proof sources,
checker scripts, lake configuration, and baseline bytes have no change.

The required `precheck.sh <tree> 5dbfcb3c` passes. It is source-only evidence.
No FG-SA precheck step fails. F-13 and F-3 checks pass. No imports are removed.
Writer self-review checked the source scope, seven edges, exact census, prior
allowance reasons, protected files, and all changed hashes. No separate review,
agent, or external process for review was started. Later proof repair and the joint
WP15/WP16 gate remain required before atomic landing.

## Changed files

- `AvailableChainFGSA/Model/Frame.lean`: canonical reader switch.
- `AvailableChainFGSARun/Model/Protocol.lean`: planned direct FrameNext import.
- `AvailableChainFGSAClaims/Statements/ComposeStmt.lean`: exact Next foundation frame.
- `AvailableChainFGSAClaims/Claims/Foundations.lean`: final frame and foundation claims.
- `AvailableChainFGSAClaims/Claims/Clean.lean`: Next foundation antecedent.
- `AvailableChainFGSAClaims/FGSAClaims.lean`: final frame and interface fields.
- `AvailableChainFGSA/Tests/PortResolution.lean`: canonical prefix-filter expectations.
- `AvailableChainFGSA/Tests/PortMerge.lean`: canonical retained proposal/voter expectations.
- `AvailableChainFGSA/Tests/Smoke.lean`: canonical carried-support expectation.
- `docs/FGSA-API.md`: 54 measured hash changes; prior exception notes preserved.
- `scripts/fgsa-manifest-allow.txt`: 53 changed original-frozen pins; prior reasons preserved.
  The remaining changed API entry is the later `FGSAClaims.weakContinuationLive` field.
- `scripts/fgsa-deep-allow.json`: 897 exact exceptions.
- `scripts/fgsa-frame-allow.json`: five exact exceptions.
- `docs/reports/fgsa-port-switch-diff.json`: source hashes, kernel-node changes, root paths,
  shallow old/new values, target list, classifications, and validation results.
- `docs/reports/fgsa-port-switch.md`: this protocol-change and validation record.

## Reproduce the red-window measurement

Create a temporary Lean file from the exact V2Manifest source before its `def main`.
Append the following main. Replace `IMPORTS` with one `{ module := <Lean name> }` for
each `###` module heading in the current API, in heading order. There are 57 headings.
Run it with `lake env lean --run`. Keep all existing source imports and checker code.

```lean
def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[IMPORTS] {}
  let decls ← runCore env (scan .fgsa)
  IO.FS.writeFile ".lake/port-switch/current-api.md" (← familyManifest .fgsa env decls)
  let roots := decls.toArray.flatMap fun (_, xs) => xs.map (·.1)
  let snapshot ← deepSnapshot env roots
  IO.FS.writeFile ".lake/port-switch/current-snapshot.json" snapshot.compress
  return 0
```

Compare the generated entry sections with `docs/FGSA-API.md`; preserve its manual header.
Then run the existing checks without writing a baseline:

```sh
python3 scripts/fgsa-deep.py --frame-check
python3 scripts/fgsa-deep.py --check \
  --snapshot .lake/port-switch/current-snapshot.json
lake env lean --run scripts/V2Manifest.lean --scope fgsa --check-frozen
```

New Lean and prose lines are at most 100 characters. Fixed-format generated API rows,
exact-name JSON keys, and tab-separated allowance records retain their required format.
