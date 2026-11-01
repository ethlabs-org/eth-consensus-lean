# FG-SA port source census

**Historical record — superseded 2026-10-09.** This document records its
original source basis. Freeze rules, port totals, ownership paths, and exact
exception rows are not current acceptance data. Future changes use generated
current snapshots and reviewed diffs. Open proof obligations remain open.
The old API data remains in Git at
`6c36d4810cb070655f2f4aadb3346db6c76aa0a3`. No checker reads this record.


Checked base: `b033d223088fa30fd2763c3ae4a00b20bf28e91b` (post-P13).
Plan: [r2 and binding rulings](plans/fgsa-port-r2.md).
Source report: `codex/reports/reviews/derisk2-port-census-sol.md` in the
tip-stability research tree, SHA-256 `77c901e804964d3574561f55db1cef9493d7b33a8b7c65ef5d0eec5f41b89b5e`.
The source census matches 369/876. There is no difference to explain.
P13 changes none of the model, claim, or manifest inputs to this census.

```text
┌────────────────────────────┬───────┐
│ Item                       │ Count │
├────────────────────────────┼───────┤
│ Source declarations        │   369 │
│ Current manifest entries   │   876 │
│ Original frozen entries    │   799 │
│ Later entries              │    77 │
└────────────────────────────┴───────┘
```

A: Same-event transport preserves the read. The equality argument fixes the
same event list, inputs, seats, honest set, and environment. Clock and handlers
stay fixed. `recordOwn` changes the record only; restore resets `Node.st`
independently of that record. Induction on the event list gives equal stored
state, including proposals, votes, stamps, leases, outputs, F, J, and heights.
This is the source argument from the census report. It is not a checked lemma.

B: Meaning changes through a reader, object, witness, or run premise.
Attribute every B entry below to the single h+i+j protocol switch in r2.
There is no general implication for the complete declaration. Aggregate
constructors and projections have class B because their carrier changes;
this does not weaken an individual class-A guarantee.

C-i: Contest reads agree in a stated context. This is additional evidence,
not a change of class for the complete bare declaration. For Clean reads,
positive CleanCut gives FaultQ through `HealthyPrefix₂.faultQ_of_pos`;
CleanPrefix uses `partAt`. The Clean invariant gives compatible crossed entries,
so both contests are false; slot zero uses genesis. FaultQ alone is insufficient.
For Recovery reads, `Recovery₂.fault` gives FaultX, Base gives roots and
authentication, and RXing with the current local finality carrier and
`h_F ≤ j < H` puts the top blocks above F. Thus contest, Z, and lo agree.
Neither context needs equal honest finalized roots. These contextual records
apply to the Clean/Recovery frame consumers of the B declarations below.

Binding ruling A: `RFrameExact` and `RFrame` keep their source text and become
legacy. Their B attribution remains. `FrameNext` is the final frame surface;
it is new after this base and is not counted here. Its shallow entries remain
fixed at SWITCH, but its run dependency changes. WP00c must record the exact
pre/post deep digest exceptions before SWITCH; S0-I does not invent those values.

The records below give each affected source declaration, its base path and
line, its class, and every exact selected manifest entry. `frozen` means that
the entry name occurs in `FGSA-API-frozen.md`; it does not mean its current
hash equals the original hash. Names ending in `_def`, constructors, and
projections inherit the class of their complete source declaration.
The mechanical rule is N, public N_def if present, and all manifest names
starting with N followed by a dot. Model readers and run duties that cause
these changes are also recorded in the ownership register as census inputs.

Recheck from the repository root:

```sh
python3 scripts/recount-fgsa-port-census.py
```

The command checks the source declaration and its current line, rebuilds every
entry expansion from both manifests, rejects overlapping entries, and compares
the complete records and totals. This is a source census. WP00c must compare
it with the compiled dependency closure before SWITCH and at final closure.

## Base records and checks

The ownership register has 735 exact edit paths, with 66 marked new at this
base. It expands all local proof prerequisites, 34 Finality modules, the full
Healing split (Base: WP09a; seven phase files: WP04b; remaining 124: WP09b),
and all 99 existing proof tests. WP16 owns architecture and S0 history data;
WP00a acts as that data owner for S0-I only. New S0-D and S0-T paths have their
package owners and remain marked new until the register base is advanced.
Run the positive check and its duplicate-owner negative control with:

```sh
python3 scripts/check-fgsa-port-owners.py --selftest
```

P13 is closed by its non-null tip `b033d223` in the existing inherited-history
schema. Its old base-to-landing range also includes the main PC-SA Formation
change `edc925ff` to `Statements/Premises.lean`. That path already has exact
history in the inherited record. P13 records the same commit as
`inherited-main`, so the endpoint-range checker can verify it without treating
it as a P13 source edit. Neither S0 byte manifest was changed.

The PC-SA baseline records exact source-file SHA-256 values and compiled
statement roots from `V2Manifest --scope pcsa`. Its separate dependency graph
includes public and private constants across libraries, normalized kernel type
and definition/data value representations, and theorem types without theorem
proofs. Per-node and per-root SHA-256 values cover those representations;
they do not depend only on the existing 64-bit hashes. The extraction writes
only the baseline and a temporary probe; it reads `docs/PCSA-API.md` without
changing it. To compare a later build with this base:

```sh
python3 scripts/record-fgsa-port-pcsa-baseline.py --check
```

Use the required wrapper for this command. This PC-SA snapshot does not replace
WP00c's separate pre-SWITCH FG-SA deep baseline after all Stage 0 landings.

## Complete source-to-manifest records

```json
[
  {
    "path": "AvailableChainFGSARun/Statements/AC.lean",
    "declaration": "AvailableChain.FGSA.Run.fgsaAC",
    "line": 12,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.fgsaAC",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSARun/Statements/Acceptance.lean",
    "declaration": "AvailableChain.FGSA.Run.fgsaTrigger",
    "line": 26,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.fgsaTrigger",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSARun/Statements/Client.lean",
    "declaration": "AvailableChain.FGSA.Run.EmitsRow",
    "line": 10,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.EmitsRow",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSARun/Statements/Client.lean",
    "declaration": "AvailableChain.FGSA.Run.EmittedRowsNoSlash",
    "line": 15,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.EmittedRowsNoSlash",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSARun/Statements/Client.lean",
    "declaration": "AvailableChain.FGSA.Run.fgClientEvent",
    "line": 28,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.fgClientEvent",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSARun/Statements/Client.lean",
    "declaration": "AvailableChain.FGSA.Run.fgClientEvents",
    "line": 40,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.fgClientEvents",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSARun/Statements/Emission.lean",
    "declaration": "AvailableChain.FGSA.Run.HonestEmissionWellFormed",
    "line": 21,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HonestEmissionWellFormed",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSARun/Statements/Emission.lean",
    "declaration": "AvailableChain.FGSA.Run.HonestProposalDecodes",
    "line": 28,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HonestProposalDecodes",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSARun/Statements/Emission.lean",
    "declaration": "AvailableChain.FGSA.Run.HeadTargetAtEmission",
    "line": 39,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HeadTargetAtEmission",
        "kind": "def",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSARun/Statements/Interface.lean",
    "declaration": "AvailableChain.FGSA.Run.fgsaInterface",
    "line": 42,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.fgsaInterface",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSARun/Statements/Interface.lean",
    "declaration": "AvailableChain.FGSA.Run.fgsaOutputs",
    "line": 58,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.fgsaOutputs",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSARun/Statements/ReceiptCoverage.lean",
    "declaration": "AvailableChain.FGSA.Run.ReceiptCoveragePremises",
    "line": 29,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ReceiptCoveragePremises",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ReceiptCoveragePremises.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ReceiptCoveragePremises.within",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ReceiptCoveragePremises.slotWindow",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ReceiptCoveragePremises.compat",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ReceiptCoveragePremises.deadline",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSARun/Statements/ReceiptCoverage.lean",
    "declaration": "AvailableChain.FGSA.Run.ReceiptCoverageStatement",
    "line": 91,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ReceiptCoverageStatement",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ReceiptCoverageStatement_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSARun/Statements/Roots.lean",
    "declaration": "AvailableChain.FGSA.Run.DirectNamedProposalInRun",
    "line": 13,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.DirectNamedProposalInRun",
        "kind": "def",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSARun/Statements/Roots.lean",
    "declaration": "AvailableChain.FGSA.Run.NamedProposalInRun",
    "line": 19,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.NamedProposalInRun",
        "kind": "def",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSARun/Statements/Roots.lean",
    "declaration": "AvailableChain.FGSA.Run.NamedRootCollisionFree",
    "line": 24,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.NamedRootCollisionFree",
        "kind": "structure",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.NamedRootCollisionFree.mk",
        "kind": "ctor",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.NamedRootCollisionFree.root_injective",
        "kind": "field",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSARun/Statements/Roots.lean",
    "declaration": "AvailableChain.FGSA.Run.DirectRootBlockInRun",
    "line": 33,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.DirectRootBlockInRun",
        "kind": "def",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSARun/Statements/Roots.lean",
    "declaration": "AvailableChain.FGSA.Run.RootBlockInRun",
    "line": 37,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RootBlockInRun",
        "kind": "def",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSARun/Statements/Slashing.lean",
    "declaration": "AvailableChain.FGSA.Run.fgsaSlashing",
    "line": 26,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.fgsaSlashing",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Clean.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanGateAt",
    "line": 62,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanGateAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Clean.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanSafetyAt",
    "line": 91,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanSafetyAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Clean.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanHistoryAt",
    "line": 17,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanHistoryAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Clean.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanTruncAt",
    "line": 71,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanTruncAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Clean.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanCutClaim",
    "line": 101,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanCutClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Clean.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanCutZeroClaim",
    "line": 109,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanCutZeroClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Clean.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanHistoryClaim",
    "line": 114,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanHistoryClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Clean.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanPrefixTruncationClaim",
    "line": 119,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanPrefixTruncationClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Clean.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanSafetyClaim",
    "line": 124,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanSafetyClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Clean.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanCutPosClaim",
    "line": 133,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanCutPosClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalityLivenessConcl_W",
    "line": 51,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalityLivenessConcl_W",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.ProposalFinalConcl_W",
    "line": 69,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ProposalFinalConcl_W",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.AboveFrontierConcl_W",
    "line": 75,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.AboveFrontierConcl_W",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalityKernelClaim_W",
    "line": 17,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalityKernelClaim_W",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.KernelACSideClaim_W",
    "line": 25,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.KernelACSideClaim_W",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalityKernelJoinedClaim_W",
    "line": 33,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalityKernelJoinedClaim_W",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.TailKernelClaim_W",
    "line": 41,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TailKernelClaim_W",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.FirstFinalityConcl_W",
    "line": 62,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FirstFinalityConcl_W",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.FirstFinalityRecFEClaim_W",
    "line": 82,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FirstFinalityRecFEClaim_W",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.FirstFinalityRecF4Claim_W",
    "line": 91,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FirstFinalityRecF4Claim_W",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalityLivenessRecFEClaim_W",
    "line": 100,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalityLivenessRecFEClaim_W",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalityLivenessRecF4Claim_W",
    "line": 109,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalityLivenessRecF4Claim_W",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.ProposalFinalRecFEClaim_W",
    "line": 118,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ProposalFinalRecFEClaim_W",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.ProposalFinalRecF4Claim_W",
    "line": 128,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ProposalFinalRecF4Claim_W",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.AboveFrontierRecFEClaim_W",
    "line": 138,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.AboveFrontierRecFEClaim_W",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.AboveFrontierRecF4Claim_W",
    "line": 147,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.AboveFrontierRecF4Claim_W",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalityLivenessGSTClaim_W",
    "line": 157,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalityLivenessGSTClaim_W",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.ProposalFinalGSTClaim_W",
    "line": 171,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ProposalFinalGSTClaim_W",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.AboveFrontierGSTClaim_W",
    "line": 184,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.AboveFrontierGSTClaim_W",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.StoreAt",
    "line": 81,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.StoreAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.ActiveViewAt",
    "line": 88,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ActiveViewAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.LeaseOriginsAt",
    "line": 93,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.LeaseOriginsAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.ChainCertificatesAt",
    "line": 136,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ChainCertificatesAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.ChainCertificatesClaim",
    "line": 140,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ChainCertificatesClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.StoreClaim",
    "line": 147,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.StoreClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.ActiveViewClaim",
    "line": 154,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ActiveViewClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.LeaseOriginsClaim",
    "line": 161,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.LeaseOriginsClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.OutputNestingAt",
    "line": 195,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.OutputNestingAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.OutputNestingClaim",
    "line": 198,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.OutputNestingClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalizedMonotonicityClaim",
    "line": 334,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalizedMonotonicityClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalizedSafetyConcl",
    "line": 361,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalizedSafetyConcl",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.ClientSafeAll",
    "line": 15,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ClientSafeAll",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.ClientSafetyClaim",
    "line": 21,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ClientSafetyClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.ClientSafetyBaseClaim",
    "line": 28,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ClientSafetyBaseClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.FGFoundationClaim",
    "line": 40,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FGFoundationClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.SrcFrameAboveClaim",
    "line": 48,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.SrcFrameAboveClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.RunFGBlock",
    "line": 61,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RunFGBlock",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.CarrierAt",
    "line": 70,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CarrierAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.SourceDisciplineBaseAt",
    "line": 110,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.SourceDisciplineBaseAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.SourceDisciplineAt",
    "line": 121,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.SourceDisciplineAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.CarrierClaim",
    "line": 126,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CarrierClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.FrameAt",
    "line": 206,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FrameAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.FrameClaim",
    "line": 210,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FrameClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.SourceDisciplineBaseClaim",
    "line": 217,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.SourceDisciplineBaseClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.SourceDisciplineClaim",
    "line": 224,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.SourceDisciplineClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.RowServiceBaseClaim",
    "line": 232,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RowServiceBaseClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.RowServiceClaim",
    "line": 243,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RowServiceClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.WholeRunAccountableClaim",
    "line": 284,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.WholeRunAccountableClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.WholeRunAgreementClaim",
    "line": 294,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.WholeRunAgreementClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.EventPrefixAgreementClaim",
    "line": 305,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.EventPrefixAgreementClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.FaultCountSlashableBoundClaim",
    "line": 321,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FaultCountSlashableBoundClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.HonestNeverSlashedClaim",
    "line": 350,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HonestNeverSlashedClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalizedSafetyClaim",
    "line": 371,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalizedSafetyClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Foundations.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalLockClaim",
    "line": 384,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalLockClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Healing.lean",
    "declaration": "AvailableChain.FGSA.Run.RowPermissionAt",
    "line": 14,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RowPermissionAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Healing.lean",
    "declaration": "AvailableChain.FGSA.Run.RowPermissionClaim",
    "line": 28,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RowPermissionClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Healing.lean",
    "declaration": "AvailableChain.FGSA.Run.HealingInputClaim",
    "line": 36,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HealingInputClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Healing.lean",
    "declaration": "AvailableChain.FGSA.Run.HTimeConcl",
    "line": 44,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HTimeConcl",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Healing.lean",
    "declaration": "AvailableChain.FGSA.Run.HTimeClaim",
    "line": 52,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HTimeClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Healing.lean",
    "declaration": "AvailableChain.FGSA.Run.ResetArrivalConcl",
    "line": 60,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ResetArrivalConcl",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Healing.lean",
    "declaration": "AvailableChain.FGSA.Run.ResetArrivalClaim",
    "line": 66,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ResetArrivalClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Healing.lean",
    "declaration": "AvailableChain.FGSA.Run.RenewedPromotionConcl",
    "line": 76,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RenewedPromotionConcl",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Healing.lean",
    "declaration": "AvailableChain.FGSA.Run.RenewedPromotionClaim",
    "line": 100,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RenewedPromotionClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Healing.lean",
    "declaration": "AvailableChain.FGSA.Run.HTimeBestClaim",
    "line": 111,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HTimeBestClaim",
        "kind": "def",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Healing.lean",
    "declaration": "AvailableChain.FGSA.Run.HTimeSearchClaim",
    "line": 125,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HTimeSearchClaim",
        "kind": "def",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Outage.lean",
    "declaration": "AvailableChain.FGSA.Run.InclusionPostGateAt",
    "line": 52,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.InclusionPostGateAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Outage.lean",
    "declaration": "AvailableChain.FGSA.Run.InclusionAt",
    "line": 62,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.InclusionAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Outage.lean",
    "declaration": "AvailableChain.FGSA.Run.FCompatBefore",
    "line": 101,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FCompatBefore",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Outage.lean",
    "declaration": "AvailableChain.FGSA.Run.ExactProposalAt",
    "line": 27,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ExactProposalAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Outage.lean",
    "declaration": "AvailableChain.FGSA.Run.ExactProposalClaim",
    "line": 42,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ExactProposalClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Outage.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanInclusionPostGateClaim",
    "line": 72,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanInclusionPostGateClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Outage.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanInclusionClaim",
    "line": 82,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanInclusionClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Outage.lean",
    "declaration": "AvailableChain.FGSA.Run.DutiesExtendOn",
    "line": 92,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.DutiesExtendOn",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Outage.lean",
    "declaration": "AvailableChain.FGSA.Run.P1Concl",
    "line": 110,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.P1Concl",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Outage.lean",
    "declaration": "AvailableChain.FGSA.Run.LeaseOrFFrom",
    "line": 124,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.LeaseOrFFrom",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Outage.lean",
    "declaration": "AvailableChain.FGSA.Run.OutageCompatAt",
    "line": 136,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.OutageCompatAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Outage.lean",
    "declaration": "AvailableChain.FGSA.Run.OutageCompatClaim",
    "line": 148,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.OutageCompatClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Outage.lean",
    "declaration": "AvailableChain.FGSA.Run.FastP1Claim",
    "line": 158,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FastP1Claim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Outage.lean",
    "declaration": "AvailableChain.FGSA.Run.SlowP1Claim",
    "line": 168,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.SlowP1Claim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Outage.lean",
    "declaration": "AvailableChain.FGSA.Run.AvailableFromConcl",
    "line": 176,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.AvailableFromConcl",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Outage.lean",
    "declaration": "AvailableChain.FGSA.Run.AvailableGrowthConcl",
    "line": 187,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.AvailableGrowthConcl",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Outage.lean",
    "declaration": "AvailableChain.FGSA.Run.AvailableGSTClaim",
    "line": 204,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.AvailableGSTClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Outage.lean",
    "declaration": "AvailableChain.FGSA.Run.AvailableGrowthGSTClaim",
    "line": 220,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.AvailableGrowthGSTClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Outage.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanGrowthClaim",
    "line": 238,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanGrowthClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/OutageContinuation.lean",
    "declaration": "AvailableChain.FGSA.Run.OutageContinuationClaim",
    "line": 10,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.OutageContinuationClaim",
        "kind": "def",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Shared.lean",
    "declaration": "AvailableChain.FGSA.Run.SameLabelAt",
    "line": 15,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.SameLabelAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Shared.lean",
    "declaration": "AvailableChain.FGSA.Run.SameLabelClaim",
    "line": 21,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.SameLabelClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Shared.lean",
    "declaration": "AvailableChain.FGSA.Run.HeadReachesLoAt",
    "line": 29,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HeadReachesLoAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Shared.lean",
    "declaration": "AvailableChain.FGSA.Run.HeadReachesLoClaim",
    "line": 42,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HeadReachesLoClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Shared.lean",
    "declaration": "AvailableChain.FGSA.Run.ReleaseAt",
    "line": 74,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ReleaseAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/Shared.lean",
    "declaration": "AvailableChain.FGSA.Run.ReleaseClaim",
    "line": 87,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ReleaseClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/WeakContinuation.lean",
    "declaration": "AvailableChain.FGSA.Run.WeakContinuationClaim",
    "line": 13,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.WeakContinuationClaim",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/WeakContinuation.lean",
    "declaration": "AvailableChain.FGSA.Run.WeakContinuationLiveClaim",
    "line": 24,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.WeakContinuationLiveClaim",
        "kind": "def",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Claims/WeakContinuationGrowth.lean",
    "declaration": "AvailableChain.FGSA.Run.WeakContinuationGrowthClaim",
    "line": 11,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.WeakContinuationGrowthClaim",
        "kind": "def",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/FGSAClaims.lean",
    "declaration": "AvailableChain.FGSA.Run.FGSASafetyClaims",
    "line": 22,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims.carrier",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims.chainCertificates",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims.store",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims.activeView",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims.leaseOrigins",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims.reconcile",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims.outputNesting",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims.frame",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims.clientSafety",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims.clientSafetyBase",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims.sourceDisciplineBase",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims.sourceDiscipline",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims.sameLabel",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims.releaseStore",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims.release",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims.headReachesLo",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims.cleanCut",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims.cleanHistory",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims.cleanPrefixTruncation",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyClaims.cleanSafety",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/FGSAClaims.lean",
    "declaration": "AvailableChain.FGSA.Run.FGSASafetyInterfaces",
    "line": 45,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyInterfaces",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyInterfaces.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyInterfaces.fgFoundation",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyInterfaces.srcFrameAbove",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyInterfaces.cpPrefix",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyInterfaces.cpCompat",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyInterfaces.tSrc",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyInterfaces.labelBound",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSASafetyInterfaces.timingContract",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/FGSAClaims.lean",
    "declaration": "AvailableChain.FGSA.Run.FGSAFinalityClaims",
    "line": 79,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FGSAFinalityClaims",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAFinalityClaims.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAFinalityClaims.accountable",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAFinalityClaims.agreement",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAFinalityClaims.runAccountable",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAFinalityClaims.runAgreement",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAFinalityClaims.eventPrefixAgreement",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAFinalityClaims.faultCountSlashableBound",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAFinalityClaims.finalizedMonotone",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAFinalityClaims.honestNeverSlashed",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/FGSAClaims.lean",
    "declaration": "AvailableChain.FGSA.Run.FGSAClaims",
    "line": 91,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.toFGSASafetyClaims",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.finality",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.finalizedSafety",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.finalLock",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.outageCompat",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.fastP1",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.slowP1",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.exactProposal",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.cleanInclusionPostGate",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.cleanInclusion",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.firstFinalityRecFE",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.firstFinalityRecF4",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.finalityLivenessGSTRecFE",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.finalityLivenessGSTRecF4",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.proposalFinalGSTRecFE",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.proposalFinalGSTRecF4",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.aboveFrontierGSTRecFE",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.aboveFrontierGSTRecF4",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.availableGST",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.availableGrowthGST",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.cleanGrowth",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGSAClaims.weakContinuationLive",
        "kind": "field",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.RStore",
    "line": 35,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RStore",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.RStore_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.RActive",
    "line": 68,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RActive",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.RActive_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.RStoreCumul",
    "line": 102,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RStoreCumul",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.RStoreCumul_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.RMono",
    "line": 122,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RMono",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.RMono_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.RGeo",
    "line": 272,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RGeo",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.RGeo_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.RCert",
    "line": 300,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RCert",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.RCert_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.RRec",
    "line": 349,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RRec",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.RRec_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.RXing",
    "line": 701,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RXing",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.RCarrierView",
    "line": 23,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RCarrierView",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.RCarrierView_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.RFrameExact",
    "line": 141,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RFrameExact",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.RFrameExact_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.RFrame",
    "line": 160,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RFrame",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.RFrame_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.TSrc",
    "line": 396,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TSrc",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TSrc_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.LabelBound",
    "line": 417,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.LabelBound",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.LabelBound_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.TChain",
    "line": 437,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TChain",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TChain_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.TCompat",
    "line": 462,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TCompat",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TCompat_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.RStrat",
    "line": 497,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RStrat",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.RStrat_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.RQCOrigin",
    "line": 518,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RQCOrigin",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.RQCOrigin_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.SrcFrameAbove",
    "line": 594,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.SrcFrameAbove",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.SrcFrameAbove_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.SrcFrame",
    "line": 618,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.SrcFrame",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.SrcFrameAboveStmt",
    "line": 624,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.SrcFrameAboveStmt",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.SrcFrameAboveStmt_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.CPPrefix",
    "line": 636,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CPPrefix",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CPPrefix_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.CPCompat",
    "line": 659,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CPCompat",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CPCompat_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.RCap",
    "line": 710,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RCap",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.THigh",
    "line": 719,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.THigh",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.TCarrier",
    "line": 728,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TCarrier",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.TRowsSelect",
    "line": 740,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TRowsSelect",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.TRowsSync",
    "line": 752,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TRowsSync",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.TRowsReceipt",
    "line": 764,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TRowsReceipt",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TRowsReceipt_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.TRows",
    "line": 782,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TRows",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TRows.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TRows.select",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TRows.sync",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TRows.receipt",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.SourceBefore",
    "line": 790,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.SourceBefore",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.Kept",
    "line": 797,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.Kept",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.KeepOrCause",
    "line": 804,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.KeepOrCause",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.RExcl",
    "line": 815,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RExcl",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.RKeep",
    "line": 827,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RKeep",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.RFProv",
    "line": 852,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RFProv",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.TDel",
    "line": 869,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TDel",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.TDelReset",
    "line": 880,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TDelReset",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.TGeom",
    "line": 888,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TGeom",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.ExactService",
    "line": 897,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ExactService",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.PhaseInterval",
    "line": 917,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.PhaseInterval",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.Transfers",
    "line": 928,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.Transfers",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.PhaseBody",
    "line": 939,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.PhaseBody",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.TPerm",
    "line": 951,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TPerm",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.ProposalGap",
    "line": 959,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ProposalGap",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.RepairAfter",
    "line": 966,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RepairAfter",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.TRepair",
    "line": 974,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TRepair",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.OpeningCovered",
    "line": 997,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.OpeningCovered",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.OpeningEntry",
    "line": 1008,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.OpeningEntry",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.TCommon",
    "line": 1015,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TCommon",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.TFrontier",
    "line": 1041,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TFrontier",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ChannelProps.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalityRowCarriage",
    "line": 1070,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalityRowCarriage",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityRowCarriage_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.FAdvanceAt",
    "line": 109,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FAdvanceAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.candidatesAt",
    "line": 114,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.candidatesAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.RowSigner",
    "line": 137,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RowSigner",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.RowSigner_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.RowComplete",
    "line": 151,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RowComplete",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.RowComplete_def",
        "kind": "theorem",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.HeldAt",
    "line": 162,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HeldAt",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HeldAt_def",
        "kind": "theorem",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.BlockInRunBefore",
    "line": 166,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.BlockInRunBefore",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.proposalStateAt",
    "line": 187,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.proposalStateAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.heldAtProposal",
    "line": 192,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.heldAtProposal",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.onParentChain",
    "line": 196,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.onParentChain",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.HeldBefore",
    "line": 200,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HeldBefore",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.ValidForParent",
    "line": 204,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ValidForParent",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ValidForParent_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.HeightMatch",
    "line": 218,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HeightMatch",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HeightMatch_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.frameR",
    "line": 46,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.frameR",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.frameR_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.domainR",
    "line": 49,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.domainR",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.domainR_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.jointSource",
    "line": 65,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.jointSource",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.jointSource_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.proposerHead",
    "line": 70,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.proposerHead",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.proposerHead_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.R_at",
    "line": 106,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.R_at",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.D_at",
    "line": 107,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.D_at",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.proposalHeadAt",
    "line": 118,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.proposalHeadAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.actionHead",
    "line": 121,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.actionHead",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.actionTriple",
    "line": 123,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.actionTriple",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.HonestRowAt",
    "line": 141,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HonestRowAt",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HonestRowAt_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.HonestRowBefore",
    "line": 144,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HonestRowBefore",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HonestRowBefore_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.HonestCarrier",
    "line": 155,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HonestCarrier",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HonestCarrier_def",
        "kind": "theorem",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Channels.lean",
    "declaration": "AvailableChain.FGSA.Run.headAtLabel",
    "line": 236,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.headAtLabel",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.windowIdx",
    "line": 19,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.windowIdx",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.WalkBatch",
    "line": 105,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.WalkBatch",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.frontierAtIdx",
    "line": 319,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.frontierAtIdx",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.TopEvidence",
    "line": 323,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TopEvidence",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.TimingContract",
    "line": 30,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TimingContract",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TimingContract.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TimingContract.rowLag",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TimingContract.certLag",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TimingContract.label",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TimingContract.atomic",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TimingContract.tickFG",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.FGFoundation",
    "line": 44,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FGFoundation",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGFoundation.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGFoundation.store",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGFoundation.cumul",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGFoundation.mono",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGFoundation.frame",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGFoundation.geo",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGFoundation.strat",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FGFoundation.reconcile",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.TStart",
    "line": 60,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TStart",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.FullVoteService",
    "line": 71,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FullVoteService",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.TVote",
    "line": 87,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TVote",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.TWalk",
    "line": 117,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TWalk",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.CoreServices",
    "line": 134,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CoreServices",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CoreServices.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CoreServices.start",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CoreServices.vote",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CoreServices.walk",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.ResetArrivalStatement",
    "line": 160,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ResetArrivalStatement",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ResetArrivalStatement_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.ResetArrivalFullStatement",
    "line": 181,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ResetArrivalFullStatement",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ResetArrivalFullStatement_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.kernelStart",
    "line": 207,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.kernelStart",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.OpeningCarrier_W",
    "line": 213,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.OpeningCarrier_W",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.OpeningCarrier_W_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.KernelConclusion_W",
    "line": 233,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.KernelConclusion_W",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.KernelConclusion_W_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.KernelPrem_W",
    "line": 259,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.KernelPrem_W",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.KernelPrem_W.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.KernelPrem_W.set",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.KernelPrem_W.bound",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.KernelPrem_W.window",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.KernelPrem_W.start",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.KernelPrem_W.hhor",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.KernelPrem_W.input",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.KernelPrem_W.services",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.TailKernelPrem_W",
    "line": 284,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TailKernelPrem_W",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TailKernelPrem_W.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TailKernelPrem_W.set",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TailKernelPrem_W.bound",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TailKernelPrem_W.input",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TailKernelPrem_W.start",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TailKernelPrem_W.window",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TailKernelPrem_W.carrier",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TailKernelPrem_W.high",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TailKernelPrem_W.cover",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TailKernelPrem_W.hhor",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.HealTContract",
    "line": 306,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HealTContract",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealTContract.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealTContract.del",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealTContract.delReset",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealTContract.perm",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealTContract.repair",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealTContract.common",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealTContract.frontier",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealTContract.geom",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.ContestEvidence",
    "line": 328,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ContestEvidence",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.EffectiveEvent",
    "line": 333,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.EffectiveEvent",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.AttemptPhaseAt",
    "line": 341,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.AttemptPhaseAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.ServedFrontier",
    "line": 349,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ServedFrontier",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.AttemptValid",
    "line": 358,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.AttemptValid",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.AttemptEndsBy",
    "line": 383,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.AttemptEndsBy",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.SettledPhaseFrame",
    "line": 399,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.SettledPhaseFrame",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.SettledPhaseFrame_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.RPhase",
    "line": 453,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RPhase",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.RPhase_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.HealRContract",
    "line": 555,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HealRContract",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealRContract.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealRContract.xing",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealRContract.cap",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealRContract.phase",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealRContract.excl",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealRContract.keep",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealRContract.fprov",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/ComposeStmt.lean",
    "declaration": "AvailableChain.FGSA.Run.ProgressAttemptStatement",
    "line": 584,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ProgressAttemptStatement",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ProgressAttemptStatement_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/FinalityApi.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalityExecution",
    "line": 93,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalityExecution",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityExecution_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/FinalityApi.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalityBlock",
    "line": 36,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalityBlock",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityBlock_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/FinalityApi.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalitySlashableBound",
    "line": 76,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalitySlashableBound",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalitySlashableBound_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/FinalityApi.lean",
    "declaration": "AvailableChain.FGSA.Run.WholeRunAccountable",
    "line": 109,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.WholeRunAccountable",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.WholeRunAccountable_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/FinalityApi.lean",
    "declaration": "AvailableChain.FGSA.Run.WholeRunAgreement",
    "line": 150,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.WholeRunAgreement",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.WholeRunAgreement_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Fold.lean",
    "declaration": "AvailableChain.FGSA.Run.honestSeats",
    "line": 133,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.honestSeats",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.honestSeats_def",
        "kind": "theorem",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Fold.lean",
    "declaration": "AvailableChain.FGSA.Run.ChainRowsBefore",
    "line": 160,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ChainRowsBefore",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Fold.lean",
    "declaration": "AvailableChain.FGSA.Run.PreBatchPrem",
    "line": 170,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.PreBatchPrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.PreBatchPrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.PreBatchPrem.base",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.PreBatchPrem.faultQ",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.PreBatchPrem.entry",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.PreBatchPrem.path",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.PreBatchPrem.cut",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.PreBatchPrem.early",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.PreBatchPrem.rows",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.PreBatchPrem.noRow",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Fold.lean",
    "declaration": "AvailableChain.FGSA.Run.NoMixedPreBatchParent",
    "line": 194,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.NoMixedPreBatchParent",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Fold.lean",
    "declaration": "AvailableChain.FGSA.Run.BatchPrem",
    "line": 203,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.BatchPrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BatchPrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BatchPrem.base",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BatchPrem.faultQ",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BatchPrem.deltaF",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BatchPrem.rowsReceipt",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BatchPrem.horizon",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BatchPrem.carrier",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BatchPrem.after",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BatchPrem.valid",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BatchPrem.entry",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BatchPrem.path",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BatchPrem.above",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Fold.lean",
    "declaration": "AvailableChain.FGSA.Run.BatchCoverage",
    "line": 241,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.BatchCoverage",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Fold.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalityBatchPrem_W",
    "line": 302,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalityBatchPrem_W",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityBatchPrem_W.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityBatchPrem_W.base",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityBatchPrem_W.faultQ",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityBatchPrem_W.deltaF",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityBatchPrem_W.rowsReceipt",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityBatchPrem_W.carrier",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityBatchPrem_W.after",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityBatchPrem_W.horizon",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityBatchPrem_W.parent",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityBatchPrem_W.birth",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityBatchPrem_W.retainedOrCovered",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityBatchPrem_W.batch",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Fold.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalityBatchCoverage_W",
    "line": 331,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalityBatchCoverage_W",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityBatchCoverage_W_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Healed.lean",
    "declaration": "AvailableChain.FGSA.Run.healStart",
    "line": 24,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.healStart",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.healStart_def",
        "kind": "theorem",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Healed.lean",
    "declaration": "AvailableChain.FGSA.Run.HealSuffix",
    "line": 29,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HealSuffix",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealSuffix_def",
        "kind": "theorem",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Healed.lean",
    "declaration": "AvailableChain.FGSA.Run.Healed",
    "line": 41,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.Healed",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Healed.lean",
    "declaration": "AvailableChain.FGSA.Run.H2A",
    "line": 60,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.H2A",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Healed.lean",
    "declaration": "AvailableChain.FGSA.Run.H2Prime",
    "line": 69,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.H2Prime",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Healed.lean",
    "declaration": "AvailableChain.FGSA.Run.H3",
    "line": 76,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.H3",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Healed.lean",
    "declaration": "AvailableChain.FGSA.Run.H4",
    "line": 80,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.H4",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Healed.lean",
    "declaration": "AvailableChain.FGSA.Run.H5RawTransfer",
    "line": 89,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.H5RawTransfer",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Healed.lean",
    "declaration": "AvailableChain.FGSA.Run.H6GateService",
    "line": 100,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.H6GateService",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Healed.lean",
    "declaration": "AvailableChain.FGSA.Run.HealT",
    "line": 114,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HealT",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealT.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealT.h1",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealT.h2",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealT.rows",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Healed.lean",
    "declaration": "AvailableChain.FGSA.Run.HealAC",
    "line": 119,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HealAC",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealAC.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealAC.h2A",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealAC.h2'",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealAC.h3",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealAC.h4",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealAC.h5",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealAC.h6",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Healed.lean",
    "declaration": "AvailableChain.FGSA.Run.HealingInput",
    "line": 142,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HealingInput",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealingInput.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealingInput.healed",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealingInput.wit",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealingInput.t",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealingInput.ac",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Healed.lean",
    "declaration": "AvailableChain.FGSA.Run.HTimeStatement",
    "line": 151,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HTimeStatement",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HTimeStatement_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/HealedBest.lean",
    "declaration": "AvailableChain.FGSA.Run.HTimeBestConcl",
    "line": 12,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HTimeBestConcl",
        "kind": "def",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.HTimeBestConcl_def",
        "kind": "theorem",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/LiveDC.lean",
    "declaration": "AvailableChain.FGSA.Run.LiveDCConcl_W",
    "line": 22,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.LiveDCConcl_W",
        "kind": "def",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.LiveDCConcl_W_def",
        "kind": "theorem",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/LiveDC.lean",
    "declaration": "AvailableChain.FGSA.Run.LiveDCFromWindowsStatement",
    "line": 46,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.LiveDCFromWindowsStatement",
        "kind": "def",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.LiveDCFromWindowsStatement_def",
        "kind": "theorem",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/OutageContinuation.lean",
    "declaration": "AvailableChain.FGSA.Run.OutageContinuationConcl",
    "line": 39,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.OutageContinuationConcl",
        "kind": "def",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/OutageContinuation.lean",
    "declaration": "AvailableChain.FGSA.Run.OutageContinuationPrem",
    "line": 20,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.OutageContinuationPrem",
        "kind": "structure",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.OutageContinuationPrem.mk",
        "kind": "ctor",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.OutageContinuationPrem.pre",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.OutageContinuationPrem.sleepy",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.OutageContinuationPrem.order",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.OutageContinuationPrem.lag",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.OutageContinuationPrem.lengthV",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.OutageContinuationPrem.fastPart",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.OutageContinuationPrem.sync",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.OutageContinuationPrem.gst",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.OutageContinuationPrem.partAfter",
        "kind": "field",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/OutputReads.lean",
    "declaration": "AvailableChain.FGSA.Run.ServedFromGateAt",
    "line": 19,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ServedFromGateAt",
        "kind": "def",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.ServedFromGateAt_def",
        "kind": "theorem",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/OutputReads.lean",
    "declaration": "AvailableChain.FGSA.Run.JointGrowthAt",
    "line": 38,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.JointGrowthAt",
        "kind": "def",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.JointGrowthAt_def",
        "kind": "theorem",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalitySet_W",
    "line": 31,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalitySet_W",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalitySet_W.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalitySet_W.core",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalitySet_W.bound",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalitySet_W.recur",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.FirstFinalityPrem_W",
    "line": 46,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FirstFinalityPrem_W",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FirstFinalityPrem_W.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FirstFinalityPrem_W.set",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FirstFinalityPrem_W.hhor",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalityLivenessPrem_W",
    "line": 53,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalityLivenessPrem_W",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityLivenessPrem_W.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityLivenessPrem_W.set",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityLivenessPrem_W.input",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityLivenessPrem_W.start",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityLivenessPrem_W.hhor",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.ProposalFinalPrem_W",
    "line": 62,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ProposalFinalPrem_W",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ProposalFinalPrem_W.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ProposalFinalPrem_W.set",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ProposalFinalPrem_W.input",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ProposalFinalPrem_W.prop",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ProposalFinalPrem_W.start",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ProposalFinalPrem_W.hhor",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Finality.lean",
    "declaration": "AvailableChain.FGSA.Run.AboveFrontierPrem_W",
    "line": 73,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.AboveFrontierPrem_W",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AboveFrontierPrem_W.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AboveFrontierPrem_W.set",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AboveFrontierPrem_W.input",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AboveFrontierPrem_W.start",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AboveFrontierPrem_W.firstHorizon",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AboveFrontierPrem_W.hhor",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/FinalityGST.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W",
    "line": 14,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.set",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.late",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.hhor",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/FinalityGST.lean",
    "declaration": "AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W",
    "line": 24,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.set",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.prop",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.late",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.hhor",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/FinalityGST.lean",
    "declaration": "AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W",
    "line": 37,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.set",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.late",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.hhor",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Healing.lean",
    "declaration": "AvailableChain.FGSA.Run.HealingPrem",
    "line": 30,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HealingPrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealingPrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealingPrem.set",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealingPrem.bound",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Healing.lean",
    "declaration": "AvailableChain.FGSA.Run.HealingWitnessPrem",
    "line": 37,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HealingWitnessPrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealingWitnessPrem.toHealingPrem",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealingWitnessPrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealingWitnessPrem.h0",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Healing.lean",
    "declaration": "AvailableChain.FGSA.Run.HealingTimePrem",
    "line": 43,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HealingTimePrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealingTimePrem.toHealingPrem",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealingTimePrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealingTimePrem.hhor",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Healing.lean",
    "declaration": "AvailableChain.FGSA.Run.ResetArrivalPrem",
    "line": 50,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ResetArrivalPrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ResetArrivalPrem.toHealingPrem",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ResetArrivalPrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ResetArrivalPrem.hhor",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Healing.lean",
    "declaration": "AvailableChain.FGSA.Run.ResetArrivalFullPrem",
    "line": 57,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ResetArrivalFullPrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ResetArrivalFullPrem.toHealingPrem",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ResetArrivalFullPrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ResetArrivalFullPrem.hhor",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Healing.lean",
    "declaration": "AvailableChain.FGSA.Run.KernelJoinedPrem",
    "line": 65,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.KernelJoinedPrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.KernelJoinedPrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.KernelJoinedPrem.set",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.KernelJoinedPrem.bound",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.KernelJoinedPrem.window",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.KernelJoinedPrem.start",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.KernelJoinedPrem.hhor",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Healing.lean",
    "declaration": "AvailableChain.FGSA.Run.HealingAttemptPrem",
    "line": 79,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HealingAttemptPrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealingAttemptPrem.toHealingPrem",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealingAttemptPrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealingAttemptPrem.valid",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealingAttemptPrem.hhor",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Healing.lean",
    "declaration": "AvailableChain.FGSA.Run.HealingInputPrem",
    "line": 87,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HealingInputPrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealingInputPrem.toHealingWitnessPrem",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealingInputPrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealingInputPrem.hhor",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Healing.lean",
    "declaration": "AvailableChain.FGSA.Run.RenewedPromotionPrem",
    "line": 93,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RenewedPromotionPrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.RenewedPromotionPrem.toHealingPrem",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.RenewedPromotionPrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.RenewedPromotionPrem.hhor",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Inclusion.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanInclusionPrem",
    "line": 15,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanInclusionPrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanInclusionPrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanInclusionPrem.set",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanInclusionPrem.prop",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanInclusionPrem.hhor",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Inclusion.lean",
    "declaration": "AvailableChain.FGSA.Run.ExactProposalPrem",
    "line": 26,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ExactProposalPrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ExactProposalPrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ExactProposalPrem.set",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ExactProposalPrem.prop",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ExactProposalPrem.hhor",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Outage.lean",
    "declaration": "AvailableChain.FGSA.Run.OutagePrem",
    "line": 12,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.OutagePrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.OutagePrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.OutagePrem.set",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Safety.lean",
    "declaration": "AvailableChain.FGSA.Run.BasePrem",
    "line": 21,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.BasePrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BasePrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BasePrem.set",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Safety.lean",
    "declaration": "AvailableChain.FGSA.Run.SameLabelPrem",
    "line": 28,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.SameLabelPrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.SameLabelPrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.SameLabelPrem.set",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.SameLabelPrem.sync",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Safety.lean",
    "declaration": "AvailableChain.FGSA.Run.SourceDisciplinePrem",
    "line": 34,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.SourceDisciplinePrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.SourceDisciplinePrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.SourceDisciplinePrem.set",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.SourceDisciplinePrem.quorum",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Safety.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalizedSafetyPrem",
    "line": 39,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalizedSafetyPrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalizedSafetyPrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalizedSafetyPrem.set",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalizedSafetyPrem.fault",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Safety.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanPrem",
    "line": 47,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanPrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanPrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanPrem.set",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Safety.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanPrefixPrem",
    "line": 54,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanPrefixPrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanPrefixPrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanPrefixPrem.set",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Safety.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanCutPrem",
    "line": 61,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanCutPrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanCutPrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanCutPrem.set",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Packages/Safety.lean",
    "declaration": "AvailableChain.FGSA.Run.ReleasePrem",
    "line": 66,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.ReleasePrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ReleasePrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ReleasePrem.set",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.ReleasePrem.lt",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Phases.lean",
    "declaration": "AvailableChain.FGSA.Run.Ready_W",
    "line": 80,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.Ready_W",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Ready_W_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Phases.lean",
    "declaration": "AvailableChain.FGSA.Run.receiptInsert_W",
    "line": 93,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.receiptInsert_W",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.receiptInsert_W_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Phases.lean",
    "declaration": "AvailableChain.FGSA.Run.BlockDelivery_W",
    "line": 111,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.BlockDelivery_W",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BlockDelivery_W.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BlockDelivery_W.selected",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BlockDelivery_W.witness",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Phases.lean",
    "declaration": "AvailableChain.FGSA.Run.AcceptGuards_W",
    "line": 127,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.AcceptGuards_W",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AcceptGuards_W.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AcceptGuards_W.finCmp",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AcceptGuards_W.jPath",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AcceptGuards_W.cap",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Phases.lean",
    "declaration": "AvailableChain.FGSA.Run.FreshPrem",
    "line": 22,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FreshPrem",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FreshPrem.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FreshPrem.base",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FreshPrem.faultQ",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FreshPrem.cut",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FreshPrem.early",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FreshPrem.rows",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FreshPrem.noNextRow",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FreshPrem.noFinRow",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Phases.lean",
    "declaration": "AvailableChain.FGSA.Run.JustifyFresh_W",
    "line": 65,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.JustifyFresh_W",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.JustifyFresh_W_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Phases.lean",
    "declaration": "AvailableChain.FGSA.Run.AcceptPrem_W",
    "line": 155,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.AcceptPrem_W",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AcceptPrem_W.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AcceptPrem_W.base",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AcceptPrem_W.faultBound",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AcceptPrem_W.finalized",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AcceptPrem_W.deliver",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AcceptPrem_W.guards",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AcceptPrem_W.horizon",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Phases.lean",
    "declaration": "AvailableChain.FGSA.Run.AcceptBefore_W",
    "line": 182,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.AcceptBefore_W",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AcceptBefore_W_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Phases.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalizePrem_W",
    "line": 192,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalizePrem_W",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalizePrem_W.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalizePrem_W.fold",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalizePrem_W.base",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalizePrem_W.faultBound",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalizePrem_W.deliver",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalizePrem_W.guards",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalizePrem_W.horizon",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Phases.lean",
    "declaration": "AvailableChain.FGSA.Run.FinalizePending_W",
    "line": 219,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FinalizePending_W",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FinalizePending_W_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Phases.lean",
    "declaration": "AvailableChain.FGSA.Run.FreshFinalityRows_W",
    "line": 295,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.FreshFinalityRows_W",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.FreshFinalityRows_W_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Phases.lean",
    "declaration": "AvailableChain.FGSA.Run.TerminalCarriagePrem_W",
    "line": 311,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TerminalCarriagePrem_W",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TerminalCarriagePrem_W.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TerminalCarriagePrem_W.base",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TerminalCarriagePrem_W.faultQ",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TerminalCarriagePrem_W.deltaF",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TerminalCarriagePrem_W.carrier",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TerminalCarriagePrem_W.parent",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TerminalCarriagePrem_W.path",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TerminalCarriagePrem_W.freshHeight",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TerminalCarriagePrem_W.retainedOrCovered",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TerminalCarriagePrem_W.horizon",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TerminalCarriagePrem_W.seats",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TerminalCarriagePrem_W.rows",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TerminalCarriagePrem_W.fresh",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TerminalCarriagePrem_W.heightEntry",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TerminalCarriagePrem_W.receipt",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Phases.lean",
    "declaration": "AvailableChain.FGSA.Run.TerminalCarriage_W",
    "line": 343,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.TerminalCarriage_W",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.TerminalCarriage_W_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Reads.lean",
    "declaration": "AvailableChain.FGSA.Run.storeAt",
    "line": 78,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.storeAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Reads.lean",
    "declaration": "AvailableChain.FGSA.Run.S_at",
    "line": 81,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.S_at",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.S_at_def",
        "kind": "theorem",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Reads.lean",
    "declaration": "AvailableChain.FGSA.Run.F_at",
    "line": 82,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.F_at",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Reads.lean",
    "declaration": "AvailableChain.FGSA.Run.J_at",
    "line": 83,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.J_at",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Reads.lean",
    "declaration": "AvailableChain.FGSA.Run.gateIn",
    "line": 87,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.gateIn",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.gateIn_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Reads.lean",
    "declaration": "AvailableChain.FGSA.Run.gateResult",
    "line": 100,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.gateResult",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.gateResult_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Reads.lean",
    "declaration": "AvailableChain.FGSA.Run.IsGateTick",
    "line": 124,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.IsGateTick",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Reads.lean",
    "declaration": "AvailableChain.FGSA.Run.gateResultAt",
    "line": 129,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.gateResultAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Reads.lean",
    "declaration": "AvailableChain.FGSA.Run.gatePassedAt",
    "line": 141,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.gatePassedAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Reads.lean",
    "declaration": "AvailableChain.FGSA.Run.fastAt",
    "line": 150,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.fastAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Reads.lean",
    "declaration": "AvailableChain.FGSA.Run.labelBoundAt",
    "line": 190,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.labelBoundAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Reads.lean",
    "declaration": "AvailableChain.FGSA.Run.DeliveredAt",
    "line": 195,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.DeliveredAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Reads.lean",
    "declaration": "AvailableChain.FGSA.Run.HandlesRowAt",
    "line": 200,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HandlesRowAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Reads.lean",
    "declaration": "AvailableChain.FGSA.Run.AcceptsFinalBefore",
    "line": 205,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.AcceptsFinalBefore",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Reads.lean",
    "declaration": "AvailableChain.FGSA.Run.cleanResults",
    "line": 210,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.cleanResults",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Reads.lean",
    "declaration": "AvailableChain.FGSA.Run.BelowLabel",
    "line": 216,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.BelowLabel",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Reads.lean",
    "declaration": "AvailableChain.FGSA.Run.headAtIdx",
    "line": 156,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.headAtIdx",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Reads.lean",
    "declaration": "AvailableChain.FGSA.Run.vHead",
    "line": 163,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.vHead",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.vHead_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Reads.lean",
    "declaration": "AvailableChain.FGSA.Run.actionSourceFG",
    "line": 176,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.actionSourceFG",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.actionSourceFG_def",
        "kind": "theorem",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Reads.lean",
    "declaration": "AvailableChain.FGSA.Run.actionSource",
    "line": 185,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.actionSource",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Regimes.lean",
    "declaration": "AvailableChain.FGSA.Run.AwakeProposerRecurrenceFrom",
    "line": 98,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.AwakeProposerRecurrenceFrom",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Regimes.lean",
    "declaration": "AvailableChain.FGSA.Run.Base₂",
    "line": 18,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.Base₂",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Base₂.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Base₂.valid",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Base₂.linked",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Base₂.cstar",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Base₂.noRestart",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Base₂.delta",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Base₂.idealization",
        "kind": "field",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Regimes.lean",
    "declaration": "AvailableChain.FGSA.Run.HealthyPrefix₂",
    "line": 30,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HealthyPrefix₂",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealthyPrefix₂.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealthyPrefix₂.base",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealthyPrefix₂.cut",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealthyPrefix₂.healthy",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealthyPrefix₂.deltaF",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.HealthyPrefix₂.partBefore",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Regimes.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanPrefix₂",
    "line": 41,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanPrefix₂",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanPrefix₂.toHealthyPrefix₂",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanPrefix₂.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanPrefix₂.partAt",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Regimes.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanCut₂",
    "line": 48,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanCut₂",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Regimes.lean",
    "declaration": "AvailableChain.FGSA.Run.Clean₂",
    "line": 55,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.Clean₂",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Clean₂.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Clean₂.pre",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Clean₂.gst",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Regimes.lean",
    "declaration": "AvailableChain.FGSA.Run.Recovery₂",
    "line": 64,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.Recovery₂",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Recovery₂.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Recovery₂.sync",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Recovery₂.deltaF",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Recovery₂.gap",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Recovery₂.base",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Recovery₂.fault",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Recovery₂.awake",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Recovery₂.gapPos",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Regimes.lean",
    "declaration": "AvailableChain.FGSA.Run.BaseSet",
    "line": 77,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.BaseSet",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Regimes.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanSet",
    "line": 78,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanSet",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Regimes.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanCutSet",
    "line": 80,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanCutSet",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Regimes.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanPrefixSet",
    "line": 83,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanPrefixSet",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Regimes.lean",
    "declaration": "AvailableChain.FGSA.Run.HealingSet",
    "line": 89,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HealingSet",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Regimes.lean",
    "declaration": "AvailableChain.FGSA.Run.Outage₂",
    "line": 109,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.Outage₂",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Outage₂.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Outage₂.pre",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Outage₂.sleepy",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Outage₂.order",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Outage₂.lag",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Outage₂.budget",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.Outage₂.fastPart",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Regimes.lean",
    "declaration": "AvailableChain.FGSA.Run.OutageSet",
    "line": 120,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.OutageSet",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/WeakContinuation.lean",
    "declaration": "AvailableChain.FGSA.Run.AgreesThrough₂",
    "line": 43,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.AgreesThrough₂",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AgreesThrough₂.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AgreesThrough₂.honest",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AgreesThrough₂.gst",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AgreesThrough₂.delta",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AgreesThrough₂.seats",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AgreesThrough₂.inputs",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AgreesThrough₂.awake",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AgreesThrough₂.events",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.AgreesThrough₂.suffixTime",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/WeakContinuation.lean",
    "declaration": "AvailableChain.FGSA.Run.SSafeFromCut₂",
    "line": 108,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.SSafeFromCut₂",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.SSafeFromCut₂.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.SSafeFromCut₂.compatible",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.SSafeFromCut₂.monotone",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.SSafeFromCut₂.seed",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.SSafeFromCut₂.finalBelow",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.SSafeFromCut₂.outputs",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/WeakContinuation.lean",
    "declaration": "AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂",
    "line": 24,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂.toRecovery₂",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂.liveness",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂.endpoint",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/WeakContinuation.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanContinuation₂",
    "line": 68,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanContinuation₂",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanContinuation₂.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanContinuation₂.base",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanContinuation₂.agrees",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanContinuation₂.covered",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanContinuation₂.sync",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanContinuation₂.deltaF",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanContinuation₂.participation",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/WeakContinuation.lean",
    "declaration": "AvailableChain.FGSA.Run.BoundedHealingCut₂",
    "line": 86,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.BoundedHealingCut₂",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BoundedHealingCut₂.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BoundedHealingCut₂.afterGST",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BoundedHealingCut₂.beforeEnd",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BoundedHealingCut₂.cut",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BoundedHealingCut₂.actualProposal",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.BoundedHealingCut₂.refreshed",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/WeakContinuation.lean",
    "declaration": "AvailableChain.FGSA.Run.BoundedSafetyRecovery₂",
    "line": 137,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.BoundedSafetyRecovery₂",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/WeakContinuationGrowth.lean",
    "declaration": "AvailableChain.FGSA.Run.RetainedAgreesThrough₂",
    "line": 15,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.RetainedAgreesThrough₂",
        "kind": "structure",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.RetainedAgreesThrough₂.mk",
        "kind": "ctor",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.RetainedAgreesThrough₂.honest",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.RetainedAgreesThrough₂.gst",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.RetainedAgreesThrough₂.delta",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.RetainedAgreesThrough₂.seats",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.RetainedAgreesThrough₂.inputs",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.RetainedAgreesThrough₂.awake",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.RetainedAgreesThrough₂.events",
        "kind": "field",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/WeakContinuationGrowth.lean",
    "declaration": "AvailableChain.FGSA.Run.PendingSourceDelivery₂",
    "line": 35,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.PendingSourceDelivery₂",
        "kind": "structure",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.PendingSourceDelivery₂.mk",
        "kind": "ctor",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.PendingSourceDelivery₂.sourceBroadcast",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.PendingSourceDelivery₂.sourceRelay",
        "kind": "field",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/WeakContinuationGrowth.lean",
    "declaration": "AvailableChain.FGSA.Run.CleanGrowthContinuation₂",
    "line": 63,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.CleanGrowthContinuation₂",
        "kind": "structure",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanGrowthContinuation₂.mk",
        "kind": "ctor",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanGrowthContinuation₂.base",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanGrowthContinuation₂.agrees",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanGrowthContinuation₂.covered",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanGrowthContinuation₂.sync",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanGrowthContinuation₂.pending",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanGrowthContinuation₂.deltaF",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanGrowthContinuation₂.accountable",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.CleanGrowthContinuation₂.participation",
        "kind": "field",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/WeakContinuationGrowth.lean",
    "declaration": "AvailableChain.FGSA.Run.BoundedGrowthRecovery₂",
    "line": 81,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.BoundedGrowthRecovery₂",
        "kind": "def",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.BoundedGrowthRecovery₂_def",
        "kind": "theorem",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/WeakContinuationLive.lean",
    "declaration": "AvailableChain.FGSA.Run.WeakContinuationLiveAt₂",
    "line": 18,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.WeakContinuationLiveAt₂",
        "kind": "structure",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.mk",
        "kind": "ctor",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.safety",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.inclusion",
        "kind": "field",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.growth",
        "kind": "field",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/WeakContinuationLive.lean",
    "declaration": "AvailableChain.FGSA.Run.BoundedSafetyLivenessRecovery₂",
    "line": 62,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.BoundedSafetyLivenessRecovery₂",
        "kind": "def",
        "frozen": false
      },
      {
        "name": "AvailableChain.FGSA.Run.BoundedSafetyLivenessRecovery₂_def",
        "kind": "theorem",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Windows.lean",
    "declaration": "AvailableChain.FGSA.Run.WinSpec",
    "line": 15,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.WinSpec",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Windows.lean",
    "declaration": "AvailableChain.FGSA.Run.gapWin",
    "line": 49,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.gapWin",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Windows.lean",
    "declaration": "AvailableChain.FGSA.Run.formWinAt",
    "line": 53,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.formWinAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Windows.lean",
    "declaration": "AvailableChain.FGSA.Run.kernelWin",
    "line": 56,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.kernelWin",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Windows.lean",
    "declaration": "AvailableChain.FGSA.Run.trigWin",
    "line": 59,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.trigWin",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Windows.lean",
    "declaration": "AvailableChain.FGSA.Run.cleanWinAt",
    "line": 28,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.cleanWinAt",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Windows.lean",
    "declaration": "AvailableChain.FGSA.Run.cleanWin",
    "line": 40,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.cleanWin",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Windows.lean",
    "declaration": "AvailableChain.FGSA.Run.cleanPrefixWin",
    "line": 43,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.cleanPrefixWin",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Windows.lean",
    "declaration": "AvailableChain.FGSA.Run.cleanLabelWin",
    "line": 46,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.cleanLabelWin",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Windows.lean",
    "declaration": "AvailableChain.FGSA.Run.outWin",
    "line": 64,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.outWin",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Witness.lean",
    "declaration": "AvailableChain.FGSA.Run.honestFrontier",
    "line": 60,
    "class": "A",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.honestFrontier",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Witness.lean",
    "declaration": "AvailableChain.FGSA.Run.oldRowHeights",
    "line": 50,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.oldRowHeights",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Witness.lean",
    "declaration": "AvailableChain.FGSA.Run.muOf",
    "line": 54,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.muOf",
        "kind": "def",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.muOf_def",
        "kind": "theorem",
        "frozen": false
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Witness.lean",
    "declaration": "AvailableChain.FGSA.Run.HeightRow",
    "line": 64,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.HeightRow",
        "kind": "def",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Witness.lean",
    "declaration": "AvailableChain.FGSA.Run.H0Reset",
    "line": 70,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.H0Reset",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.H0Reset.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.H0Reset.rG_after",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.H0Reset.rG_first",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.H0Reset.cut",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.H0Reset.frontier",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.H0Reset.rowCap",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.H0Reset.mu_le",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.H0Reset.cut_lower",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.H0Reset.cut_upper",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.H0Reset.reset_row",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.H0Reset.reset_first",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.H0Reset.label",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.H0Reset.fresh",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.H0Reset.synchronous",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Witness.lean",
    "declaration": "AvailableChain.FGSA.Run.H0",
    "line": 94,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.H0",
        "kind": "structure",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.H0.toH0Reset",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.H0.mk",
        "kind": "ctor",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.H0.proposal_lower",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.H0.proposal",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.H0.proposal_first",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.H0.after_gst",
        "kind": "field",
        "frozen": true
      },
      {
        "name": "AvailableChain.FGSA.Run.H0.source_prefix",
        "kind": "field",
        "frozen": true
      }
    ]
  },
  {
    "path": "AvailableChainFGSAClaims/Statements/Witness.lean",
    "declaration": "AvailableChain.FGSA.Run.tstarOf",
    "line": 104,
    "class": "B",
    "manifest_entries": [
      {
        "name": "AvailableChain.FGSA.Run.tstarOf",
        "kind": "def",
        "frozen": true
      }
    ]
  }
]
```
