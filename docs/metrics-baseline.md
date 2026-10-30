# Baseline metrics (foundation plan §11 step 1)

> Measured at `888664e6`, before the move to one library (#5): the module names below are the old ones
> (`ConsensusSpec.*`, `ConsensusProofs.*`, ...); the `[[layer]]` entries of `scripts/boundaries.toml` map the current names.

Report-only numbers for the layout before the foundation reorg (#4), taken at `888664e6` (main,
2026-10-29). Later steps compare against them. Nothing here is a gate: plan §6 makes depth, cones and
critical path reports, with no thresholds.

## How to regenerate

```sh
# Graph metrics and the layer map: no build, about 1 s. Exit 1 on a module without a layer.
python3 -I scripts/metrics-baseline.py [--json out.json] [--no-modules]

# Cold build profile of the default targets (in a job, in your own worktree): the project's own
# modules from scratch, dependencies from the hard-linked packages, Lake's artifact cache off so
# that no project module is restored. Check first that the dependencies are built
# (`lake build --no-build Mathlib.Tactic`), or Mathlib compiles.
job --mem 16G --cpus 8 consensus-lean metrics-cold -- bash -lc 'cd <worktree> && rm -rf .lake/build &&
  LAKE_ARTIFACT_CACHE=false /usr/bin/time -v -o "$RUN_DIR/time.txt" lake build -v > "$RUN_DIR/build.log" 2>&1'
python3 -I scripts/metrics-baseline.py --timings <RUN_DIR>/build.log
```

The layer of a module is its `[[layer]]` in `scripts/boundaries.toml` (since step 3, #6, which replaced
`scripts/layers.toml` with the boundary checker's config); a generated root is `Aggregate`, a module of a
target outside the checked libraries `(<target>)`. Milestones are the milestone layers (`Proofs.<M>`).

Files that only check.sh compiles directly (`scripts/SpecSurface.lean`, the `scripts/fixtures/` files
outside `CheckFixtures`) belong to no target, so they are not counted.

The build profile uses Lake's own per-module times (`lake build -v`). lakeprof was not used:
installing it from GitHub was not permitted in this session (external code on the shared box).
Lake's times give the same per-module data, and the script computes the critical path from them and
the import graph.

Lake prints times of 1–10 s as `{ms/1000}.{(ms+50)/100 % 10}s`, without a carry, so 1950–1999 ms
prints as `1.0s`. Summed time and the critical path can therefore be a few seconds low.

## Headline numbers

| Metric | Baseline |
|---|---|
| Modules | 130 in lakefile targets, 88 of them in the default targets; every module has a layer (18 layers; Core is empty) |
| Import depth (edges) | full graph: max 29; median 8 over the 88 default-target modules. The chain starts at the root `ConsensusTests`, runs through Tests and passes 6 aggregates |
| Library depth | max 18: Test, Challenge, Solution and Tool modules left out, and an import of an aggregate counted as the aggregate's own imports. The plan's figures for comparison: Carleson 30, PFR 19, FLT 14, CSLib 13 |
| Downstream cone | max 84/88 (95%, `ConsensusSpec.Problem.Basic`), median 28; 58 of 88 modules above 15% |
| `@[expose]` | whole-file `@[expose] public section` in 109 of 123 `module` files, including all 27 Lemmas files, 3 Proofs files and 2 Main files; no per-declaration expose |
| Imports (`module` files) | project: 270 public, 0 plain, 2 meta, 1 `import all` (in Test). External: 52 public, 13 distinct modules, no `import Mathlib`. 6 more imports in the 7 non-`module` files (check-decls copies) |
| Aggregates | 8 import-only modules (4 library roots, 4 folder aggregates); 29 imports of them, from 24 modules |
| Cold build, default targets | 49.4 s wall, 196 s CPU (158 user + 38 sys, 4.0 cores on average), peak RSS of one process 1.8 GB; 88 modules built, 167 s of module time in total |
| Critical path | 47.5 s across 30 modules, the same chain as the maximal depth. The build is bound by this chain, not by cores |

Machine: the shared ethlabs box, `job --mem 16G --cpus 8`, with one other 8-core job running (load
about 8). Lean v4.35.0, Mathlib v4.35.0.

## Notes for the next steps

- **Critical path.** From Spec upward, the longest chain runs Spec → Lemmas → generic Proofs/Main →
  Instances → Tests and ends at the root `ConsensusTests`. On the way it passes 5 more aggregates:
  `ConsensusProofs.Problem`, `ConsensusProofs.Model.Canonical`, `ConsensusProofs.Model`,
  `ConsensusProofs.Shape` and `ConsensusInstances`. Each one adds a module load to the chain, and the 8
  aggregates together take 9.2 s of module time. Removing aggregate imports inside the library (plan
  §1, step 2) shortens the chain and shrinks cones.
- **Edges the plan's matrix (§2) forbids** (see the layer-edge table below). Step 3 either moves them
  or records them as reviewed exceptions:
  - `Proofs.RegimesRealizable → Proofs.Behaviour` crosses milestones.
  - `Instances.Goldilocks.Spec → Main`: `ConsensusInstances.Goldilocks` imports
    `ConsensusProofs.Shape.Accepted` for its own theorems.
  - `Instances.Streamlet.Spec → Instances.Bft.Spec` and `Instances.Tendermint.Spec → Instances.Bft.Spec`:
    one instance imports another, so the shared `Bft` material moves down.
  - `Instances.Bft.Spec → Aggregate`, and every other import of an aggregate.
- **`Proofs` as a module component.** check-imports.py (now check-boundaries.py) refuses module components named `Proofs` or
  `Exports` because the vendored check-decls exempts them, hard-coded in `scripts/CheckDecls.lean`
  (`inProofs`, `inExports`). The plan's `Proofs/<M>/` prefix needs one of three things:
  - a different component name;
  - an edit to the vendored file, which breaks its verbatim status and `vendor.sha256`;
  - check-decls dropped as a gate, which plan §5 already makes a review item.

  The last two change a trust check, so they need two reviews (#21).
- **Definitions outside the exposed layers.** Plan §3 removes expose from Lemmas, Proofs and Main.
  These files still hold top-level definitions:
  - Lemmas: `Problem.Derived`, `Model.CanonicalStatement`, the `Model.Canonical.*` construction,
    `Adequate`, `Causal`, `Credentials`, `Protection`, `Truncate`.
  - Proofs: `Shape.Realizable`, with 9 definitions.
  - Main: `Shape.Service`.

  Step 5 (#8) either moves the ones that are unfolded elsewhere down into Spec, which grows the trusted
  surface, or asks for an approved exception to §3.
- **Mixed files.** `ConsensusInstances.GoldilocksSheet` (mapped to Instances.Goldilocks.Statements)
  holds the reviewed target and 25 theorems. `Goldilocks`, `Bft`, `Streamlet` and `Tendermint` (mapped to
  their Spec layers) hold the theorems that make them accepted instances (`*_admissible`,
  `*_progressFits`, `*_progressTolerant`). Split them into Spec, Statements and Proofs when the
  Goldilocks slice (step 7) starts.
- **Tool layer.** The 41 check-stack modules (check-decls, its fixtures and CheckFixtures) sit outside
  the library layers; the plan moves checker fixtures into the test library.

## Report

Output of `python3 -I scripts/metrics-baseline.py --timings <cold build.log>` at `888664e6`.


Modules: 130 in lakefile targets, 88 in the default targets (ConsensusSpec, ConsensusProofs, ConsensusInstances, ConsensusTests).

### Per target layer

| layer | modules | lines | max depth | max cone | `@[expose]` sections | other `@[expose]` | public imports | plain imports | meta imports | `import all` | build s |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Spec | 22 | 2479 | 9 | 84 | 22 | 0 | 48 | 0 | 0 | 0 | 35.1 |
| Statements | 1 | 62 | 10 | 13 | 1 | 0 | 3 | 0 | 0 | 0 | 1.2 |
| Lemmas | 27 | 3294 | 15 | 60 | 27 | 0 | 66 | 0 | 0 | 0 | 56.8 |
| Proofs.Behaviour | 1 | 182 | 16 | 22 | 1 | 0 | 3 | 0 | 0 | 0 | 1.6 |
| Proofs.RegimesRealizable | 1 | 877 | 17 | 21 | 1 | 0 | 4 | 0 | 0 | 0 | 2.9 |
| Proofs.Faithful | 1 | 128 | 6 | 28 | 1 | 0 | 5 | 0 | 0 | 0 | 3.7 |
| Main | 2 | 91 | 19 | 20 | 2 | 0 | 3 | 0 | 0 | 0 | 2.7 |
| Instances.Goldilocks.Spec | 1 | 233 | 19 | 11 | 1 | 0 | 1 | 0 | 0 | 0 | 1.5 |
| Instances.Goldilocks.Statements | 1 | 689 | 20 | 10 | 1 | 0 | 2 | 0 | 0 | 0 | 2.2 |
| Instances.Bft.Spec | 1 | 78 | 21 | 12 | 1 | 0 | 2 | 0 | 0 | 0 | 1.3 |
| Instances.Streamlet.Spec | 1 | 54 | 22 | 10 | 1 | 0 | 2 | 0 | 0 | 0 | 1.5 |
| Instances.Tendermint.Spec | 1 | 50 | 22 | 10 | 1 | 0 | 2 | 0 | 0 | 0 | 1.2 |
| Test | 19 | 4732 | 28 | 9 | 18 | 0 | 72 | 0 | 1 | 1 | 44.6 |
| Challenge | 1 | 17 | 12 | - | 1 | 0 | 1 | 0 | 0 | 0 | - |
| Solution | 1 | 27 | 19 | 11 | 1 | 0 | 4 | 0 | 0 | 0 | 1.6 |
| Aggregate | 8 | 123 | 29 | 53 | 0 | 0 | 89 | 0 | 0 | 0 | 9.2 |
| Tool | 41 | 939 | 2 | - | 29 | 0 | 15 | 0 | 3 | 0 | - |

### Totals

- Depth (longest chain of project imports, in edges): max 29, `ConsensusTests -> ConsensusTests.Index -> ConsensusTests.Vacuity -> ConsensusTests.Realizable -> ConsensusTests.Controls -> ConsensusTests.Support -> ConsensusInstances -> ConsensusInstances.Streamlet -> ConsensusInstances.Bft -> ConsensusProofs.Shape -> ConsensusProofs.Shape.Service -> ConsensusProofs.Shape.Accepted -> ConsensusProofs.Shape.Realizable -> ConsensusProofs.Shape.Refinement -> ConsensusProofs.Shape.Payload -> ConsensusProofs.Model -> ConsensusProofs.Model.Adequate -> ConsensusProofs.Model.Canonical -> ConsensusProofs.Model.Canonical.Construction -> ConsensusProofs.Model.Canonical.Network -> ConsensusProofs.Model.Canonical.Schedule -> ConsensusProofs.Model.Canonical.Events -> ConsensusProofs.Model.Canonical.Delivery -> ConsensusProofs.Model.CanonicalStatement -> ConsensusProofs.Problem -> ConsensusProofs.Problem.Facts.Good -> ConsensusProofs.Problem.Facts.Atoms -> ConsensusProofs.Problem.Derived -> ConsensusSpec.Problem.Network -> ConsensusSpec.Problem.Basic`.
- Depth over the default targets: max 29, median 8.
- Library depth (layers outside `non_library` and Aggregate; an aggregate import counts as its imports): max 18, `ConsensusInstances.Streamlet -> ConsensusInstances.Bft -> ConsensusProofs.Shape.Service -> ConsensusProofs.Shape.Accepted -> ConsensusProofs.Shape.Realizable -> ConsensusProofs.Shape.Refinement -> ConsensusProofs.Shape.Payload -> ConsensusProofs.Model.Adequate -> ConsensusProofs.Model.Canonical.Construction -> ConsensusProofs.Model.Canonical.Network -> ConsensusProofs.Model.Canonical.Schedule -> ConsensusProofs.Model.Canonical.Events -> ConsensusProofs.Model.Canonical.Delivery -> ConsensusProofs.Model.CanonicalStatement -> ConsensusProofs.Problem.Facts.Good -> ConsensusProofs.Problem.Facts.Atoms -> ConsensusProofs.Problem.Derived -> ConsensusSpec.Problem.Network -> ConsensusSpec.Problem.Basic`.
- Downstream cone (default-target modules that import the module, transitively; 88 = 100%): max 84 (95%, `ConsensusSpec.Problem.Basic`), median 28, 58 modules above 15%.
- `module` files: 123/130. Whole-file `@[expose] public section`: 109; other `@[expose]`: 0; `public section` (any): 109.
- Imports of project modules: 270 public, 0 plain, 2 meta, 1 `import all`. External imports: 52 public, 0 plain, 2 meta, 0 `import all`; `import Mathlib`: 0. Imports in non-`module` files (not counted above): 6.
- Distinct external modules imported directly: 13.
- Import-only aggregates (layer Aggregate): 8; imports of an aggregate by another layer: 29 (from 24 modules).

Direct imports between distinct layers (from -> to: count; up to two examples):

| from | to | imports | examples |
|---|---|---|---|
| Statements | Spec | 3 | `ConsensusSpec.Statements` -> `ConsensusSpec.Model.Served`; `ConsensusSpec.Statements` -> `ConsensusSpec.Shape.Accepted` |
| Lemmas | Aggregate | 7 | `ConsensusProofs.Model.Adequate` -> `ConsensusProofs.Model.Canonical`; `ConsensusProofs.Model.Candidates` -> `ConsensusProofs.Problem` |
| Lemmas | Spec | 18 | `ConsensusProofs.Blocks.Facts` -> `ConsensusSpec.Blocks.Chains`; `ConsensusProofs.Blocks.Facts` -> `ConsensusSpec.Blocks.Payload` |
| Proofs.Behaviour | Lemmas | 2 | `ConsensusProofs.Shape.Refinement` -> `ConsensusProofs.Problem.Facts.Transfer`; `ConsensusProofs.Shape.Refinement` -> `ConsensusProofs.Shape.Payload` |
| Proofs.Behaviour | Spec | 1 | `ConsensusProofs.Shape.Refinement` -> `ConsensusSpec.Shape.Claims` |
| Proofs.RegimesRealizable | Proofs.Behaviour | 1 | `ConsensusProofs.Shape.Realizable` -> `ConsensusProofs.Shape.Refinement` |
| Proofs.RegimesRealizable | Spec | 2 | `ConsensusProofs.Shape.Realizable` -> `ConsensusSpec.Shape.Active`; `ConsensusProofs.Shape.Realizable` -> `ConsensusSpec.Shape.ProgressFit` |
| Proofs.Faithful | Aggregate | 1 | `ConsensusProofs.Model.Faithful` -> `ConsensusProofs.Problem` |
| Proofs.Faithful | Lemmas | 1 | `ConsensusProofs.Model.Faithful` -> `ConsensusProofs.Model.Protocol` |
| Proofs.Faithful | Spec | 2 | `ConsensusProofs.Model.Faithful` -> `ConsensusSpec.Model.Served`; `ConsensusProofs.Model.Faithful` -> `ConsensusSpec.Model.System` |
| Main | Proofs.RegimesRealizable | 1 | `ConsensusProofs.Shape.Accepted` -> `ConsensusProofs.Shape.Realizable` |
| Main | Spec | 1 | `ConsensusProofs.Shape.Accepted` -> `ConsensusSpec.Shape.Accepted` |
| Instances.Goldilocks.Spec | Main | 1 | `ConsensusInstances.Goldilocks` -> `ConsensusProofs.Shape.Accepted` |
| Instances.Goldilocks.Statements | Instances.Goldilocks.Spec | 1 | `ConsensusInstances.GoldilocksSheet` -> `ConsensusInstances.Goldilocks` |
| Instances.Bft.Spec | Aggregate | 1 | `ConsensusInstances.Bft` -> `ConsensusProofs.Shape` |
| Instances.Streamlet.Spec | Instances.Bft.Spec | 1 | `ConsensusInstances.Streamlet` -> `ConsensusInstances.Bft` |
| Instances.Tendermint.Spec | Instances.Bft.Spec | 1 | `ConsensusInstances.Tendermint` -> `ConsensusInstances.Bft` |
| Test | Aggregate | 19 | `ConsensusTests.Common` -> `ConsensusProofs.Problem`; `ConsensusTests.Controls` -> `ConsensusInstances` |
| Test | Lemmas | 1 | `ConsensusTests.Blocks` -> `ConsensusProofs.Blocks.Facts` |
| Test | Solution | 2 | `ConsensusTests.Index` -> `ConsensusProofs.Review`; `ConsensusTests.ReviewAxioms` -> `ConsensusProofs.Review` |
| Test | Statements | 1 | `ConsensusTests.ReviewAxioms` -> `ConsensusSpec.Statements` |
| Challenge | Aggregate | 1 | `ConsensusChallenge` -> `ConsensusSpec` |
| Solution | Main | 1 | `ConsensusProofs.Review` -> `ConsensusProofs.Shape.Accepted` |
| Solution | Proofs.Faithful | 1 | `ConsensusProofs.Review` -> `ConsensusProofs.Model.Faithful` |
| Solution | Proofs.RegimesRealizable | 1 | `ConsensusProofs.Review` -> `ConsensusProofs.Shape.Realizable` |
| Solution | Statements | 1 | `ConsensusProofs.Review` -> `ConsensusSpec.Statements` |
| Aggregate | Instances.Bft.Spec | 1 | `ConsensusInstances` -> `ConsensusInstances.Bft` |
| Aggregate | Instances.Goldilocks.Spec | 1 | `ConsensusInstances` -> `ConsensusInstances.Goldilocks` |
| Aggregate | Instances.Goldilocks.Statements | 1 | `ConsensusInstances` -> `ConsensusInstances.GoldilocksSheet` |
| Aggregate | Instances.Streamlet.Spec | 1 | `ConsensusInstances` -> `ConsensusInstances.Streamlet` |
| Aggregate | Instances.Tendermint.Spec | 1 | `ConsensusInstances` -> `ConsensusInstances.Tendermint` |
| Aggregate | Lemmas | 23 | `ConsensusProofs.Model.Canonical` -> `ConsensusProofs.Model.Canonical.Construction`; `ConsensusProofs.Model` -> `ConsensusProofs.Model.Adequate` |
| Aggregate | Main | 2 | `ConsensusProofs.Shape` -> `ConsensusProofs.Shape.Accepted`; `ConsensusProofs.Shape` -> `ConsensusProofs.Shape.Service` |
| Aggregate | Proofs.Behaviour | 1 | `ConsensusProofs.Shape` -> `ConsensusProofs.Shape.Refinement` |
| Aggregate | Proofs.Faithful | 1 | `ConsensusProofs.Model` -> `ConsensusProofs.Model.Faithful` |
| Aggregate | Proofs.RegimesRealizable | 1 | `ConsensusProofs.Shape` -> `ConsensusProofs.Shape.Realizable` |
| Aggregate | Solution | 1 | `ConsensusProofs` -> `ConsensusProofs.Review` |
| Aggregate | Spec | 30 | `ConsensusProofs.Problem` -> `ConsensusSpec.Problem.Good`; `ConsensusProofs.Shape` -> `ConsensusSpec.Shape.Accepted` |
| Aggregate | Statements | 1 | `ConsensusSpec` -> `ConsensusSpec.Statements` |
| Aggregate | Test | 18 | `ConsensusTests` -> `ConsensusTests.Blocks`; `ConsensusTests` -> `ConsensusTests.Controls` |

Largest downstream cones (default targets):

| module | layer | cone | share |
|---|---|---|---|
| `ConsensusSpec.Problem.Basic` | Spec | 84 | 95% |
| `ConsensusSpec.Problem.Network` | Spec | 75 | 85% |
| `ConsensusSpec.Problem.Properties` | Spec | 73 | 83% |
| `ConsensusSpec.Problem.Regimes` | Spec | 68 | 77% |
| `ConsensusSpec.Problem.Good` | Spec | 66 | 75% |
| `ConsensusSpec.Model.Objects` | Spec | 66 | 75% |
| `ConsensusSpec.Model.Protocol` | Spec | 61 | 69% |
| `ConsensusProofs.Problem.Derived` | Lemmas | 60 | 68% |
| `ConsensusSpec.Model.Run` | Spec | 59 | 67% |
| `ConsensusSpec.Model.Conditions` | Spec | 58 | 66% |
| `ConsensusSpec.Model.System` | Spec | 57 | 65% |
| `ConsensusProofs.Problem.Facts.Regimes` | Lemmas | 55 | 62% |

### Build profile (from --timings)

- Project modules with a time: 88/130; sum of module times 167.0 s.
- Critical path (longest import chain weighted by module time): 47.5 s, 30 modules: `ConsensusTests -> ConsensusTests.Index -> ConsensusTests.Vacuity -> ConsensusTests.Realizable -> ConsensusTests.Controls -> ConsensusTests.Support -> ConsensusInstances -> ConsensusInstances.Streamlet -> ConsensusInstances.Bft -> ConsensusProofs.Shape -> ConsensusProofs.Shape.Service -> ConsensusProofs.Shape.Accepted -> ConsensusProofs.Shape.Realizable -> ConsensusProofs.Shape.Refinement -> ConsensusProofs.Shape.Payload -> ConsensusProofs.Model -> ConsensusProofs.Model.Adequate -> ConsensusProofs.Model.Canonical -> ConsensusProofs.Model.Canonical.Construction -> ConsensusProofs.Model.Canonical.Network -> ConsensusProofs.Model.Canonical.Schedule -> ConsensusProofs.Model.Canonical.Events -> ConsensusProofs.Model.Canonical.Delivery -> ConsensusProofs.Model.CanonicalStatement -> ConsensusProofs.Problem -> ConsensusProofs.Problem.Facts.Good -> ConsensusProofs.Problem.Facts.Atoms -> ConsensusProofs.Problem.Derived -> ConsensusSpec.Problem.Network -> ConsensusSpec.Problem.Basic`.

Slowest modules:

| module | layer | s |
|---|---|---|
| `ConsensusTests.Regimes` | Test | 5.9 |
| `ConsensusProofs.Blocks.Facts` | Lemmas | 3.8 |
| `ConsensusTests.Problem` | Test | 3.8 |
| `ConsensusProofs.Model.Faithful` | Proofs.Faithful | 3.7 |
| `ConsensusSpec.Shape.Compile` | Spec | 3.7 |
| `ConsensusTests.Gaps` | Test | 3.6 |
| `ConsensusSpec.Shape.ProgressFit` | Spec | 3.5 |
| `ConsensusProofs.Model.Mempool` | Lemmas | 3.4 |
| `ConsensusProofs.Model.Objects` | Lemmas | 3.4 |
| `ConsensusProofs.Model.Candidates` | Lemmas | 3.3 |
| `ConsensusTests.Common` | Test | 3.2 |
| `ConsensusProofs.Model.CanonicalStatement` | Lemmas | 3.1 |

<details><summary>Every module: layer, lines, depth, cone, imports, expose, build time, milestones</summary>


Cone: default-target modules that import it (`-`: not a default-target module). Milestones (at `888664e6`): the `[milestones]` proof modules of the former scripts/layers.toml whose imports reach it.

| module | layer | target | lines | depth | cone | public imp | plain imp | expose | build s | milestones |
|---|---|---|---|---|---|---|---|---|---|---|
| `ConsensusSpec.Blocks.Chains` | Spec | ConsensusSpec | 96 | 1 | 36 | 3 | 0 | 1 | 1.0 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusSpec.Blocks.Payload` | Spec | ConsensusSpec | 30 | 2 | 35 | 2 | 0 | 1 | 0.6 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusSpec.Blocks.Progress` | Spec | ConsensusSpec | 112 | 2 | 35 | 1 | 0 | 1 | 1.4 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusSpec.Blocks.TimeGrid` | Spec | ConsensusSpec | 41 | 1 | 36 | 2 | 0 | 1 | 1.2 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusSpec.Model.Conditions` | Spec | ConsensusSpec | 81 | 3 | 58 | 2 | 0 | 1 | 2.3 | AcceptedGood, Behaviour, Faithful, RegimesRealizable |
| `ConsensusSpec.Model.Objects` | Spec | ConsensusSpec | 109 | 0 | 66 | 1 | 0 | 1 | 1.0 | AcceptedGood, Behaviour, Faithful, RegimesRealizable |
| `ConsensusSpec.Model.Protocol` | Spec | ConsensusSpec | 125 | 1 | 61 | 4 | 0 | 1 | 0.9 | AcceptedGood, Behaviour, Faithful, RegimesRealizable |
| `ConsensusSpec.Model.Run` | Spec | ConsensusSpec | 242 | 2 | 59 | 2 | 0 | 1 | 1.4 | AcceptedGood, Behaviour, Faithful, RegimesRealizable |
| `ConsensusSpec.Model.Served` | Spec | ConsensusSpec | 28 | 5 | 31 | 1 | 0 | 1 | 1.2 | AcceptedGood, Behaviour, Faithful, RegimesRealizable |
| `ConsensusSpec.Model.System` | Spec | ConsensusSpec | 86 | 4 | 57 | 2 | 0 | 1 | 1.3 | AcceptedGood, Behaviour, Faithful, RegimesRealizable |
| `ConsensusSpec.Problem.Basic` | Spec | ConsensusSpec | 233 | 0 | 84 | 5 | 0 | 1 | 0.8 | AcceptedGood, Behaviour, Faithful, RegimesRealizable |
| `ConsensusSpec.Problem.Good` | Spec | ConsensusSpec | 255 | 3 | 66 | 3 | 0 | 1 | 1.7 | AcceptedGood, Behaviour, Faithful, RegimesRealizable |
| `ConsensusSpec.Problem.Network` | Spec | ConsensusSpec | 96 | 1 | 75 | 2 | 0 | 1 | 1.8 | AcceptedGood, Behaviour, Faithful, RegimesRealizable |
| `ConsensusSpec.Problem.Properties` | Spec | ConsensusSpec | 122 | 1 | 73 | 1 | 0 | 1 | 0.7 | AcceptedGood, Behaviour, Faithful, RegimesRealizable |
| `ConsensusSpec.Problem.Regimes` | Spec | ConsensusSpec | 155 | 2 | 68 | 2 | 0 | 1 | 2.1 | AcceptedGood, Behaviour, Faithful, RegimesRealizable |
| `ConsensusSpec.Shape.Accepted` | Spec | ConsensusSpec | 51 | 9 | 23 | 3 | 0 | 1 | 1.6 | AcceptedGood |
| `ConsensusSpec.Shape.Active` | Spec | ConsensusSpec | 91 | 8 | 25 | 2 | 0 | 1 | 2.1 | AcceptedGood, RegimesRealizable |
| `ConsensusSpec.Shape.Claims` | Spec | ConsensusSpec | 95 | 8 | 26 | 1 | 0 | 1 | 1.6 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusSpec.Shape.Compile` | Spec | ConsensusSpec | 110 | 6 | 30 | 1 | 0 | 1 | 3.7 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusSpec.Shape.ProgressFit` | Spec | ConsensusSpec | 56 | 6 | 26 | 1 | 0 | 1 | 3.5 | AcceptedGood, RegimesRealizable |
| `ConsensusSpec.Shape.Run` | Spec | ConsensusSpec | 119 | 7 | 29 | 2 | 0 | 1 | 1.5 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusSpec.Shape.Shape` | Spec | ConsensusSpec | 146 | 5 | 32 | 5 | 0 | 1 | 1.7 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusSpec.Statements` | Statements | ConsensusSpec | 62 | 10 | 13 | 3 | 0 | 1 | 1.2 | - |
| `ConsensusProofs.Blocks.Facts` | Lemmas | ConsensusProofs | 275 | 3 | 25 | 4 | 0 | 1 | 3.8 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Model.Adequate` | Lemmas | ConsensusProofs | 76 | 13 | 28 | 3 | 0 | 1 | 1.2 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Model.Candidates` | Lemmas | ConsensusProofs | 103 | 6 | 36 | 3 | 0 | 1 | 3.3 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Model.Canonical.Construction` | Lemmas | ConsensusProofs | 110 | 11 | 31 | 2 | 0 | 1 | 1.2 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Model.Canonical.Delivery` | Lemmas | ConsensusProofs | 23 | 7 | 38 | 2 | 0 | 1 | 2.2 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Model.Canonical.Events` | Lemmas | ConsensusProofs | 106 | 8 | 37 | 2 | 0 | 1 | 1.6 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Model.Canonical.Network` | Lemmas | ConsensusProofs | 153 | 10 | 32 | 2 | 0 | 1 | 1.7 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Model.Canonical.Schedule` | Lemmas | ConsensusProofs | 288 | 9 | 33 | 1 | 0 | 1 | 2.5 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Model.Canonical.Unforgeable` | Lemmas | ConsensusProofs | 198 | 9 | 35 | 2 | 0 | 1 | 2.2 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Model.CanonicalStatement` | Lemmas | ConsensusProofs | 17 | 6 | 39 | 3 | 0 | 1 | 3.1 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Model.Causal` | Lemmas | ConsensusProofs | 122 | 13 | 28 | 2 | 0 | 1 | 1.2 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Model.Credentials` | Lemmas | ConsensusProofs | 127 | 10 | 32 | 2 | 0 | 1 | 1.4 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Model.Laws` | Lemmas | ConsensusProofs | 59 | 8 | 28 | 1 | 0 | 1 | 1.8 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Model.Mempool` | Lemmas | ConsensusProofs | 42 | 6 | 28 | 3 | 0 | 1 | 3.4 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Model.Objects` | Lemmas | ConsensusProofs | 72 | 6 | 41 | 3 | 0 | 1 | 3.4 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Model.Protection` | Lemmas | ConsensusProofs | 333 | 10 | 29 | 2 | 0 | 1 | 2.0 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Model.Protocol` | Lemmas | ConsensusProofs | 28 | 2 | 47 | 1 | 0 | 1 | 1.0 | AcceptedGood, Behaviour, Faithful, RegimesRealizable |
| `ConsensusProofs.Model.Truncate` | Lemmas | ConsensusProofs | 249 | 8 | 29 | 2 | 0 | 1 | 2.1 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Model.View` | Lemmas | ConsensusProofs | 199 | 7 | 36 | 1 | 0 | 1 | 1.7 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Problem.Derived` | Lemmas | ConsensusProofs | 64 | 2 | 60 | 2 | 0 | 1 | 1.9 | AcceptedGood, Behaviour, Faithful, RegimesRealizable |
| `ConsensusProofs.Problem.Facts.Atoms` | Lemmas | ConsensusProofs | 42 | 3 | 55 | 3 | 0 | 1 | 2.3 | AcceptedGood, Behaviour, Faithful, RegimesRealizable |
| `ConsensusProofs.Problem.Facts.Good` | Lemmas | ConsensusProofs | 226 | 4 | 54 | 7 | 0 | 1 | 1.4 | AcceptedGood, Behaviour, Faithful, RegimesRealizable |
| `ConsensusProofs.Problem.Facts.Network` | Lemmas | ConsensusProofs | 114 | 3 | 55 | 3 | 0 | 1 | 2.3 | AcceptedGood, Behaviour, Faithful, RegimesRealizable |
| `ConsensusProofs.Problem.Facts.Properties` | Lemmas | ConsensusProofs | 99 | 3 | 55 | 2 | 0 | 1 | 2.3 | AcceptedGood, Behaviour, Faithful, RegimesRealizable |
| `ConsensusProofs.Problem.Facts.Regimes` | Lemmas | ConsensusProofs | 40 | 3 | 55 | 3 | 0 | 1 | 2.1 | AcceptedGood, Behaviour, Faithful, RegimesRealizable |
| `ConsensusProofs.Problem.Facts.Transfer` | Lemmas | ConsensusProofs | 48 | 3 | 54 | 2 | 0 | 1 | 2.3 | AcceptedGood, Behaviour, Faithful, RegimesRealizable |
| `ConsensusProofs.Shape.Payload` | Lemmas | ConsensusProofs | 81 | 15 | 23 | 3 | 0 | 1 | 1.4 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Shape.Refinement` | Proofs.Behaviour | ConsensusProofs | 182 | 16 | 22 | 3 | 0 | 1 | 1.6 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Shape.Realizable` | Proofs.RegimesRealizable | ConsensusProofs | 877 | 17 | 21 | 4 | 0 | 1 | 2.9 | AcceptedGood, RegimesRealizable |
| `ConsensusProofs.Model.Faithful` | Proofs.Faithful | ConsensusProofs | 128 | 6 | 28 | 5 | 0 | 1 | 3.7 | AcceptedGood, Behaviour, Faithful, RegimesRealizable |
| `ConsensusProofs.Shape.Accepted` | Main | ConsensusProofs | 37 | 18 | 20 | 2 | 0 | 1 | 1.1 | AcceptedGood |
| `ConsensusProofs.Shape.Service` | Main | ConsensusProofs | 54 | 19 | 15 | 1 | 0 | 1 | 1.6 | - |
| `ConsensusInstances.Goldilocks` | Instances.Goldilocks.Spec | ConsensusInstances | 233 | 19 | 11 | 1 | 0 | 1 | 1.5 | - |
| `ConsensusInstances.GoldilocksSheet` | Instances.Goldilocks.Statements | ConsensusInstances | 689 | 20 | 10 | 2 | 0 | 1 | 2.2 | - |
| `ConsensusInstances.Bft` | Instances.Bft.Spec | ConsensusInstances | 78 | 21 | 12 | 2 | 0 | 1 | 1.3 | - |
| `ConsensusInstances.Streamlet` | Instances.Streamlet.Spec | ConsensusInstances | 54 | 22 | 10 | 2 | 0 | 1 | 1.5 | - |
| `ConsensusInstances.Tendermint` | Instances.Tendermint.Spec | ConsensusInstances | 50 | 22 | 10 | 2 | 0 | 1 | 1.2 | - |
| `ConsensusTests.Blocks` | Test | ConsensusTests | 163 | 7 | 2 | 3 | 0 | 1 | 2.2 | - |
| `ConsensusTests.Common` | Test | ConsensusTests | 21 | 6 | 9 | 2 | 0 | 1 | 3.2 | - |
| `ConsensusTests.Controls` | Test | ConsensusTests | 197 | 25 | 4 | 4 | 0 | 1 | 1.6 | - |
| `ConsensusTests.Gaps` | Test | ConsensusTests | 133 | 6 | 2 | 2 | 0 | 1 | 3.6 | - |
| `ConsensusTests.Goldilocks` | Test | ConsensusTests | 229 | 24 | 2 | 3 | 0 | 1 | 1.8 | - |
| `ConsensusTests.Good` | Test | ConsensusTests | 456 | 7 | 4 | 3 | 0 | 1 | 3.0 | - |
| `ConsensusTests.Index` | Test | ConsensusTests | 410 | 28 | 1 | 18 | 0 | 0 | 2.3 | - |
| `ConsensusTests.Leaks` | Test | ConsensusTests | 567 | 25 | 2 | 5 | 0 | 1 | 2.7 | - |
| `ConsensusTests.Lift` | Test | ConsensusTests | 282 | 15 | 2 | 2 | 0 | 1 | 2.1 | - |
| `ConsensusTests.Model` | Test | ConsensusTests | 173 | 15 | 3 | 3 | 0 | 1 | 1.9 | - |
| `ConsensusTests.Network` | Test | ConsensusTests | 369 | 16 | 2 | 3 | 0 | 1 | 2.4 | - |
| `ConsensusTests.Problem` | Test | ConsensusTests | 213 | 6 | 2 | 2 | 0 | 1 | 3.8 | - |
| `ConsensusTests.Realizable` | Test | ConsensusTests | 265 | 26 | 3 | 6 | 0 | 1 | 1.4 | - |
| `ConsensusTests.Regimes` | Test | ConsensusTests | 462 | 6 | 5 | 2 | 0 | 1 | 5.9 | - |
| `ConsensusTests.ReviewAxioms` | Test | ConsensusTests | 68 | 20 | 1 | 1 | 0 | 1 | 2.2 | - |
| `ConsensusTests.ReviewGuard` | Test | ConsensusTests | 67 | 0 | 2 | 1 | 0 | 1 | 0.6 | - |
| `ConsensusTests.Shape` | Test | ConsensusTests | 183 | 25 | 4 | 5 | 0 | 1 | 1.4 | - |
| `ConsensusTests.Support` | Test | ConsensusTests | 209 | 24 | 7 | 3 | 0 | 1 | 1.0 | - |
| `ConsensusTests.Vacuity` | Test | ConsensusTests | 265 | 27 | 2 | 4 | 0 | 1 | 1.5 | - |
| `ConsensusChallenge` | Challenge | ConsensusChallenge | 17 | 12 | - | 1 | 0 | 1 | - | - |
| `ConsensusProofs.Review` | Solution | ConsensusProofs | 27 | 19 | 11 | 4 | 0 | 1 | 1.6 | - |
| `ConsensusInstances` | Aggregate | ConsensusInstances | 9 | 23 | 9 | 5 | 0 | 0 | 1.0 | - |
| `ConsensusProofs` | Aggregate | ConsensusProofs | 9 | 21 | 9 | 5 | 0 | 0 | 1.4 | - |
| `ConsensusProofs.Model` | Aggregate | ConsensusProofs | 15 | 14 | 27 | 14 | 0 | 0 | 1.0 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Model.Canonical` | Aggregate | ConsensusProofs | 5 | 12 | 30 | 1 | 0 | 0 | 1.0 | AcceptedGood, Behaviour, RegimesRealizable |
| `ConsensusProofs.Problem` | Aggregate | ConsensusProofs | 15 | 5 | 53 | 8 | 0 | 0 | 1.1 | AcceptedGood, Behaviour, Faithful, RegimesRealizable |
| `ConsensusProofs.Shape` | Aggregate | ConsensusProofs | 21 | 20 | 14 | 15 | 0 | 0 | 1.2 | - |
| `ConsensusSpec` | Aggregate | ConsensusSpec | 30 | 11 | 0 | 23 | 0 | 0 | 1.2 | - |
| `ConsensusTests` | Aggregate | ConsensusTests | 19 | 29 | 0 | 18 | 0 | 0 | 1.3 | - |
| `CheckDecls` | Tool | check-decls | 329 | 0 | - | 0 | 0 | 0 | - | - |
| `CheckDeclsForeign` | Tool | CheckDeclsTest | 16 | 0 | - | 0 | 0 | 0 | - | - |
| `CheckDeclsTest` | Tool | CheckDeclsTest | 11 | 2 | - | 0 | 0 | 0 | - | - |
| `CheckDeclsTest.Bad` | Tool | CheckDeclsTest | 83 | 1 | - | 0 | 0 | 0 | - | - |
| `CheckDeclsTest.Exports` | Tool | CheckDeclsTest | 14 | 0 | - | 0 | 0 | 0 | - | - |
| `CheckDeclsTest.Good` | Tool | CheckDeclsTest | 34 | 0 | - | 0 | 0 | 0 | - | - |
| `CheckDeclsTest.Proofs.Native` | Tool | CheckDeclsTest | 12 | 0 | - | 0 | 0 | 0 | - | - |
| `CheckFixtures.BadAttr` | Tool | CheckFixtures | 6 | 1 | - | 0 | 0 | 1 | - | - |
| `CheckFixtures.BadAttr.Register` | Tool | CheckFixtures | 6 | 0 | - | 0 | 0 | 1 | - | - |
| `CheckFixtures.BadInit` | Tool | CheckFixtures | 6 | 0 | - | 1 | 0 | 1 | - | - |
| `CheckFixtures.BadLocalSyntax` | Tool | CheckFixtures | 13 | 0 | - | 0 | 0 | 1 | - | - |
| `CheckFixtures.BadMacro` | Tool | CheckFixtures | 7 | 1 | - | 1 | 0 | 1 | - | - |
| `CheckFixtures.BadMacro.A` | Tool | CheckFixtures | 7 | 0 | - | 1 | 0 | 1 | - | - |
| `CheckFixtures.BadScopedSyntax` | Tool | CheckFixtures | 8 | 0 | - | 1 | 0 | 1 | - | - |
| `CheckFixtures.BadSkipKernel` | Tool | CheckFixtures | 2 | 1 | - | 1 | 0 | 0 | - | - |
| `CheckFixtures.BadSkipKernel.A` | Tool | CheckFixtures | 14 | 0 | - | 0 | 0 | 1 | - | - |
| `CheckFixtures.BadTheorem` | Tool | CheckFixtures | 2 | 1 | - | 1 | 0 | 0 | - | - |
| `CheckFixtures.BadTheorem.A` | Tool | CheckFixtures | 9 | 0 | - | 0 | 0 | 1 | - | - |
| `CheckFixtures.Cmp.Axiom` | Tool | CheckFixtures | 15 | 0 | - | 0 | 0 | 1 | - | - |
| `CheckFixtures.Cmp.Challenge` | Tool | CheckFixtures | 13 | 0 | - | 0 | 0 | 1 | - | - |
| `CheckFixtures.Cmp.DefChallenge` | Tool | CheckFixtures | 15 | 0 | - | 0 | 0 | 1 | - | - |
| `CheckFixtures.Cmp.DefSolution` | Tool | CheckFixtures | 17 | 0 | - | 0 | 0 | 1 | - | - |
| `CheckFixtures.Cmp.Good` | Tool | CheckFixtures | 13 | 0 | - | 0 | 0 | 1 | - | - |
| `CheckFixtures.Cmp.Stmt` | Tool | CheckFixtures | 14 | 0 | - | 0 | 0 | 1 | - | - |
| `CheckFixtures.EmptyScope` | Tool | CheckFixtures | 4 | 0 | - | 0 | 0 | 0 | - | - |
| `CheckFixtures.GoodSpec` | Tool | CheckFixtures | 3 | 2 | - | 2 | 0 | 0 | - | - |
| `CheckFixtures.GoodSpec.A` | Tool | CheckFixtures | 85 | 0 | - | 2 | 0 | 1 | - | - |
| `CheckFixtures.GoodSpec.B` | Tool | CheckFixtures | 11 | 1 | - | 1 | 0 | 1 | - | - |
| `CheckFixtures.OrphanLib` | Tool | CheckFixtures | 12 | 0 | - | 0 | 0 | 1 | - | - |
| `CheckFixtures.OrphanLib.Bad` | Tool | CheckFixtures | 13 | 0 | - | 0 | 0 | 1 | - | - |
| `CheckFixtures.Proof` | Tool | CheckFixtures | 24 | 0 | - | 0 | 0 | 1 | - | - |
| `CheckFixtures.ReviewBad` | Tool | CheckFixtures | 2 | 1 | - | 1 | 0 | 0 | - | - |
| `CheckFixtures.ReviewBad.A` | Tool | CheckFixtures | 24 | 0 | - | 0 | 0 | 1 | - | - |
| `CheckFixtures.ReviewEscape` | Tool | CheckFixtures | 30 | 0 | - | 0 | 0 | 1 | - | - |
| `CheckFixtures.RootDecl` | Tool | CheckFixtures | 6 | 1 | - | 1 | 0 | 1 | - | - |
| `CheckFixtures.RootDecl.A` | Tool | CheckFixtures | 9 | 0 | - | 0 | 0 | 1 | - | - |
| `CheckFixtures.SnapA.Defs` | Tool | CheckFixtures | 9 | 0 | - | 0 | 0 | 1 | - | - |
| `CheckFixtures.SnapAuxA.Defs` | Tool | CheckFixtures | 11 | 0 | - | 1 | 0 | 1 | - | - |
| `CheckFixtures.SnapAuxB.Defs` | Tool | CheckFixtures | 11 | 0 | - | 1 | 0 | 1 | - | - |
| `CheckFixtures.SnapB.Defs` | Tool | CheckFixtures | 9 | 0 | - | 0 | 0 | 1 | - | - |
| `CheckFixtures.SnapHidden.Defs` | Tool | CheckFixtures | 10 | 0 | - | 0 | 0 | 1 | - | - |

</details>
