# Spec approval record

## Approval

**Current rule (owner, #2, 2026-10-30): nothing blocks on the owner.** The tag is an agent approval: an agent
other than the change's author (claude-ethlabs, or the amp-orbs coordinator) moves it once the author has done a
fidelity read-back (a subagent, in the author's own session) and CI's fast check is green. The tag message names
the PR, the protected files changed against the previous tag, and the evidence. Before 2026-10-30 the owner
approved, or authorized claude-ethlabs to.

Tag history (`git cat-file -p spec-approved` shows the current message):

| Commit | Tag object | Change | Moved by |
|---|---|---|---|
| `4b7c5148` | | post-reorg trusted surface | claude-ethlabs on Francesco's authorization (2026-10-29) |
| `9c7433b9` | `6549c000` | PR #30: verbatim move to the single library (#5) | claude-ethlabs |
| `c27122cf` | `4e506f96` | PR #43: instance semantics and statements as trusted paths; Goldilocks sheet to `Baseline.lean`; `Derived.lean` protected | claude-ethlabs |
| `1cf90770` | `151658c8` | PR #44: Goldilocks M₁ (FG safety) semantics and statements | claude-ethlabs, after Francesco's statement review |
| `ce9f849` | `068a5194` | PR #46: `Derived.lean` keeps only the sheet's definitions (pure removal) | claude-ethlabs |
| `f98ed97` | `ab7d3566` | PR #49: Goldilocks Common and Frame statements (additions under `Instances/Goldilocks` only) | amp-orbs (coordinator, not the author); first agent approval |

Since #5 the tag `spec-approved` pointed to `9c7433b988576147b46977bc9bab454fc8907c20` (9c7433b9), the head of
PR #30 and the verbatim move of this surface to the single library `ConsensusLean` (section "Move to one library
`ConsensusLean` (#5)" below). Before that, the trusted surface was **approved at
`4b7c51484baa5725301d559d437f22a0ea5ab9a2` (4b7c5148) on 2026-10-29 by claude-ethlabs on Francesco's
authorization**: annotated tag `spec-approved` ("Owner approval (Francesco,
granted to claude-ethlabs 2026-10-29): protected Spec / review statements / challenge / toolchain at 4b7c5148
(post-reorg; verbatim moves + v4.35 internal term differences documented in the reorg evidence)").

The **trusted surface**, checked by CI's `review-boundary` job against the tag (any difference fails), is the
list `trusted_paths` in `scripts/boundaries.toml` (since #5): `ConsensusLean/{Init,Core,Spec,Statements,ToMathlib}`
(each as `X.lean` and `X/**`), `Challenge.lean`, `comparator.json`, `lean-toolchain`, `lake-manifest.json`,
`ConsensusLeanTest/ReviewAxioms.lean`, `ConsensusLeanTest/ReviewGuard.lean`, and since #38 the instance semantics
and statements: for every instance `P` `Instances/<P>/{Spec,Statements}` (file and directory) and
`Instances/<P>/Refinement/Defs.lean`, existing or not; check-boundaries.py requires the `protected` instance
layers to be covered. These are tag-protected, not trusted layers: the Goldilocks `Baseline` modules read
definitions of the generic `Main` and `Lemmas/Problem/Derived.lean` (`FaultsBelow`, `Safe`, `ReadySafeUpTo`)
through a reviewed import exception. `ConsensusLean/Lemmas/Problem/Derived.lean`, which defines only those three, `Agree`, and their
characterising lemmas (which must sit with the unexposed bodies; other derived notions are in the unprotected
`DerivedFacts.lean`), is in `trusted_paths` too (a Lemmas file, so not a trusted layer), so no unreviewed edit changes the definitions the sheet reads (a name scan of the sheet found no other definition
outside the trusted paths that its statements read); its elaboration still depends on the unprotected modules it
imports (a new declaration in `Consensus.Shape`, an instance or a notation there could change how its names
resolve), so the tag freezes the sheet's text and definitions, not everything it imports. The exception is limited to the two `Baseline` modules and does not extend to their importers, so a
milestone statement cannot depend on `Main` or `Lemmas`. **The Goldilocks files at #38 (`Spec/Baseline.lean`, `Statements/Baseline.lean`, moved from `Spec.lean`,
`Statements.lean`; against the tagged files the differences are the one import of the moved Spec and #37's proof
edit at `Statements/Baseline.lean:559` (`Trace.safe_iff.mpr`)) are a pre-foundation baseline, not
approved**: the tag covers them so that every later edit is reviewed; no proof targets them, and approval comes
only with the first slice (#10) re-reviewed against goldilocks `spec/goldilocks-claims.tex`. At `4b7c5148` it was `ConsensusSpec/**`,
`ConsensusSpec.lean`, `ConsensusChallenge.lean`, `comparator.json`, `lean-toolchain`, `lake-manifest.json`,
`ConsensusTests/ReviewAxioms.lean`, `ConsensusTests/ReviewGuard.lean`; the move is recorded in
"Move to one library `ConsensusLean` (#5)" below. The sections between describe the approved surface at
`4b7c5148` under its current paths.
The check infrastructure (`scripts/**`, `.github/**`, `lakefile.toml`; `lakefile.lean` must not exist) is
not covered by the tag: agents maintain it (`TRUST.md`). It is described below because it defines what
the checks enforce.

This record compares `2852f717` (the informal "B1 fixes" review) with the approved commit. It was written
with git, Python and file reads only; the evidence script below reruns every textual claim.
[TRUST.md](../TRUST.md) and [README.md](../README.md) give the fuller contract and assumptions.

## Protected paths and declarations

Every file of the trusted layers (`ConsensusLean/Init.lean`, `ConsensusLean/Spec/`, `ConsensusLean/Statements/`;
`Core` and `ToMathlib` are empty) is part of the claim. Namespaces remain `Consensus.*`.
The Spec import closure excludes project Lemmas, Proofs, Main, Instances, Solution and tests.

| File under `ConsensusLean/Spec/` (`ConsensusSpec/` at `4b7c5148`) | Meaning |
|---|---|
| `Problem/Basic.lean` | Capabilities, output schemas, environments, points, traces, communication logs and systems. |
| `Problem/Network.lean` | Delivery, `Held`/`TxHeld`, partial synchrony, cut/outage networks and eager logs. |
| `Problem/Properties.lean` | Agreement, monotonicity, ready safety, nesting, transaction liveness, resilience and local accountability. |
| `Problem/Regimes.lean` | Numerical `Params`/`Contract`, admissibility, sleepy/healthy/outage regimes and timing accessors. |
| `Problem/Good.lean` | External data, progress, `Behaviour`, adequacy, active witnesses, `Realizable` and `Good`. |
| `Model/Objects.lean` | Authenticated objects, carried-object closure, signers, items and decidable equality. |
| `Model/Protocol.lean` | Public parameters, closed selection, protocol interfaces, selection admissibility and families. |
| `Model/Run.lean` | Events/order, engine state, releases, inboxes, views, persistent slashing protection and reads. |
| `Model/Conditions.lean` | Unforgeability, selection/credential conditions, `ExecutionValid` and engine logs. |
| `Model/System.lean` | Evidence-based conviction, observed collisions, `sysOf` and external PKI/selection data. |
| `Model/Served.lean` | Engine holding at a deadline, `Run.Served`. |
| `Blocks/TimeGrid.lean` | Slots, lengths and times; phases in multiples of Δ. |
| `Blocks/Progress.lean` | Patterns, recurrence windows, `ProgressReq`, `PatternRecurrence` and `NotReadyOn`. |
| `Blocks/Chains.lean` | Headers/chains, roots/digests, structural prefixes, linkage and provenance. |
| `Blocks/Payload.lean` | Transaction encoding/decoding and `ledgerOf`, retaining first occurrences. |
| `Shape/Shape.lean` | Skeletons, closed roles, proposal provenance, duties, `ChainShape` and `ShapeFamily`. |
| `Shape/Compile.lean` | Compile skeleton duties and shape state machines into model protocols. |
| `Shape/Run.lean` | Compiled systems, chain traces, output validity, proposal liveness and `shapeProgress`. |
| `Shape/Claims.lean` | The chain-level safety, liveness, accountability and resilience claims. |
| `Shape/ProgressFit.lean` | Progress fit and tolerance, including participation and bad-proposer tolerance. |
| `Shape/Active.lean` | Progress activity, `BadProposerEvery` and `RealizableActive` witnesses. |
| `Shape/Accepted.lean` | Acceptance: claims, admissible numbers, service, progress fit and tolerance. |
| `../Statements/Review.lean` (`Statements.lean` at `4b7c5148`) | The four review propositions below. |

| Other protected path | Meaning |
|---|---|
| `ConsensusLean/Init.lean` | Curated public imports (`Mathlib.Init`, `Mathlib.Tactic.Common`); owns no declarations. Replaces the import-only root `ConsensusSpec.lean` of `4b7c5148` in the list. |
| `Challenge.lean` | Non-default comparator challenge: imports exactly `ConsensusLean.Statements.Review`; four placeholder proofs. |
| `comparator.json` | Challenge/solution modules, four theorem names and three permitted axioms. |
| `ConsensusLeanTest/ReviewAxioms.lean` | Compiled statement/type, binder-kind, completeness and exact axiom pins. |
| `ConsensusLeanTest/ReviewGuard.lean` | Shared implementation of those statement/completeness checks, also used by negative fixtures. |
| `lean-toolchain` | Exact Lean version: `leanprover/lean4:v4.35.0`. |
| `lakefile.toml` | Libraries, default targets, Mathlib requirement, Lean options and checker executable. |
| `lake-manifest.json` | Exact nine dependency revisions, URLs and configuration/manifest paths. |
| `lakefile.lean` | Must not exist at the repository root; the TOML-only Lake boundary rejects it. |
| `scripts/**` | The trust-check driver, tools, reviewed data and positive/negative controls described next. |
| `.github/**` | CI definitions and CODEOWNERS; changes can alter enforcement itself. |

The review propositions are in `ConsensusLean/Statements/Review.lean`, inside
`namespace Consensus.Review` with `open Consensus.Shape Consensus.Model Consensus.Blocks`:

```lean
def AcceptedGood : Prop :=
  ∀ {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    {F : ShapeFamily O Info} {K : Contract ProgressReq}, Accepted F K →
    ∀ (V : Type) [Fintype V] [DecidableEq V],
      Good (sysOf O (compiled F) V) (shapeProgress F V) K

def RegimesRealizable : Prop :=
  ∀ {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    (F : ShapeFamily O Info) (K : Contract ProgressReq),
    K.params.Admissible → ProgressFits K F → ProgressTolerant O K →
    ∀ (V : Type) [Fintype V] [DecidableEq V], 5 ≤ Fintype.card V → RealizableActive F K V

def LogFaithful : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O}
    (r : (sysOf O F V).Run),
    (∀ v o t, ((sysOf O F V).log r).sent v ⟨r.1, o⟩ t ↔ r.2.releases v o t) ∧
    (∀ v o t, ((sysOf O F V).log r).recv v ⟨r.1, o⟩ t ↔ r.2.receives v o t) ∧
    (∀ v m t, ((sysOf O F V).log r).sent v m t ∨ ((sysOf O F V).log r).recv v m t →
      ∃ o, m = ⟨r.1, o⟩) ∧
    ((sysOf O F V).log r).inbox = r.2.inbox

def HeldIffServed : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}
    (rho : Run F E), rho.ExecutionValid → ∀ {w : V}, w ∈ rho.honest →
    ∀ (o : (protoOf F E).Object) {d : Time}, d ≤ rho.horizon →
      (CommLog.Held rho.point rho.log w o d ↔ rho.Served w o d)

```

| Proposition (`Consensus.Review.*`) | What it says; proof |
|---|---|
| `AcceptedGood` | Every accepted shape gives an L0 `Good` system for every finite validator type. `acceptedGood` uses `Consensus.Shape.Accepted.good`. |
| `RegimesRealizable` | Admissibility, progress fit and tolerance give active regime witnesses for ≥5 validators, including bad-proposer windows. `regimesRealizable` uses `Consensus.Shape.regimes_realizable`. |
| `LogFaithful` | The system log records exactly engine releases, receipts and inboxes, with only the run's environment tag. `logFaithful` uses `Consensus.Model.sysOf_log_faithful`. |
| `HeldIffServed` | On valid runs, for honest nodes and deadlines within the horizon, L0 holding equals engine service. `heldIffServed` uses `Consensus.Model.Run.held_iff_served`. |

The four lower-case proofs are in `Solution.lean`. The source theorems
are in `ConsensusLean/Main.lean`, `ConsensusLean/Proofs/RegimesRealizable/Main.lean` and
`ConsensusLean/Proofs/Faithful/Main.lean` respectively (the last file supplies both model theorems).
`ReviewAxioms.lean` compares each definition body to its source theorem's type by
alpha-equality, plus an explicit comparison of all binder kinds (`{}`, `()`, `[]`, `⦃⦄`).
`ReviewGuard.checkComplete` requires a pair for every non-proof, non-matcher constant
owned by Statements, including private constants and other namespaces.
The guarded axiom output pins both sets of four proofs to exactly
`propext`, `Classical.choice` and `Quot.sound`.

The comparator matches the challenge against `Solution`, limits axioms,
replays exports in a sandbox and requires identical reachable constants across exports.
Both sides use this tree's Spec. The snapshot and the approval of each change detect Spec drift.
The challenge's `sorry` proofs are deliberate and excluded from default libraries.

`lakefile.toml` defaults to `ConsensusLean` (since #5; at `4b7c5148`: Spec, Proofs, Instances and Tests);
`ConsensusLeanTest` is the `testDriver`; `Solution`, `Challenge` and the fixture libraries are non-default. Its six options are `pp.unicode.fun=true`,
`relaxedAutoImplicit=false`, `weak.linter.mathlibStandardSet=true`,
`weak.linter.flexible=false`, `weak.linter.style.header=false` and
`maxSynthPendingDepth=3`. `scripts/pins.toml` independently pins all nine manifest packages.

The `scripts/**` stack is:

| Files/groups | Review purpose |
|---|---|
| `check.sh` | Driver and self-tests: pins, build/freshness, imports, declarations, Spec surface, sequential replay, review pins, grep, vendor hashes, comparator, sandboxed Lake checks and docs. |
| `check-boundaries.py` | Parsed imports, layer matrix and exceptions, Init chain, generated-root listing, library inventory, trusted-path coverage and base-name provenance constraints. |
| `check-pins.py` | Toolchain, dependency manifest, clean checkouts and actual Lake resolution. |
| `SpecSurface.lean` | Snapshot, persisted extensions, theorem hygiene, constant-free parents, statement inventory and reachability; loads no checked extension state. |
| `CheckDecls.lean` | Vendored EthLib declaration/axiom checker with three local patches (TRUST.md); detects unfinished proofs, unsafe/opaque/partial declarations and forbidden implementation hooks. |
| `test_check_decls.sh`, `CheckDeclsTest.lean`, `CheckDeclsForeign.lean`, `CheckDeclsTest/**` | EthLib checker self-tests, including deliberately bad and exempt declarations. |
| `LICENSE.EthLib` | CC0 licence for the vendored checker and tests. |
| `fixtures/**` | Import, surface, review guard, grep, pins, docs, comparator and Lake replay controls. Deliberately invalid fixtures must fail. |
| `boundaries.toml` | Reviewed libraries, layer matrix and exceptions, base set, fixture exclusions, `trusted_paths` and check configuration. |
| `pins.toml` | Reviewed exact toolchain and dependency provenance, including URLs/revisions/config paths. |
| `spec-snapshot.txt` | Reviewed readable declarations and structural type/value hashes for every Spec-owned constant; header fixes pins/options. Proof values are omitted. |
| `spec-extensions.txt` | Reviewed persisted-extension whitelist; not a complete audit of non-persisted source effects. |
| `spec-theorems.txt` | Reviewed exceptions to Spec theorem hygiene: the two Countable instances for ParentRef and Header. |
| `check_decls_baseline.txt` | Reviewed checker exceptions: only the two ReviewGuard meta checks' opaque Meta API reachability. Stale exceptions fail. |
| `vendor.sha256` | Reviewed SHA-256 pins of all nine EthLib copies, including fixtures/licence. |

The nine vendor files match the recorded reuse-study source byte for byte; the
verification command below checks both source bytes and hashes. This establishes
copy identity, not an upstream commit: that source directory has no git metadata.

At `4b7c5148`, `.github/CODEOWNERS` listed the protected paths, `workflows/ci.yml` ran the full check
stack and review boundary on every push, and `workflows/paranoid.yml` added weekly/manual external-checker
replay. Since issue #14, `ci.yml` runs the fast tier and the review boundary (trusted surface only), and
`full.yml` runs everything nightly, including the comparator with `--paranoid`.

## What changed since 2852f717

`3c740dc4` upgrades Lean/Mathlib; `b63acb10` reorganizes the libraries;
`9babb88c` adds the review interface; later commits replace/harden the checks.
At the baseline the actual directories were `ConsensusProblem/`, `ConsensusModel/`,
`ConsensusModelProofs/`, `ConsensusBlocks/`, `ConsensusShape/` and `ConsensusShapeTests/`.
There was no `Spec/` directory at `2852f717`; that name appears in reorganization plans.

### Spec source changes

Of the 20 whole-file Spec moves, 2 are byte-identical and 15 change only imports.
No namespace, `module`, `public` or `@[expose]` normalization was needed to get those counts.
The two Mathlib import renames are `Data.Countable.Basic` → `Basic.Countable.Basic`
in Chains and `Data.Countable.Defs` → `Basic.Countable.Defs` in Protocol.

These are all remaining Spec source changes, beyond imports and new file framing:

- `Model/Protocol.lean` removes `SelSpec.admits_exists`. Its declaration and proof
  move unchanged to `ConsensusProofs/Model/Protocol.lean`.
- `Shape/Accepted.lean` removes `Accepted.behaviour` and `Accepted.good`. Both
  declaration/proof blocks move unchanged to `ConsensusProofs/Shape/Accepted.lean`.
  The `Accepted` structure is unchanged; the header now names the proof file.
- `Shape/Run.lean` rewrites the `mono` and `shrink` proof fields of `shapeProgress`,
  in both `recur` and `notReadyAtMost` cases, to inline interval inequalities.
  This removes calls to `PatternRecurrence.mono/shrink` and `NotReadyOn.mono/shrink`
  so Spec no longer imports the proof library. The data fields and proposition types stay the same.
- New `Model/Served.lean` extracts `Run.Served` from
  `ConsensusModelProofs/Faithful.lean`. The definition block and its surrounding
  namespace/variable context agree; the file framing is new.
- New `Shape/Active.lean` extracts `progLen`, `ProgressActive`, `BadProposerEvery`
  and `RealizableActive` from `ConsensusShape/Realizable.lean`. All four blocks
  agree exactly, with the same namespace/open/variable context. Proofs remain in Proofs.
- New `Statements.lean` introduces four `Prop` wrappers for existing theorem types.
  These are new declarations, not file moves. Their source types were in
  `ConsensusShape/Accepted.lean` (`Accepted.good`),
  `ConsensusShape/Realizable.lean` (`regimes_realizable`) and
  `ConsensusModelProofs/Faithful.lean` (`sysOf_log_faithful`, `Run.held_iff_served`).

Thus there are non-verbatim source edits. The existing contract definitions have
no changed non-proof bodies in this source comparison. This statement comes from
the full residual diffs and extraction checks below; it is not a claim that all
compiled terms are identical across Lean versions.

### Snapshot evidence and its limits

There is **no production snapshot in git at `2852f717`**, under this or another name.
The only snapshot/canonical data there are `scripts/fixtures/goodspec.{snapshot,canonical}`
and `scripts/fixtures/snapA.{snapshot,canonical}`. The old driver's comment says the
real Spec snapshot gate awaits the reorganization.
Consequently `git diff 2852f717 4b7c5148 -- scripts/spec-snapshot.txt` is an addition,
not an old/new declaration equivalence check. The new file has 24 module headers
(root plus 23 files) and 1,161 constant records.

The earliest committed production snapshot is `1eb8b6ec:scripts/spec-snapshot.txt`,
already on v4.35.0 but describing the old library layout. Comparing it with `4b7c5148`:

- Toolchain, all nine package revisions and all six options in the header are identical.
  Against `2852f717`'s configuration, toolchain and all nine revisions changed; options did not.
- The `## ` lines change module names/order: 21 headers become 24, including the new root,
  Served and Statements; the old Realizable surface becomes Active.
  Namespace-qualified public constant names do not acquire the new module prefix.
- Records change from 1,271 to 1,161: 117 disappear, 7 appear, 1,154 names are shared.
  Of the removed records, 99 are proof declarations and 18 are definitions/auxiliaries.
  Two removed private matchers reappear with owning-module names under ConsensusSpec;
  the other 115 records leave the Spec inventory.
  The other five additions are Served and the four review definitions.
- Of the shared records, 1,150 agree exactly. Four have raw hash changes:
  `Consensus.Blocks.instReprParentRef.repr`, `Consensus.instReprCapability.repr`,
  `Consensus.Capability.noConfusion` and `Consensus.Capability.noConfusionType`.
  The two Repr entries retain their readable text alongside the private matcher renames.
  Basic's source is byte-identical despite the two generated noConfusion hash differences.

This intermediate diff is not merely renamed `## ` headers. It also changes the
protected declaration inventory and raw hashes. The command below prints all four
residual records. The separate upgrade audit uses a frozen canonical serializer;
it supplies the stronger old/new term evidence, rather than treating these snapshots
as identical. Older scratch readable/canonical dumps exist at
`/srv/runs/fradamt/consensus-lean/reorg/snapshot-before{,-canonical}.txt`;
they use a different format and are not a tagged git baseline.

### v4.35 internal terms: existing audit evidence

Read [/srv/runs/fradamt/consensus-lean/reorg2/expected-diffs.md](/srv/runs/fradamt/consensus-lean/reorg2/expected-diffs.md)
and [/srv/runs/fradamt/consensus-lean/reorg2/dep-audit.md](/srv/runs/fradamt/consensus-lean/reorg2/dep-audit.md).
These are shared-box run artefacts, not tracked repository files.
Their reported kernel probes were read for this guide, not rerun.

The audit compares all 2,535 project constants: 2,492 unchanged, 43 changed,
0 unresolved. Dependency closure: 1,093 old, 1,190 new; 1,063 unchanged,
24 changed, 6 old-only and 103 new-only. All 109 one-sided dependencies are reached
only through proved-equivalent changed constants in the cut-graph traversal.
All 43 project and 24 dependency changes have kernel-checked equivalence probes.
There are no rename-map or proof-subterm-only cases. Of 34 dependency module moves,
33 have identical type/value hashes; `PartialOrder.ofSetLike` is the changed one.

The 43 project constants, grouped (all names have prefix `Consensus.`):

| Count | Constants/kind |
|---|---|
| 32 | Both `casesOn` and `recOn` for `Behaviour`, `CommLog.Delivers`, `CommLog.EagerFrom`, `Good`, `Model.Run.ExecutionValid`, `Model.Run.SameTrace`, `Params.Admissible`, `Realizable`, `Shape.Accepted`, `Shape.GoldilocksExtraAt`, `Shape.RealizableActive`, `Shape.ShapeClaimsAt`, `System.Adequate`, `System.Laws`, `Trace.Laws`, `Trace.PrefixOf`. |
| 8 | Both `noConfusion` and `noConfusionType` for `Capability`, `Shape.GKind`, `Shape.GOut` and `Shape.Tests.Problem.G3`. |
| 2 | `Model.Obj.decEq.match_1` and `Model.Obj.decEqList.match_1`: Decidable matcher types/values. |
| 1 | `Model.protects`: elaborated Option/Fin decision/order instances. |

The command below checks this list against the audit.

The dependency changes comprise 21 Decidable-family/eliminator/conditional/decision-procedure
or matcher constants, 2 enum noConfusion helpers and `PartialOrder.ofSetLike`.
Lean changes `Decidable` from an inductive to a Boolean/reflection structure.
The audit uses an isomorphism with both round trips, preserved decisions and old
eliminator/matcher equations. Generated Prop-structure eliminators have pointwise
kernel proofs against parsed, round-tripped and kernel-typed exact old terms.
Enum helpers use constructor cases. `protects` is definitionally equal to its exact
old elaborated value. The audit records 0 unexpected project differences.

### Configuration and trust infrastructure

- `lean-toolchain`: v4.34.1 → v4.35.0. `lakefile.toml`: Mathlib v4.34.1 → v4.35.0;
  six old default libraries become four role libraries; challenge, EthLib tests and
  check-decls executable are added. All six Lean options are unchanged.
- `lake-manifest.json`: all nine exact revisions change; format 1.2.0 → 1.3.0;
  stale package name `«available-chain»` → `«consensus-lean»`; Cli input revision
  v4.34.0 → v4.35.0. Pins retain the reviewed concrete resolutions.
- `ConsensusSpec.lean` is a new import-only collection, replacing the old role-mixed
  roots' Spec coverage. `comparator.json` and `ConsensusChallenge.lean` are new.
- `ReviewAxioms.lean` and `ReviewGuard.lean` are new compiled guards, not moves of
  `CheckConsensusAxioms.lean`. The old file audited global axiom use; declaration
  checks/replay now cover that role. The new guards add the four statement pairs,
  exact binder checks and owning-module completeness.
- `scripts/CheckSpec.lean` is removed. Its responsibilities are split across
  import/pin Python tools, `SpecSurface.lean`, the EthLib checker and `check.sh`.
  Reviewed data files are added. The driver is substantially replaced; fixture
  groups are added/reworked for the new checks.
- `.github/CODEOWNERS`, `workflows/ci.yml` and `workflows/paranoid.yml` are all new
  relative to `2852f717`.
- After 4b7c5148, the CI-tiers change (issue #14) gives `scripts/check.sh` modes (`--fast` per PR,
  `--full` nightly, `--changed` locally) and the comparator `--paranoid` (full mode), adds
  `scripts/check-changed.sh` and the import-graph output of `check-imports.py`, splits CI into
  `ci.yml` (fast tier + review boundary, which warns while the tag is missing) and `full.yml`
  (nightly; replaces `paranoid.yml`), adds `notify.yml`, and sets the CODEOWNERS owner to `@fradamt`.

### Complete per-file provenance at 4b7c5148

`V` = byte-identical file/copy; `I` = only import-line changes;
`R` = real textual change; `S` = extracted declaration blocks agree, new file framing;
`N` = new file/declarations, no old file unless a source is named.
“Same” means the destination path also existed at `2852f717`.
Copied fixture configurations follow git's copy detection, not an inferred semantic origin.
The absent root `lakefile.lean` is protected too. This inventory fixes the historical
comparison; the CI-tier additions above must also be reviewed.

| File at 4b7c5148 | Source at 2852f717 | Class |
|---|---|---|
| `.github/CODEOWNERS` | — | N |
| `.github/workflows/ci.yml` | — | N |
| `.github/workflows/paranoid.yml` | — | N |
| `ConsensusChallenge.lean` | — | N |
| `ConsensusSpec.lean` | — | N |
| `ConsensusSpec/Blocks/Chains.lean` | `ConsensusBlocks/Chains.lean` | I |
| `ConsensusSpec/Blocks/Payload.lean` | `ConsensusBlocks/Payload.lean` | I |
| `ConsensusSpec/Blocks/Progress.lean` | `ConsensusBlocks/Progress.lean` | I |
| `ConsensusSpec/Blocks/TimeGrid.lean` | `ConsensusBlocks/TimeGrid.lean` | I |
| `ConsensusSpec/Model/Conditions.lean` | `ConsensusModel/Conditions.lean` | I |
| `ConsensusSpec/Model/Objects.lean` | `ConsensusModel/Objects.lean` | V |
| `ConsensusSpec/Model/Protocol.lean` | `ConsensusModel/Protocol.lean` | R |
| `ConsensusSpec/Model/Run.lean` | `ConsensusModel/Run.lean` | I |
| `ConsensusSpec/Model/Served.lean` | `ConsensusModelProofs/Faithful.lean` | S |
| `ConsensusSpec/Model/System.lean` | `ConsensusModel/System.lean` | I |
| `ConsensusSpec/Problem/Basic.lean` | `ConsensusProblem/Basic.lean` | V |
| `ConsensusSpec/Problem/Good.lean` | `ConsensusProblem/Good.lean` | I |
| `ConsensusSpec/Problem/Network.lean` | `ConsensusProblem/Network.lean` | I |
| `ConsensusSpec/Problem/Properties.lean` | `ConsensusProblem/Properties.lean` | I |
| `ConsensusSpec/Problem/Regimes.lean` | `ConsensusProblem/Regimes.lean` | I |
| `ConsensusSpec/Shape/Accepted.lean` | `ConsensusShape/Accepted.lean` | R |
| `ConsensusSpec/Shape/Active.lean` | `ConsensusShape/Realizable.lean` | S |
| `ConsensusSpec/Shape/Claims.lean` | `ConsensusShape/Claims.lean` | I |
| `ConsensusSpec/Shape/Compile.lean` | `ConsensusShape/Compile.lean` | I |
| `ConsensusSpec/Shape/ProgressFit.lean` | `ConsensusShape/ProgressFit.lean` | I |
| `ConsensusSpec/Shape/Run.lean` | `ConsensusShape/Run.lean` | R |
| `ConsensusSpec/Shape/Shape.lean` | `ConsensusShape/Shape.lean` | I |
| `ConsensusSpec/Statements.lean` | source theorem types; see Spec source changes above | N |
| `ConsensusTests/ReviewAxioms.lean` | — | N |
| `ConsensusTests/ReviewGuard.lean` | — | N |
| `comparator.json` | — | N |
| `lake-manifest.json` | same | R |
| `lakefile.toml` | same | R |
| `lean-toolchain` | same | R |

`scripts/**` at 4b7c5148 (235 files): 203 new (`N`), 16 byte-identical copies (`V`, the
vendored EthLib checker and fixture copies of the root configuration), 16 changed (`R`, mostly
fixture lakefiles/manifests derived from the root ones). The evidence script below prints the
full per-file list.

### Rerunnable evidence checks

Run from the repository root. This is the read-only command used for the file
classifications, residual Spec diffs, split-block identity, snapshot comparison and
vendor identity. It invokes no Lean tools. `N` rows in its raw inventory include
the two `S` extractions explained above.

<details><summary>Evidence script (read-only; git + Python)</summary>

```sh
python3 - <<'PY'
from pathlib import Path
import collections, difflib, hashlib, re, subprocess, tomllib
A, B = "2852f717", "4b7c5148"
def git(*args):
    return subprocess.check_output(["git", *args], text=True)
def get(r, p):
    return subprocess.check_output(["git", "show", r + ":" + p]).decode("utf-8")
def paths(r):
    return git("ls-tree", "-r", "--name-only", r).splitlines()
def norm(s):
    return "".join(l for l in s.splitlines(True)
                   if not re.match(r"^(?:public )?import ", l))
roots = {"ConsensusSpec.lean", "ConsensusChallenge.lean", "comparator.json",
         "lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json",
         "ConsensusTests/ReviewAxioms.lean", "ConsensusTests/ReviewGuard.lean"}
old, origins = set(paths(A)), {}
for line in git("diff", "-M", "-C", "--find-copies-harder",
                "--name-status", A, B).splitlines():
    status, *ps = line.split("\t")
    if status.startswith(("R", "C")):
        origins[ps[-1]] = ps[0]
counts = collections.Counter()
for p in paths(B):
    if not (p in roots or p.startswith(("ConsensusSpec/", "scripts/", ".github/"))):
        continue
    src = p if p in old else origins.get(p)
    c = "N"
    if src:
        x, y = get(A, src), get(B, p)
        c = "V" if x == y else "I" if norm(x) == norm(y) else "R"
        if p.startswith("ConsensusSpec/"):
            counts[c] += 1
            if c == "R":
                print("".join(difflib.unified_diff(
                    norm(x).splitlines(True), norm(y).splitlines(True),
                    fromfile=src, tofile=p)))
    print(c, p, "<-", src or "(new)")
print("Whole-file Spec moves:", dict(counts))
assert counts == {"V": 2, "I": 15, "R": 3}
assert "lakefile.lean" not in old and "lakefile.lean" not in paths(B)
def block(t, kind, name):
    return re.search(r"^" + kind + " " + re.escape(name) +
                     r"\b.*?(?=\n\n|\Z)", t, re.M | re.S).group()
for src, dst, kind, names in [
    ("ConsensusModelProofs/Faithful.lean", "ConsensusSpec/Model/Served.lean",
     "def", ["Served"]),
    ("ConsensusShape/Realizable.lean", "ConsensusSpec/Shape/Active.lean",
     "def", ["progLen", "ProgressActive", "BadProposerEvery"]),
    ("ConsensusShape/Realizable.lean", "ConsensusSpec/Shape/Active.lean",
     "structure", ["RealizableActive"]),
    ("ConsensusShape/Accepted.lean", "ConsensusSpec/Shape/Accepted.lean",
     "structure", ["Accepted"]),
    ("ConsensusModel/Protocol.lean", "ConsensusProofs/Model/Protocol.lean",
     "theorem", ["admits_exists"]),
    ("ConsensusShape/Accepted.lean", "ConsensusProofs/Shape/Accepted.lean",
     "theorem", ["Accepted.behaviour", "Accepted.good"]),
]:
    for name in names:
        assert block(get(A, src), kind, name) == block(get(B, dst), kind, name)
        print("EXACT BLOCK", name, src, "->", dst)
print("Old snapshot candidates:",
      [p for p in paths(A) if re.search(r"snap|canon", p, re.I)
       and not p.endswith(".lean")])
assert (tomllib.loads(get(A, "lakefile.toml"))["leanOptions"] ==
        tomllib.loads(get(B, "lakefile.toml"))["leanOptions"])
def records(t):
    header, modules, out, name = [], [], {}, None
    for line in t.splitlines(True):
        if line.startswith("## "):
            modules.append(line.strip())
            name = None
        elif re.match(r"^(def|theorem|ctor|recursor|induct) ", line):
            name = line.split()[1]
            out[name] = line
        elif name:
            out[name] += line
        elif not modules:
            header.append(line)
    return "".join(header), modules, {k: v.rstrip() for k, v in out.items()}
ah, am, ar = records(get("1eb8b6ec", "scripts/spec-snapshot.txt"))
bh, bm, br = records(get(B, "scripts/spec-snapshot.txt"))
assert ah == bh
added, removed, shared = br.keys()-ar.keys(), ar.keys()-br.keys(), ar.keys()&br.keys()
changed = sorted(k for k in shared if ar[k] != br[k])
assert (len(ar), len(br), len(added), len(removed), len(shared), len(changed)) == (
    1271, 1161, 7, 117, 1154, 4)
print("Snapshot headers identical; module counts:", len(am), len(bm))
print("Added:", sorted(added))
print("Removed by kind:", collections.Counter(ar[k].split()[0] for k in removed))
for k in changed:
    print(k, "\nOLD:", ar[k], "\nNEW:", br[k])
vendor = Path("/srv/runs/fradamt/consensus-lean/reuse/src/EthLib")
for line in get(B, "scripts/vendor.sha256").splitlines():
    if not line or line.startswith("#"):
        continue
    expected, p = line.split()
    data = subprocess.check_output(["git", "show", B + ":" + p])
    src = vendor / ("LICENSE" if p == "scripts/LICENSE.EthLib" else p)
    assert hashlib.sha256(data).hexdigest() == expected
    assert data == src.read_bytes()
    print("VERIFIED HASH + SOURCE", p)
audit = Path("/srv/runs/fradamt/consensus-lean/reorg2/expected-diffs.md").read_text()
names = re.findall(r"^- diff: `([^`]+)`", audit, re.M)
assert len(names) == 43
eliminators = [n.removesuffix(".casesOn") for n in names if n.endswith(".casesOn")]
assert len(eliminators) == 16
assert set(eliminators) == {"Consensus." + n for n in [
    "Behaviour", "CommLog.Delivers", "CommLog.EagerFrom", "Good",
    "Model.Run.ExecutionValid", "Model.Run.SameTrace", "Params.Admissible",
    "Realizable", "Shape.Accepted", "Shape.GoldilocksExtraAt",
    "Shape.RealizableActive", "Shape.ShapeClaimsAt", "System.Adequate",
    "System.Laws", "Trace.Laws", "Trace.PrefixOf"]}
assert all(n + ".recOn" in names for n in eliminators)
print("Both casesOn/recOn for:", ", ".join(eliminators))
PY
```

</details>

The git-only starting checks were:

```sh
git diff -M -C --find-copies-harder --name-status 2852f717 4b7c5148
git ls-tree -r --name-only 2852f717
git log --reverse --oneline 2852f717..4b7c5148
git log --all --oneline -- scripts/spec-snapshot.txt
git diff 2852f717 4b7c5148 -- lean-toolchain lakefile.toml lake-manifest.json
git diff 1eb8b6ec 4b7c5148 -- scripts/spec-snapshot.txt
```

## Move to one library `ConsensusLean` (#5)

Approved by moving the tag `spec-approved` from `4b7c5148` to the head of PR #30 (`git cat-file -p spec-approved`
shows the commit and the message):
- old: commit `4b7c51484baa5725301d559d437f22a0ea5ab9a2`;
- new: commit `9c7433b988576147b46977bc9bab454fc8907c20` (tag object `6549c000aab70915fe25302b224f95ee7c3dcbc3`,
  tagger `fradamt-agent` (the shared agent account), 2026-10-29 22:57:40 UTC);
- main: the squash merge `81832ec49b98485fe279ccd8d6a2888da9c38c8d` (81832ec4) has the same tree as 9c7433b9
  (`0065be7e`). 9c7433b9 is not on main (PR #30 was squash-merged), but the tag keeps it reachable.

The move is a pure rename/move of the trusted surface with machine-checked equality of the compiled statements,
which Francesco's rule lets claude-ethlabs approve; a change in meaning needs his review. Old and new paths:

| At `4b7c5148` | Since #5 |
|---|---|
| `ConsensusSpec/{Problem,Model,Blocks,Shape}/*.lean` | `ConsensusLean/Spec/{Problem,Model,Blocks,Shape}/*.lean` (same file names) |
| `ConsensusSpec/Statements.lean` | `ConsensusLean/Statements/Review.lean` |
| `ConsensusSpec.lean` (import-only root) | removed; the generated root `ConsensusLean.lean` (not trusted) imports every module |
| `ConsensusChallenge.lean` | `Challenge.lean` (imports exactly `ConsensusLean.Statements.Review`) |
| `ConsensusTests/ReviewAxioms.lean`, `ReviewGuard.lean` | `ConsensusLeanTest/ReviewAxioms.lean`, `ReviewGuard.lean` |
| `comparator.json` | same path; `challenge_module` `Challenge`, `solution_module` `Solution` |
| — | `ConsensusLean/Init.lean` (new, trusted): `public import Mathlib.Init`, `public import Mathlib.Tactic.Common` |

The trusted paths now live in one place, `trusted_paths` in `scripts/boundaries.toml`; CI's `review-boundary`
checks the union of that list at the PR head and at the tag.

**What changed in the trusted files** (`git diff -M 4b7c5148 spec-approved` on the old and new paths):
- module names in `import` lines and in doc comments (a few comments re-wrapped to 100 columns), and
  `ReviewAxioms`' `checkComplete` module argument;
- `Spec/Problem/Basic.lean` and `Spec/Model/Objects.lean` (the two Spec modules that import no project module)
  gain one last import, `public import ConsensusLean.Init`. Both already reached `Mathlib.Init` and
  `Mathlib.Tactic.Common` through their Mathlib imports (same 1562-module closure), so the import adds no
  constant, instance or attribute; as the last import it does not reorder the modules loaded before it;
- `Challenge.lean` imports the statements module instead of the old Spec root; `comparator.json` names the new
  modules.

**Machine-checked equality.** A canonical dump of every constant owned by every project module (2556
constants: Spec, Statements, Lemmas, Proofs, Main, Instances, Solution, tests), with the serializer of
`2852f717:scripts/CheckSpec.lean` (binder names and mdata dropped; binder kinds, universe parameters by index,
literals and projections kept) extended to write proof terms too, was taken at `888664e6` (old layout) and at
the PR head. Old names were normalised through the module map (`_private.<M>.0.x` names carry module names).
Result (`compare.py`):
- the same 2556 names, after the suffix rename `_consensusTests` → `_consensusLeanTest` of two derived instance
  names in `ConsensusLeanTest/Leaks.lean` (Lean derives the suffix from the root module name);
- all 2556 constants identical in kind, universe count, type and value, proof terms included;
- all 1161 constants of `Init`/`Spec`/`Statements` (the snapshot's 1161 records) identical including their
  (mapped) owning module;
- 9 realized `eq_1` equation lemmas (8 in tests, `Consensus.Model.mempool.eq_1` in Lemmas) are owned by another
  module that also realizes them; their types and values are identical.

`scripts/spec-snapshot.txt` changes only in module headers (`## ConsensusSpec.*` → `## ConsensusLean.Spec.*`,
the root header removed, `## ConsensusLean.Init` added), in the two private matchers whose names carry their
module (`_private.ConsensusSpec.Blocks.Chains.0…` and `_private.ConsensusSpec.Problem.Basic.0…`), and in the
value hash of the two `Repr` instances that call them (`instReprParentRef.repr`, `instReprCapability.repr`), and in
the raw hashes of `Consensus.Capability.noConfusionType`: its universe parameter has a hygienic name that contains
the module name (`v._@.ConsensusLean.Spec.Problem.Basic._hygCtx._hyg.5`); the canonical dump numbers universe
parameters and finds it identical. 48 header lines (24 removed, 24 added), 3 constants, nothing else.

The full tier (kernel replay of every leaf, `lake check`, `lake comparator --paranoid` with the new
`comparator.json`) passed on the PR branch (run 40962983080), on a trusted surface identical to the approved one.
Reviews (PR #30): Codex gpt-6-astra and Claude Opus, three rounds, both APPROVE.

Evidence files (kept): `/srv/runs/fradamt/consensus-lean/foundation-impl/single-library/`
(`CanonDump.lean`, `map.tsv`, `canon-before.tsv.gz`, `canon-after.tsv.gz`, `compare.py`, `compare.out`).

## Verifying this approval

```sh
git fetch origin --tags
git cat-file -p spec-approved                      # annotated tag, object 9c7433b9 (before #5: 4b7c5148)
# the 4b7c5148 approval (old paths)
git diff -M 2852f717 4b7c5148 -- ConsensusSpec ConsensusSpec.lean ConsensusChallenge.lean comparator.json lean-toolchain lake-manifest.json ConsensusTests/ReviewAxioms.lean ConsensusTests/ReviewGuard.lean
git diff 1eb8b6ec 4b7c5148 -- scripts/spec-snapshot.txt
# the current surface (trusted_paths of scripts/boundaries.toml)
mapfile -t protected < <(python3 -I -c 'import tomllib; print("\n".join(tomllib.load(open("scripts/boundaries.toml", "rb"))["checks"]["trusted_paths"]))')
GIT_LITERAL_PATHSPECS=1 git diff spec-approved origin/main -- "${protected[@]}"   # empty while main is covered
```

The nightly `full.yml` run on main (`gh run list --workflow full.yml --branch main`) is the correctness
evidence for the approved surface: kernel replay, `lake check` and `lake comparator --paranoid`.

## Later changes to the trusted surface

Once the tag exists, `review-boundary` fails on a PR whose trusted surface differs from the tag, so such a
change is approved **before** merge. The author does a fidelity read-back (a subagent, in the author's own
session: the Lean read back into prose against the reference, including the `spec-snapshot.txt` diff) and gets
the fast check green; then an agent other than the author (claude-ethlabs, or the amp-orbs coordinator) checks
the protected diff below, moves the tag to the PR head with a message naming the PR, the protected files changed
and the evidence, and re-runs the PR's failed job:

```sh
git fetch origin pull/<pr>/head
paths() { git show "$1:scripts/boundaries.toml" | python3 -I -c 'import sys, tomllib; print("\n".join(tomllib.loads(sys.stdin.read())["checks"].get("trusted_paths", [])))' 2>/dev/null; }
mapfile -t protected < <({ paths FETCH_HEAD; paths spec-approved; } | sort -u)
GIT_LITERAL_PATHSPECS=1 git diff spec-approved FETCH_HEAD -- "${protected[@]}"
git tag -f -a spec-approved -m "spec-approved: <PR>; moved by <agent>; protected files changed: <...>; evidence: <...>" FETCH_HEAD && git push -f origin spec-approved
gh run rerun <run-id> --failed
```

The job compares the trusted surface only, so the approval carries over to the merge or squash commit as
long as main's trusted surface did not change meanwhile (otherwise the PR is updated and re-approved).
