# Spec approval record

## Approval

The trusted surface was **approved at `4b7c51484baa5725301d559d437f22a0ea5ab9a2` (4b7c5148) on 2026-10-29
by claude-ethlabs on Francesco's authorization**: annotated tag `spec-approved` ("Owner approval (Francesco,
granted to claude-ethlabs 2026-10-29): protected Spec / review statements / challenge / toolchain at 4b7c5148
(post-reorg; verbatim moves + v4.35 internal term differences documented in the reorg evidence)").

The **trusted surface**, checked by CI's `review-boundary` job against the tag (any difference fails):
`ConsensusSpec/**`, `ConsensusSpec.lean`, `ConsensusChallenge.lean`, `comparator.json`, `lean-toolchain`,
`lake-manifest.json`, `ConsensusTests/ReviewAxioms.lean`, `ConsensusTests/ReviewGuard.lean`.
The check infrastructure (`scripts/**`, `.github/**`, `lakefile.toml`; `lakefile.lean` must not exist) is
owner-reviewed through `.github/CODEOWNERS` and PR review, not through the tag; it is described below
because it defines what the checks enforce.

This record compares `2852f717` (the informal "B1 fixes" review) with the approved commit. It was written
with git, Python and file reads only; the evidence script below reruns every textual claim.
[TRUST.md](../TRUST.md) and [README.md](../README.md) give the fuller contract and assumptions.

## Protected paths and declarations

Every file below `ConsensusSpec/` is part of the claim. Namespaces remain `Consensus.*`.
The Spec import closure excludes project Proofs, Instances and Tests.

| File under `ConsensusSpec/` | Meaning |
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
| `Statements.lean` | The four review propositions below. |

| Other protected path | Meaning |
|---|---|
| `ConsensusSpec.lean` | Import-only root collecting the complete Spec; owns no declarations. |
| `ConsensusChallenge.lean` | Non-default comparator challenge: Spec-only imports and four placeholder proofs. |
| `comparator.json` | Challenge/solution modules, four theorem names and three permitted axioms. |
| `ConsensusTests/ReviewAxioms.lean` | Compiled statement/type, binder-kind, completeness and exact axiom pins. |
| `ConsensusTests/ReviewGuard.lean` | Shared implementation of those statement/completeness checks, also used by negative fixtures. |
| `lean-toolchain` | Exact Lean version: `leanprover/lean4:v4.35.0`. |
| `lakefile.toml` | Libraries, default targets, Mathlib requirement, Lean options and checker executable. |
| `lake-manifest.json` | Exact nine dependency revisions, URLs and configuration/manifest paths. |
| `lakefile.lean` | Must not exist at the repository root; the TOML-only Lake boundary rejects it. |
| `scripts/**` | The trust-check driver, tools, reviewed data and positive/negative controls described next. |
| `.github/**` | CI definitions and CODEOWNERS; changes can alter enforcement itself. |

The review propositions are in `ConsensusSpec/Statements.lean`, inside
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

The four lower-case proofs are in `ConsensusProofs/Review.lean`. The source theorems
are in `ConsensusProofs/Shape/Accepted.lean`, `Shape/Realizable.lean` and
`Model/Faithful.lean` respectively (the last file supplies both model theorems).
`ReviewAxioms.lean` compares each definition body to its source theorem's type by
alpha-equality, plus an explicit comparison of all binder kinds (`{}`, `()`, `[]`, `⦃⦄`).
`ReviewGuard.checkComplete` requires a pair for every non-proof, non-matcher constant
owned by Statements, including private constants and other namespaces.
The guarded axiom output pins both sets of four proofs to exactly
`propext`, `Classical.choice` and `Quot.sound`.

The comparator matches the challenge against `ConsensusProofs.Review`, limits axioms,
replays exports in a sandbox and requires identical reachable constants across exports.
Both sides use this tree's Spec. The snapshot and owner review detect Spec drift.
The challenge's `sorry` proofs are deliberate and excluded from default libraries.

`lakefile.toml` defaults to Spec, Proofs, Instances and Tests; challenge and fixture
libraries are non-default. Its six options are `pp.unicode.fun=true`,
`relaxedAutoImplicit=false`, `weak.linter.mathlibStandardSet=true`,
`weak.linter.flexible=false`, `weak.linter.style.header=false` and
`maxSynthPendingDepth=3`. `scripts/pins.toml` independently pins all nine manifest packages.

The `scripts/**` stack is:

| Files/groups | Review purpose |
|---|---|
| `check.sh` | Driver and self-tests: pins, build/freshness, imports, declarations, Spec surface, sequential replay, review pins, grep, vendor hashes, comparator, sandboxed Lake checks and docs. |
| `check-imports.py` | Parsed imports, closure rules, root coverage, library inventory and base-name provenance constraints. |
| `check-pins.py` | Toolchain, dependency manifest, clean checkouts and actual Lake resolution. |
| `SpecSurface.lean` | Snapshot, persisted extensions, theorem hygiene, constant-free parents, statement inventory and reachability; loads no checked extension state. |
| `CheckDecls.lean` | Vendored EthLib declaration/axiom checker; detects unfinished proofs, unsafe/opaque/partial declarations and forbidden implementation hooks. |
| `test_check_decls.sh`, `CheckDeclsTest.lean`, `CheckDeclsForeign.lean`, `CheckDeclsTest/**` | EthLib checker self-tests, including deliberately bad and exempt declarations. |
| `LICENSE.EthLib` | CC0 licence for the vendored checker and tests. |
| `fixtures/**` | Import, surface, review guard, grep, pins, docs, comparator and Lake replay controls. Deliberately invalid fixtures must fail. |
| `boundaries.toml` | Reviewed library inventory, R1–R3 import permissions, base set, fixture exclusions and check configuration. |
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

## Verifying this approval

```sh
git fetch origin --tags
git cat-file -p spec-approved                      # annotated tag, object 4b7c5148
git diff -M 2852f717 spec-approved -- ConsensusSpec ConsensusSpec.lean ConsensusChallenge.lean comparator.json lean-toolchain lake-manifest.json ConsensusTests/ReviewAxioms.lean ConsensusTests/ReviewGuard.lean
git diff 1eb8b6ec spec-approved -- scripts/spec-snapshot.txt
git diff spec-approved origin/main -- ConsensusSpec ConsensusSpec.lean ConsensusChallenge.lean comparator.json lean-toolchain lake-manifest.json ConsensusTests/ReviewAxioms.lean ConsensusTests/ReviewGuard.lean   # empty while main is covered
```

The nightly `full.yml` run on main (`gh run list --workflow full.yml --branch main`) is the correctness
evidence for the approved surface: kernel replay, `lake check` and `lake comparator --paranoid`.

## Later changes to the trusted surface

Once the tag exists, `review-boundary` fails on a PR whose trusted surface differs from the tag, so such a
change is approved **before** merge: the PR says that it needs approval; the owner (or an agent he
explicitly authorizes; never the PR's author on its own) reviews it, including the `spec-snapshot.txt`
diff, moves the tag to the PR head and re-runs the PR's failed job:

```sh
git fetch origin pull/<pr>/head
git diff spec-approved FETCH_HEAD -- ConsensusSpec ConsensusSpec.lean ConsensusChallenge.lean comparator.json lean-toolchain lake-manifest.json ConsensusTests/ReviewAxioms.lean ConsensusTests/ReviewGuard.lean
git tag -f -a spec-approved -m "<who approved, on whose authority, what>" FETCH_HEAD && git push -f origin spec-approved
gh run rerun <run-id> --failed
```

The job compares the trusted surface only, so the approval carries over to the merge or squash commit as
long as main's trusted surface did not change meanwhile (otherwise the PR is updated and re-approved).
