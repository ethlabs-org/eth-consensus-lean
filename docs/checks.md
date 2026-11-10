# The checks

What `scripts/check.sh` checks, step by step; its modes; what CI runs; how to run the checks locally; and the
check tools with their limits. `TRUST.md` summarises what these checks guarantee; this file has the detail.

## The steps of `scripts/check.sh`

Everything outside the trusted files is checked by Lean; `scripts/check.sh` checks the boundary:

0. **Pins:** exact toolchain, manifest, clean dependency checkouts and Lake's resolved search path match `scripts/pins.toml`.
1. **Build:** compile `ConsensusLean` (the default target), `ConsensusLeanTest` (what `lake test` builds), `Solution`, the challenge, check-decls and axiom-audit with `lake build --wfail --iofail` (any warning or info message fails, also one Lake replays from a built module; `warn.sorry = false` in the lakefile keeps `sorry` silent), and the deliberately bad fixtures without; `--no-build` still checks Lake freshness.
2. **Boundaries:** enforce the layer matrix, the Init chain, root coverage, library inventory and pinned-base names with `scripts/check-boundaries.py` (source-level, no build).
2b. **Linarith front end:** every module of the checked libraries that calls plain `linarith`/`nlinarith` (no `only`, no `!`, no configuration such as `(config := c)`, `(preprocessors := ps)` or `-flag`: the only forms the front end changes) and may import the `Lemmas` layer imports `ConsensusLean.Lemmas.Tactic.Linarith` (directly, or through the root `ConsensusLean`; an import command may span lines), except the modules in the `EXEMPT` table of `scripts/linarith-imports.py`, each with the measured reason the front end shows no gain there; an exemption that no longer applies fails. The scan is lexical (source-level, no build): outside comments and strings, the word `linarith` counts as a call unless one of those forms follows, so a declaration named `linarith` would count while `«linarith»` does not. Without `--check` the script adds the missing imports. It guards build time, not trust: the front end changes only how `linarith` searches, and the kernel checks every certificate either way.
3. **Declarations:** EthLib check-decls runs once per library scope (`ConsensusLean`, `ConsensusLeanTest`, `Solution`), checking every module for extra axioms, unfinished proofs, opaque/unsafe/partial declarations, extern/implemented_by/csimp and opaque reachability; empty scopes fail. A `sorry` is allowed (and listed) only in the `sorry = true` layers of `scripts/boundaries.toml`, `Lemmas` and `Proofs.<M>`; anywhere else it fails.
3b. **Axiom audit:** leanprover-community/axiom-audit over the import closure of `Solution` and of the `proved_milestone_modules` (the proved milestones that are not Challenge statements): every declaration of `ConsensusLean` and `Solution` in those closures uses only `propext`, `Classical.choice` and `Quot.sound`, so a `sorry` (also through an import), `native_decide` or a declared axiom there fails. The same gate covers every declaration of `ConsensusLeanTest`: a test, witness or rejection built on an unfinished lemma proves nothing (step 7 refuses proof `example`s, which never enter the environment, so every test is a named declaration). `Solution` imports generic `Main`, `RegimesRealizable` and `Faithful`, and the Goldilocks obligations endpoint, not every milestone directly. Other finished milestones are audited through `proved_milestone_modules` and pinned by `ConsensusLeanTest/MilestoneAxioms.lean`; they are not separate Challenge roots. A new unfinished milestone must stay outside all audited closures, including tests. A report lists the unfinished declarations of `ConsensusLean` (those that depend on `sorryAx`): the progress metric. "Certified" still means a passed full tier on a named commit (`docs/roadmap.md`), not merely membership in an audited closure.
3c. **Sorry inventory (report only):** see "Step 3c" below.
4. **Spec surface:** check persisted extensions, diff the complete readable/structural snapshot (including pins/options), enforce theorem hygiene and constant-free parents; the `reach` report (which Spec definitions the review statements reach; not a gate) runs in `--full`, in `--changed` when step 4 runs, and in `--fast` with `--reach`. The protected-surface snapshot diffs the same snapshot of every default-library module that `trusted_paths` covers outside the trusted layers (the instance `Spec`, `Statements` and `AsChainShape.lean`) against `scripts/instance-spec-snapshot.txt`; like the Spec snapshot it fails until regenerated with `--update-snapshot` and committed. The extension and theorem policies apply to the trusted layers only.
5. **Kernel replay:** run leanchecker on every leaf module of the checked libraries, one module per process after checking it has no descendants, two processes at a time (`REPLAY_JOBS`); parent modules own no constants.
6. **Review pins:** require the tests root to import the compiled alpha-equality guards and exact axiom pins.
7. **Backstop:** grep for `sorry`/`admit` outside the sorry layers (comments included; their count inside them, comments and strings removed and only as a term or tactic, is reported), proof `example`s (only a bare `example := @Name` or ``` example := ``Name ``` reference is allowed), native proofs, kernel bypasses and `debug.` options, Spec metacommands and unsafe lakefile options.
8. **Vendored:** verify all vendored EthLib copies against `scripts/vendor.sha256`.
9. **Comparator config:** pin challenge/solution modules, every statement name (the four review statements and the closed statements of the `milestone_statements_modules`, today the obligations endpoint and the headline `GoldilocksCorrect`, each of which must have one) and exactly the three standard axioms; validate the Spec-only challenge.
10. **Lake check (needs bubblewrap; skipped and listed as CI-only where `bwrap` is missing):** sandboxed build, export and kernel replay of the default targets, rejecting extra axioms. It rejects `sorryAx` too, so it checks the default targets only while the files of the sorry layers hold no `sorry`/`admit` term or tactic outside comments and strings (an `admit`-named field, binder or projection is not one; otherwise a NOTE and, in CI, a warning); then the checks of the part proved in Solution, the `Solution` closure, are 3b, 5 and 11. Its fixtures always run.
11. **Lake comparator (needs bubblewrap, likewise):** statement/axiom matching, sandboxed replay and agreement of reachable constants between challenge and solution exports.
12. **Docs:** require the marked file list of [`docs/definition.md`](definition.md#reading-order-the-trusted-files) to equal every file of the trusted layers exactly, and every `Consensus.…` name cited in `docs/roadmap.md` and `docs/goldilocks-mapping.md` to be listed in `ConsensusLeanTest/Index.lean`, whose build checks that it exists.
13. **Metrics (report):** depth, downstream cones, `@[expose]` and import counts (`scripts/metrics-baseline.py`, about 2 s, no build).
14. **Rebuild canary (report; `--full`, or `--canary`, which CI passes when the build configuration changed):** a fixed proof-only edit of one module (`canary_*` in `scripts/boundaries.toml`) must leave its `.olean.hash` unchanged and every default target up to date; a regression is reported (a CI warning). Its control, a statement edit, must make the default targets stale, else the step fails.

Checks with fixtures exercise the same code paths on positive and negative controls.
Spec drift is guarded by the snapshot diffs (the Spec and the protected surface), committed with each change;
dependency drift by pins; proof validity by replay, check-decls and the CI comparator.

## Modes

`scripts/check.sh` has three modes; every step it does not run prints `SKIP  <step> (<reason>)`:

| Mode | Runs | Where |
|---|---|---|
| `--fast` (default) | steps 0–4, 6–9, 12, 13: pins, build (`--wfail`), imports, linarith front end, check-decls, axiom audit, Spec surface + snapshot diff, review pins, grep, vendored hashes, comparator config, docs, metrics; self-tests only with `--selftests`, step 4's `reach` report only with `--reach`, the rebuild canary (14) only with `--canary` | `check` on every pull request (its merge commit) and push to main, with `--selftests` when `scripts/` or the build configuration changed, `--reach` when the trusted surface or `scripts/` changed, `--canary` when the build configuration changed; review-boundary and its self-test also run |
| `--full` | everything: the fast steps, every self-test, leanchecker replay (5), `lake check` (10), `lake comparator --paranoid` (11), the rebuild canary (14) | `full` nightly at 03:17 UTC, on demand and on `milestone*`/`release*` tags; clean project build, split into `lake check` and the rest, with no skipped steps |
| `--changed [<base>]` | the fast steps restricted to what changed since `<base>` (default: merge-base with `origin/main`, uncommitted and untracked files included): build of the changed modules' downstream cone, check-decls on the affected libraries, the axiom audit's gates only if the closure of `Solution` (or a test module) changed and its report only if `ConsensusLean` did, Spec surface and comparator config only if a Spec module (or the challenge, `comparator.json`, the solution's imports) changed (otherwise only noconst of step 4), grep on the changed files; pins, imports, the linarith front end, review pins, vendored hashes, docs and metrics in full (cheap). A change of `scripts/` or of the build configuration falls back to `--fast` (with self-tests for `scripts/`); with `--selftests` it runs `--fast --selftests` | locally, `scripts/check-changed.sh [<base>]` |

Only an unsplit `--full` ends with `check.sh: ALL CHECKS PASSED`; a `--split` part ends with `check.sh: PART PASSED (split <part>; ...)`, the other modes with `check.sh: PASSED (<mode> mode; ...)`.

## CI

CI is GitHub Actions. A green CI result means the GitHub check of the commit: `check`
(`.github/workflows/ci.yml`: the fast tier and the review boundary) on every pull request and every push to
`main`, and `full` (`.github/workflows/full.yml`: the full tier, in two parallel parts) nightly at 03:17 UTC, on
`milestone*`/`release*` tags and on demand. `check` runs fast mode (no replay, `lake check` or comparator;
check-decls, axiom audit, snapshot diff and review pins included) on every pull request (its merge commit) and every
push to `main`, with docs-only changes in `--changed` mode, plus review-boundary and its self-test. A head's scripts
are code a collaborator wrote: it runs on a fresh GitHub-hosted runner, on the `pull_request` event (never
`pull_request_target`), with a read-only token and no secrets, so it can change nothing but its own check result.
`check` also checks every new commit's author, committer and `Co-authored-by:` addresses against the public
allowlist `scripts/commit-emails.toml` (`scripts/check-commit-emails.py`; `push-main.sh` runs it before the push; a
privacy check, not a trust check). Each run's summary shows the check's result and SKIP lines; its log is an
artifact, and on main the step 3c sorry inventory too.

`full` runs full mode from a clean project build: a proof change merged after a green fast run is replayed by the
kernel at the latest the next night. `lake check` and `lake comparator --paranoid` run inside bubblewrap, which the
workflow installs (and smoke-tests: the job fails if user namespaces are blocked). The kernels are the toolchain's
own, pinned by `lean-toolchain` (leanchecker, leanchecker-paranoid, lean4lean, nanoda, con-leche, con-ron). Full CI
rejects any skipped step and a dirty tree; part main may defer only step 10 (`lake check`), which part lake-check
must pass. Without bubblewrap a standalone check skips these steps and lists them as CI-only, which is not a passing
full CI result. "Certified" is reserved for a full-tier certification: a passing `full` run of a named main commit
(the status legend of `docs/roadmap.md`).

Caching: `check` restores the Lake packages (with Mathlib's oleans from `lake exe cache get`) and the project build
of this PR's previous push or of main's latest, and Lake rebuilds changed modules and dependents. The full tier
builds the project from scratch; only the packages are cached. Both build the heaviest test modules one at a time
first, to fit the 16 GB runner.

## Running the checks locally

1. Iterate on one file with `lake env lean <file>` (after building its imports), or on one declaration with
   `turbo-lean check <file> --decl <name>` (a single declaration only; `lake build` stays the gate).
   `lake build` builds `ConsensusLean` by default; `lake test` builds `ConsensusLeanTest`.
2. Before committing, check what changed: `RUN_DIR="$(mktemp -d)" scripts/check-changed.sh [<base>]`.
3. Land with `scripts/push-main.sh` (it rebases on `origin/main`, reruns step 2 against it and pushes only if it
   passes; a trusted-surface change needs a `Trusted-surface:` line in each commit). The `check` workflow then runs
   on the new main head; verify its result (`gh run list --workflow ci.yml --commit <sha>`). Before a milestone or a
   toolchain/Mathlib bump, run the full tier on the exact commit: `gh workflow run full.yml --ref <branch or tag>`,
   and verify it passed.

`check.sh` refuses to run without `RUN_DIR` or `CI`: `RUN_DIR="$(mktemp -d)" scripts/check.sh --fast`, or
`CI=1 scripts/check.sh --full`.

`lake test` checks every cited name (`ConsensusLeanTest/Index.lean`) and compiles the review
type/axiom pins (`ConsensusLeanTest/ReviewAxioms.lean`). Step 12 checks, without a build, that every name
`docs/roadmap.md` and `docs/goldilocks-mapping.md` cite is in that index (as FLT's `checkdecls`
checks its blueprint) (`scripts/check-docs.py`). `--no-build` skips compilation but still
uses Lake's freshness gate, so stale artifacts fail. Snapshot/extension updates fail deliberately so
their diff is reviewed; CI refuses update flags and `--no-build`, and checks that the tree stays clean.

`lake check` and `lake comparator` need bubblewrap (`bwrap`). Where it is missing, `--full` skips
them and lists them as **CI-only**; the `full` workflow installs bubblewrap and always runs them, with their
fixtures and a guard that fails on any skipped or deferred step. The comparator runs with `--paranoid`: the review
statements' closure is replayed by Lean's kernel and by every external kernel bundled with Lean
(leanchecker-paranoid, lean4lean, nanoda, con-leche, con-ron), about 3 minutes in CI. leanchecker replays every leaf
module of the checked libraries, one module per process (`REPLAY_JOBS` at a time; 2 in `full`); never invoke it on a
root or prefix with descendants.

## The statement pins and the comparator

`Solution.lean` proves each review statement by its source theorem, and the one instance statement
of `Challenge.lean`, the Goldilocks obligations endpoint `MeetsObligations` (a closed
`Prop` definition of `milestone_statements_modules` in `scripts/boundaries.toml`), by its milestone
proof. The headline `GoldilocksCorrect`, the other closed `Prop` of that module, is proved by composing the two:
`ShapeObligations.correct` applied to `meets_obligations`. Challenge certifies these six statements and nothing
else: the trusted surface is the generic definition of a correct protocol plus the one instance module. The other Goldilocks milestones are ordinary proved lemmas:
their statements are in the untrusted `Instances/Goldilocks/Milestones/` layers,
`ConsensusLeanTest/MilestoneAxioms.lean` states and pins each one, and check.sh step 3b gates their closure
(`proved_milestone_modules`). Which claims node each statement states, and where its mapping rows are:
`docs/goldilocks-mapping.md` §"Review path".
`ConsensusLeanTest/ReviewAxioms.lean`, using `ConsensusLeanTest/ReviewGuard.lean`, compiles
alpha-equality guards (including binder kinds) and `#guard_msgs` pins of the exact axiom lists
for both the review and source theorems. `ReviewGuard.checkComplete` requires every non-proof,
non-matcher constant declared in the statements module to have a review pair, including private
constants and declarations in other namespaces. The module must contain statements only.

In CI, `lake comparator --config comparator.json` compares `Challenge.lean`
(the Spec statements with placeholder proofs) with `Solution.lean`:
matching statements, permitted axioms, sandboxed kernel replay, and identical reachable constants
in both exports to resist build-time tampering. This checks the proofs against Spec built alone;
Spec drift is checked by the snapshot diff, committed with each change.

## What each check guarantees

- **Spec drift:** snapshot every Spec-owned constant (readable text plus structural hashes), diff
  against `scripts/spec-snapshot.txt`; the regenerated snapshot diff is committed with every change, and the
  change is recorded by a `Trusted-surface:` commit line.
  Proof values are omitted by proof irrelevance; non-proof auxiliary constants are included. So are the
  auxiliary proofs of a definition (`d._proof_N`: their statements are part of what the body means); an auxiliary
  proof generated for a theorem's proof (unranged, `Prop`-typed, owned by the theorem and not named in its
  statement, such as `omega`'s `_proof_1_1`) is omitted with that proof; one its statement names is kept. Known
  limit: a proof-only edit that adds a non-`Prop` auxiliary inside a theorem's proof (a `match_N` definition) still
  changes the snapshot.
- **Protected-surface drift:** the same generator and verdict over the **protected surface**, against
  `scripts/instance-spec-snapshot.txt`. Its modules are the inventory's 6th column (`scripts/check-boundaries.py`,
  from `scripts/boundaries.toml` alone): every module of the default library whose file `[checks] trusted_paths`
  covers and whose layer is not trusted, that is, every module of the `protected` layers
  (Goldilocks `Spec`, `Statements/Obligations` and `AsChainShape.lean`; `python3 -I scripts/check-boundaries.py
  --inventory-out <file>` lists them), which may import only trusted and protected layers (check-boundaries.py), so
  the closure of the endpoint statement stays inside the surface.
  The Goldilocks milestone statements other than the endpoint, and the instance Spec that only they reach, are in
  the untrusted `Instances/Goldilocks/Milestones/` layers, outside it.
  Common/Frame claim aliases and frame-sequence vocabulary live in non-exposed Lemmas leaves,
  outside that surface; their names and propositions are preserved and audited through the test root.
  The simulation interface and canonical trace construction (`Lemmas/Simulation/{Interface,TraceDefs}`)
  likewise live in non-exposed Lemmas leaves; they remain dependencies of Solution's proof and its axiom audit, not
  of the certified endpoint statement. The shape in AsChainShape and the obligations statement stay protected.
  `check-boundaries.py` fails if a `protected` layer's module is not in it or a trusted
  layer's module is. Like the Spec snapshot, it fails step 4 on any drift (a changed definition body or type, an
  added or removed constant, the pins/options header) until `--update-snapshot` regenerates it and the diff is
  committed for review; so it gates a landing at the regeneration level, and the regenerated diff is the record.
  A proof-only change does not change it, with the limit stated for the Spec snapshot above. Not covered: the
  trusted-surface files outside the default library (`ConsensusLeanTest/ReviewAxioms.lean`, `ReviewGuard.lean`:
  step 6), `Challenge.lean` (the comparator challenge, a fixture library: step 9), the persisted-extension and
  theorem policies of step 4 (they apply to the trusted layers only), and non-Lean trusted files (pins, comparator
  config). In `--changed` mode it runs when a module of the protected surface is in the downstream cone of the
  change (an upstream change can change how it elaborates), or a `.lean` file under `trusted_paths` was deleted or
  lies outside the checked libraries; such a file is outside the import graph, so it only triggers the step: no
  module of it is snapshotted (a deleted module's lines leave the snapshot, which fails the diff).
- **Dependency drift:** exact pins; the upgrade to v4.35.0 additionally used the dependency audit (below).
- **Unfinished proofs** (the FLT/Carleson model): `sorry` may stay only in the
  `sorry = true` layers of `scripts/boundaries.toml` (`Lemmas`, `Proofs.<M>`; check-boundaries.py refuses
  the flag on a trusted layer, outside Lemmas/Proofs or outside the default library); no declaration of Spec,
  Statements, Main, the instances, the tests or the solution contains one (check-decls `--sorry-ok`, grep step 7),
  and it is never an axiom. **Proved in Solution = the import closure of
  `Solution`**: axiom-audit (step 3b, every checked head) fails any declaration of `ConsensusLean` or `Solution` in
  that closure that depends on an axiom other than the three standard ones (`sorryAx`, `native_decide`'s axioms, a
  declared axiom, also through imports), and likewise in the closure of each `proved_milestone_modules` entry
  (the proved milestones that are not Challenge statements; `ConsensusLeanTest/MilestoneAxioms.lean` pins their
  theorems), and so it does for every test declaration (a test built on an unfinished
  lemma proves nothing; grep step 7 refuses proof `example`s, which never enter the environment). `Solution` imports
  `Main`, every generic milestone and the obligations endpoint's `Main`, and `proved_milestone_modules` lists the
  other finished instance milestones' `Main`s, so all of them must be finished; a new milestone may stay unfinished
  while neither imports it (step 3b's report lists what is unfinished). The instances reach the generic library only
  through `Main`, inside the closure, so everything they use is finished today. Step 9 and the comparator check the
  closed statements of the `milestone_statements_modules` (instance statements modules under `trusted_paths`; today
  the obligations endpoint and the headline) next to the review statements. The review pins and the comparator check the axioms
  of the review and endpoint theorems too; `MilestoneAxioms` those of the other milestones (untrusted). axiom-audit's
  shared memo can under-count inside an inductive/constructor cycle when the declaration that uses the axiom directly
  is not audited (the tests gate, whose roots exclude the library): check-decls still fails a direct `sorry` outside
  the sorry layers. `lake build --wfail` runs with `warn.sorry = false`, so every other warning fails the build.
  "Certified" is reserved for a full-tier certification: `check.sh --full` passed on a named main commit,
  that is, a passing `full` workflow run of the commit (the status legend of `docs/roadmap.md`).
- **Proofs:** leanchecker, one process per leaf module of the checked libraries (parents own no
  constants); `lake check` (of the default targets while the sorry layers' files hold no `sorry`/`admit` term or
  tactic outside comments and strings, an `admit`-named field or binder not being one: it rejects `sorryAx`;
  otherwise only the comparator replays what the solution uses of the dependencies); check-decls; axiom-audit; and
  the comparator: statement matching, axiom limits, identical reachable constants across exports (tamper
  resistance) and sandboxed replay, by Lean's kernel and, with `--paranoid`, by every external kernel bundled with
  Lean. The comparator is **not a Spec-drift check**: both sides read the same source tree.

## Step 3c: the sorry inventory (report only)

Step 3c is **report only**, not a trust gate. `scripts/sorry-inventory.py` reads `scripts/sorry-inventory.toml`
(or the file given with `--config`): `modules` and `roots`, and the table `mapped` from each sorry owner to its
paper argument or OPEN (empty while the closure has no owner). Names must be fully qualified. A missing or
malformed config, empty/missing roots, stale artifacts, nonexistent mapped names and unmapped direct
`sorryAx` owners report incomplete; no generic `ShapeObligations` result substitutes for an absent
instance assembly. `SpecSurface dependencies` loads private declarations without extension
initializers and exports type/body edges. Cycle-safe reverse reachability lists every
sorry-dependent ancestor **within the configured declaration closure**, not the whole import
closure. One entry represents a direct owning declaration, not each source `sorry` occurrence.
Files are logical paths relative to the owning module's package source root. JSON schema 2
is saved at the printed `check.*/sorry-inventory.json` path under the run directory.
`mapped` means every owner has a `mapped` entry with argument text or OPEN, not that the paper argument is
valid or the proof is finished. Its regression fixtures are gates for the tool's behavior;
inventory findings and runtime errors do not change existing check verdicts.

## The check tools and the vendored copies

EthLib check-decls is CC0-1.0 and SHA-256-pinned by `scripts/vendor.sha256`. Every vendored file is
byte-identical to [ethereum/EthLib](https://github.com/ethereum/EthLib) at
`6390c73ef040311e807b9047d99dca6b1be1c42f`, except three local patches to `scripts/CheckDecls.lean`:

- **Performance:** it computes the in-scope module indices once instead of rebuilding
  `EnvironmentHeader.moduleNames` (an array of every imported module) for each of ~450k constants. Same findings,
  counts and exit codes on every library and on `test_check_decls.sh`; step 3 about 25× faster.
- **The reaches-opaque frontier:** a definition that check-decls does not check (one in a module with a `Proofs` or
  `Exports` component, a `Repr`/`ToString` formatting definition, an `initialize` function) no longer counts as
  having reported the opaque constants it reaches; they are reported at the checked definition that unfolds it.
  Without it, the single `ConsensusLean` scope let a definition in `Main` or an instance reach an opaque unreported
  through such a definition (self-test fixture `CheckFixtures.HiddenOpaque`).
- **`--sorry-ok PREFIX`** (repeatable): a `sorry` finding at a declaration of a module under such a prefix is listed
  (`allowed sorry ...`) instead of failing; every other finding kind is unchanged. check.sh passes the prefixes of
  the `sorry = true` layers; without the option the tool behaves as before.

Hashes: upstream copy `0032a6629a73ac37f49ca52b9bd665f2c6755b6014d629f8775c6f850f273bb2`; with the performance
patch `69b9fe48f5d913031348aa33895155e96236819ba7d86c9e36675a793c1241d6`; with the performance and frontier patches
`03ed87d6cecae9a145ed47e56788978ffbe67a70055c3326f933a6d397edb10a`; with all three
`b941e9baa619e80d954e2cdaf32ba7d5f48a8b29e4c888d3b97a91cee42aa367`; the vendored file, whose comments name the
patches by what they do: `43c1701aa493f339eb590376709b47f65a948bdd6edb430efd86fa87173f1784`.
`scripts/test_check_decls.sh`:
`591a1d993df5dc1a01a9cf645f71cbeffdb7da9fdff9e3ca8f5179f60ead9f25`. `vendor.sha256` also pins fixtures/licence.
check-decls runs imported modules' initializers: a defence against mistakes, not an adversarial checker.

[leanprover-community/axiom-audit](https://github.com/leanprover-community/axiom-audit) v0.1.2
(`46024e005996495c65ef609368e11ab39c4222e3`, Apache-2.0; the tool lean-action's `axiom-audit` input names) is
vendored verbatim as `scripts/AxiomAudit.lean` and `scripts/AxiomAuditMain.lean` (its `Main.lean`), SHA-256-pinned
likewise. Like check-decls it loads `.olean` files with `trustLevel := 1024`: it reads which axioms each declaration
uses, not whether the proofs check, so kernel replay (steps 5, 10, 11) and the grep for `debug.` options (step 7)
cover what it trusts.

`scripts/check-boundaries.py` checks the layer matrix of `scripts/boundaries.toml` on parsed imports
(`lean --deps-json`; the inventory part started as a CC0 port of verified-consensus `check-review-boundary.rb`).
`scripts/check-pins.py` checks provenance. Our `scripts/SpecSurface.lean` loads no extension state and runs no
checked code. Its extension check is a persisted-extension policy, not a source audit: local/non-persisted commands
are visible only through their effect in the snapshot. A grep backstop adds hygiene.

## Dependency pins and the v4.35 upgrade audit

The snapshot header includes lakefile `leanOptions` (printing, implicit binders, linters, synthesis depth),
toolchain and dependency revs. Tactics/elaborators run during compilation; replay checks the terms.

The v4.34.1 → v4.35.0 upgrade was audited: 2,535 project constants and their dependency closure were compared.
All 43 changed project and 24 changed dependency constants have kernel-checked equivalence probes,
including the `Decidable` representation change, generated eliminators and `protects`.
A cut-graph traversal covered all 109 one-sided dependencies through proved changed constants; no unresolved
differences remained.

Mathlib `.olean` files fetched by `lake exe cache get` are not rebuilt locally. leanchecker replays the project's
modules only; `lake check` exports the default targets with the constants they use and replays that export, which
re-checks what the project uses of them. A dependency's own lakefile in its pinned, clean checkout is trusted
as upstream content.
