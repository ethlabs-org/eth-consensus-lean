# Build and proof speed: what was measured

Report-only notes for whoever next makes the build faster. The measurements below are historical
results, not a new benchmark of current main. Unless stated otherwise, numbers are from one 4-core, 7 GB
VM (Lean v4.35.0, Mathlib v4.35.0); compare only numbers taken on the same machine in the same
session. The tools are adopted separately from the proof edits and tactic front end.

## How to measure

- **Per module:** `python3 -I scripts/time-modules.py -o out.tsv [MODULE ...]` elaborates each module
  alone with Lake's own `.setup.json` (imports must be built). For a before/after, time the same
  modules in both trees, interleaved, and keep the best of two rounds. Timings taken while other builds
  run, or from `lake build -v` with many jobs, moved by ±40% and misled.
- **Regressions:** generate a baseline in the built base worktree with
  `python3 -I scripts/time-modules.py -o /tmp/base-times.tsv <modules>`, then run
  `python3 -I scripts/time-modules.py --compare /tmp/base-times.tsv <modules>` in the changed tree.
  No baseline table ships in this repository. The JSON header records CPU model, logical CPU count,
  job count and commit. A missing or mismatched CPU/job header is refused unless `--same-machine`
  explicitly overrides it after checking comparability. Matching headers do not establish physical
  machine identity: use the same machine, toolchain, build options and job count, with no competing
  builds. Only exit-0 baseline rows count. CPU growth above both 25% and 1 s exits 2; an empty run,
  failed module or comparison without matching successful rows is INCOMPLETE (exit 1).
- **Per declaration and tactic:** `python3 -I scripts/profile-module.py <file>` (Lean's
  `trace.profiler`, Firefox Profiler JSON). Name the cause from the profile before editing a proof.
- **Whole build:** cold build with `LAKE_ARTIFACT_CACHE=false` and `lakeprof record`, then
  `lakeprof report -p -s` for the critical path and the simulated time by core count. Run base and
  change back to back.
- **Verification:** `scripts/check-changed.sh` remains the gate. Timing and profiling tools do not
  run in the trust checks or change their verdicts; only their deterministic regression fixtures
  run in `check.sh --selftests`. Speed measurements are not statement-equivalence evidence.
- **Statement equivalence (report-only):** in each built tree (base and change), `lake build const-dump
  && lake exe const-dump /tmp/<tree>.tsv ConsensusLean Solution ConsensusLeanTest` (and `lake exe
  const-dump /tmp/<tree>-challenge.tsv Challenge` for the challenge, which declares the review
  statements again), then `python3 -I scripts/const-diff.py /tmp/base.tsv /tmp/new.tsv`. It compares
  every public constant and every internal or private constant that a compared type or definition value
  refers to, the `implemented_by` targets and `partial` bodies of compared constants, and the field
  defaults (also a child's override) of compared structures, except defaults of fields whose projection
  is a theorem (`Prop` fields, also when a child overrides an inherited one: proofs, like their default
  tactics): kind, universe parameters (names, in order), type, value (definition bodies, inductive
  shapes), safety and axioms in both directions. Axioms are collected over every copy of a theorem that
  several modules declare alike (Lean merges them on import and keeps one), for the theorem and its
  users in the dumped modules, and a merged name whose copies' axioms differ is always compared. Axiom
  sets follow Lean's `collectAxioms` walk but take an inductive block with its constructors at once:
  Lean's stored answer (`#print axioms` downstream) can lack the constructors' axioms depending on walk
  order, which a proof edit elsewhere could flip (on main `b7bf2656`, 14 constants get a superset of
  Lean's stored answer; all others are equal). Not compared: theorem proofs, also those inside
  definitions and statements (Lean's `foo._proof_1` and private theorems hash as one tag, by proof
  irrelevance, while their axioms still count; a proof written as a term inside a statement stays
  inline, so changing it changes the statement's hash and is accepted by name after checking);
  auxiliary or private constants no compared constant refers to (proofs may use them); attributes,
  `@[extern]` code, notation, options, binder names and kinds; the dependencies. Hashes are 64-bit
  structural hashes, evidence for honest edits but not collision-resistant. Each accepted difference is
  named (`--allow-added`, `--allow-removed`, `--allow-type`, `--allow-value`, `--allow-axioms`),
  printed, and fails when it matches nothing; a proof edit can drop a public reserved name that proofs
  realize on demand (`foo.congr_simp`), which is then accepted by name. On a 4-core orb a dump of the
  three libraries takes about 11 s and 4.2 GB. Its self-test (`scripts/test_const_diff.py`, in `check.sh
  --selftests`, about 50 s there) compiles each planted mutation with `lean` and dumps it with the compiled
  tool: one per hashed field (literals, bound variables, binder types, levels, projections, `let`),
  reordered universes, a private definition or inductive under an unchanged public one, field defaults,
  `partial` and `implemented_by` bodies, a weakened statement, gained, narrowed or merged-copy axioms
  (also with the clean copy, or the only user, in a module not dumped), safety, an inductive's axioms
  independent of walk order, and proof-only controls (a proof inside a definition, a `Prop` field's
  default proof, also a child's override used by a definition, its default tactic, a private structure
  only proofs use).

## Where the time goes (main at `208c05b7`, measured on 2026-11-02)

- 425 modules then (447 at `ad13a491`), about 1,500 CPU-s when each is elaborated alone; about 180 modules take under 2 s
  and about 25 take over 8 s. On 4 cores the build is bound by total CPU; on 8 or more by its critical
  path (lakeprof: about 220 s, through `Compose.Sleepy`, `Healing.Outcome.Pivot` and the
  `Refinement.Window*` chain).
- By tactic: `linarith`/`nlinarith` are the largest single cost (about 9% of profiled time), then
  `simp`/`simp_all`, `split_ifs`, `omega`, and term elaboration. Kernel checking is about 3%.
- Mathlib's style linters (`weak.linter.mathlibStandardSet`) cost 8–11% CPU but no wall time per
  module (they run in parallel with the proofs), and no single linter dominates.

## What worked

| Change | Measured (module alone, best of 2) |
|---|---|
| `nlinarith` that needs one product → `linarith [mul_le_mul_of_nonneg_left h hΔ.le]`, or plain `linarith` where it suffices (`nlinarith` multiplies every pair of hypotheses) | `Healing.Acquire` 11.6 → 5.2 s, `Compose.Sleepy.Frame` 7.2 → 4.7 s, `Healing.Outcome.Pivot` 12.6 → 10.8 s; 43 modules −8% wall. A second pass at `b7bf2656` over the `Obligations` modules at the end of the critical path (27 of 32 calls: 15 plain `linarith`, 7 `linarith` with the one product, `le_mul_of_one_le_{left,right}` or `positivity` for the rest; the 5 left need cancellation or several products): 9 modules 45.5 → 38.9 s wall (−14.5%), 61.3 → 53.0 s CPU, the 6 on the critical path 32.1 → 28.3 s; `HealBoundRounds` 4.5 → 2.2 s, `FinalResetPremises` 6.5 → 4.6 s |
| `hnew _ (List.mem_singleton_self _)` against an unfolded singleton → `simp only [List.mem_singleton, forall_eq] at hnew` first | `Compose.Sleepy.Provenance` 6.1 → 2.7 s |
| `simpa only [..., mul_comm] using h` → `rw [..., mul_comm]; exact_mod_cast h` | `Refinement.HealedSafety` −0.9 s wall, −3.6 s CPU |
| Hot `simp`/`simp_all` → their `simp?`/`simp_all?` sets | `Refinement.Shape` 4.9 → 3.8 s; elsewhere often flat, so measure each |
| `import ConsensusLean.Lemmas.Tactic.Linarith`: plain `linarith`/`nlinarith` first run without Mathlib's `natToInt` preprocessor (a quarter of all `linarith` time: it casts every ℕ fact of the context), on failure the elaborator falls back to Mathlib's rule (a failing call runs twice, and the cheap attempt's time and heartbeats count against the declaration's `maxHeartbeats` first, so a proof close to its limit could need a scoped raise; the whole library builds with the defaults). 4 of about 1,400 calls fall back | measured at `ad13a491` + the change, all 447 modules: the 150 that imported it then −7.8% wall, −8.2% CPU; the 297 others (controls) −0.5%; whole library −4.0% wall, −4.8% CPU. In this repository the front end landed alone; `scripts/linarith-imports.py` then gave it to every module of the default libraries that calls plain `linarith`/`nlinarith` and may import the Lemmas layer: 213 modules, 208 of them by a direct import (the other five are the fixture module and the test modules Controls, Leaks, Realizable and Support, which reach it through their import of the root `ConsensusLean`, 10 plain calls). The trusted `AsChainShape.lean` calls `linarith` and is left without it. A new module that calls `linarith` gets the import from `python3 -I scripts/linarith-imports.py` (`--check` lists the missing ones); without it the module still builds, with Mathlib's front end |

Together (two commits, 28 Lemmas files, no statement changed), cold build of the default targets
back to back against `208c05b7`: wall 413.7 → 397.2 s (−4.0%), CPU 1,494 → 1,468 s (−1.8%),
critical path 247.9 → 236.9 s (−4.4%), simulated on 8 cores 278.8 → 259.8 s (−6.8%).

All four proof-speed commits together, cold build of the default targets back to back against
`ad13a491`: wall 388.3 → 369.5 s (−4.9%), CPU 1,467 → 1,374 s (−6.3%), critical path
242.3 → 223.8 s (−7.6%), simulated on 8 cores 267.0 → 246.6 s (−7.6%).

The tactic front end in this repository, measured on a 2-vCPU, 3 GB VM (Xeon @ 2.6 GHz),
base `3e503e87` (front end landed, no caller imports) against `59c7e3cd` (the 208 generated
caller imports, `scripts/linarith-imports.py`), same machine, interleaved base/new/base/new,
best of two:

- Module alone (`time-modules.py`, jobs 1): the 12 modules with the most plain calls
  69.7 → 58.8 s wall (−15.6%), 111.7 → 94.3 s CPU (−15.6%), every one faster (−6% to −32%;
  `Obligations.HealthyResetEnvelope` 9.5 → 6.5 s, `Healing.M1.FreshLock` 6.7 → 4.9 s,
  `Healing.Acquire` 6.4 → 4.9 s); three heavy unchanged controls 19.5 → 18.7 s (−4.0%, drift),
  none slower, so about −12% net of that drift.
- Cold build of the default targets (`rm -rf .lake/build`, `LAKE_ARTIFACT_CACHE=false`,
  `lakeprof record lake build`; the 516 project modules, packages prebuilt): wall 801.8 → 759.0 s
  (−5.3%), summed module time 1,502.5 → 1,435.8 s (−4.4%), critical path 289.8 → 265.6 s
  (−8.4%), simulated on 8 cores 311.4 → 290.6 s (−6.7%). Both rounds agree in sign; round to
  round, base varied by 3%.

## The critical path is the proof structure

On 8 or more cores the build waits on one chain of about 65 modules, from `Spec.SA` through
`Compose.Sleepy`, `Healing.Outcome.{Foundation,Pivot,Supplier,Service}` and
`Refinement.{HealthyEffective,…,Exposure*,RowsSupply,Window*}`. Modelled on per-module times
(`/tmp`-only script, the import graph plus `time-modules.py` output): removing any single module's
whole time shortens it by at most about 10 s, and a naive model of cutting import edges promises
−26 s from two cuts (`RowsSupply → ExposureHealed`, `Outcome.Supplier → Outcome.Pivot`). Checked
against the code, neither cut is real: `RowsSupply` can drop `ExposureHealed`, but its importer
`WindowCrossed` needs `ExposureHealed` itself (net −3.3 s), and `Supplier` uses `Pivot`'s main
theorems. The chain is the order the proofs depend on each other, and Lean already elaborates the
large proofs inside a module in parallel (`Pivot`: 33 CPU-s in 12 s wall). Faster modules on the
chain (the `linarith` work above) are what shortens it.

## The edit loop

What a contributor waits for is the rebuild after a commit, not a cold build. Replaying 40 consecutive
`main` commits that touch Lean (`3d2270d1`..`ad13a491`) in a warm worktree, `lake build` after each:

| Commits | Modules rebuilt | Wall each (4 cores) | Share of all rebuild time |
|---|---|---|---|
| 30, a new or leaf file, or a proof-only edit | 1–2 | 4–12 s (median 8.6 s overall) | 18% wall, 11% CPU |
| 6, a lemma added to a mid-level module | 8–19 | 31–62 s | 19% wall, 13% CPU |
| 4 (`556f39be`, `8df1fff0`, `818ddb19`, `5954e919`), a helper added to `AC/Steps/Core`, `AC/Steps/Nodes` (twice) or `Compose/Sleepy/Served` | 136–164 | 174–202 s | 62% wall, 76% CPU |

Proof-only edits rebuild one module even when the static import cone is larger (the module
system keeps the public `.olean` unchanged; AGENTS.md "Visibility"). A new public declaration in a
widely imported module rebuilds its whole cone: every large rebuild above added a helper lemma to
`AC/Steps/Nodes`, `AC/Steps/Core` or `Compose/Sleepy/Served` next to a new leaf file. Hence the
proposed rule "Where a new lemma goes": put single-consumer helpers in the consumer or a small leaf,
not in a widely imported module.

## The pipeline: fresh environments and stale trees

A fresh development environment can start from a snapshot taken after `.agents/setup` up to 24 hours
earlier, and, measured on 2026-11-03, `main` had moved 163 commits in the previous 24 hours (26 in 12
hours). A tree 26 commits behind rebuilt 476 modules, the whole library, on its first `lake build`
(1,774 CPU-s; 536 s wall on a busy 4-core VM), because three of those commits changed low Spec statements (`5de10bf6`, `a90299c1`,
`68a580f0`). Docstrings and comments are not the cause: rewording a docstring of
`Spec.Problem.Basic` (imported by every module), or adding a comment line, left every importer up
to date (`lake build --no-build ConsensusLean`). So a fresh environment typically pays a near-full build
before its first check.

The fix both earlier speedups used is a per-commit build cache (ml-dsa-fv: fresh environment 22.9 →
2.5 min). Lake 4.35 has it built in: `lake cache put <mappings> --scope …` uploads a build's outputs to
an S3-compatible bucket (`LAKE_CACHE_KEY`), and `lake cache get --scope …` restores them, searching
up to 100 earlier revisions. It needs a bucket and a key, and the CI to upload after each
green main build; not set up here. The nightly full tier must keep building with
`LAKE_ARTIFACT_CACHE=false` (as `scripts/check.sh` does for its rebuild checks).

## What did not help (do not retry without a new idea)

- `linarith` → `omega`: fails on most goals, because `omega` does not see through `Time` (an `abbrev`
  of `Int`).
- `linarith?` to get `linarith only [...]`: on this repo it fails on goals that `linarith` proves.
- A `linarith` that keeps only the hypotheses sharing atoms with the goal: no gain, `Δ` and
  `tr.time` connect almost every hypothesis.
- `simp_all` or `simp_all; done` before `aesop` in the `processAtt` fold proofs: the goals that cost
  time are exactly the ones that need `aesop`.
- Ascribing the expected type of `.propose`/`.poll` duty lists: measured flat (one such
  `ShapeDuty.poll` ascription in `Refinement.ForwardingDecode` was kept; it is harmless). The cost is in
  the `apply` that unifies the duty type `(protoOf (compiled (family S)) E).Duty` with `ShapeDuty`, not
  in the literal. The same mismatch is why `erw` is needed in `EngineSteps.tick_node_eq` (32 `erw`
  sites over `runDuties`/`dutyStep`).
- Restating `runDuties_fst_cons`/`_append` at `ShapeDuty (family S (pubOf E)).skel.Kind` (with a type
  ascription on the list) so that plain `rw` could replace `erw` in `tick_node_eq`: `rw` still finds no
  instance of the pattern. Not pursued further; the whole `erw` family is worth about 20–30 CPU-s.
- Splitting or re-plumbing modules on the critical path: see above.
- Unused imports (`lake shake --keep-implied`): the 37 removals that survive a build and the Init-chain
  check do not touch the critical path (modelled 169.9 → 169.9 s; average rebuild cone −0.5%). Shake's
  larger proposal adds about 2,300 direct imports.
- From the clifv and ml-dsa-fv speedups, not tried here because they did not pay there:
  `Elab.async=false` (reproducible `.olean`s but 2.5–2.8× slower), `lean -j2`, splitting a module
  whose cost is one declaration, compiling tactics.
