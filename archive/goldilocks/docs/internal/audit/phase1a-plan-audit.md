# Audit job: Phase 1a plan (framework gate and v1 catalog)

You are an independent auditor. Audit the implementation plan
`lean/available-chain/docs/plans/2026-09-28-phase1a-gate-catalog.md`
(commit `54f6e0d`). It changes the protocol framework's core types
(a "carrier" for claims, late triggers, shared profile constants,
`depsPresent` in the hooks), compiles a witness of a known floor gap,
hardens the catalog lock and the registry, regenerates the lock once, and
adds the standard and strong catalog tiers with two equivalence theorems.
The user has not reviewed it. Your job is to find what is wrong, unsound,
infeasible, inconsistent with the approved design, or not future-proof,
before the plan runs. Do not rubber-stamp. Do not edit any file. This is
a read-only task.

## Sources (read what you need; cite file:line)

All paths are relative to `/Users/francesco/ethereum/lean/available-chain`.

- The plan (above).
- The design: `docs/FRAMEWORK-DESIGN.md` v7. The user APPROVED §0–§6 and
  §9; a change to those sections is a major decision.
- `docs/PHASE0-REPORT.md` (§5.1 deviations (d), (g), (h), (i); §6 open
  items, which this plan claims to close in part).
- The current framework: `AvailableChainFramework/**` (Claim, Cert,
  Profile, Instance, Hooks, Pareto, Catalog/Core, Kit/Core,
  Engine/V2Sketch).
- The current registry: `AvailableChainRegistry/**` (Sanity, Counter,
  CounterRun, CounterIncluded, GridCOHooks, Tests).
- Scripts: `scripts/CatalogLock.lean`, `scripts/Registry.lean`;
  `docs/catalog.lock`, `docs/REGISTRY.md`.
- The v1 engine and contract: `AvailableChainModel/**`,
  `AvailableChainStatements/**` (the bundles `AvailableChain` in
  `Generic/Claims.lean` and `StrongClaims` in `Strong/Claims.lean`; the
  regimes in `Generic/Regimes.lean`, `Strong/Regimes.lean`; constants in
  `Generic/Constants.lean`).
- The Sanity witness run that Task 5 copies:
  `AvailableChainWitnesses/Sanity.lean`.

Toolchain: Lean 4 v4.30.0-rc2, Mathlib v4.30.0-rc2. You may elaborate a
small scratch file with `lake env lean <file>` in that directory (the
Mac allows 3 Lean processes: run `pgrep -fl lean` first). Do not run a
full `lake build`, and do not write inside the repository; put scratch
files under `/private/tmp`.

## What to check

1. **Lean feasibility of the core types.** Do `Carrier` (`Inst : Type 1`,
   `Ctx : Inst → Validators → Type`), `ClaimSpec (K : Carrier)`,
   `Cert`, `Profile K` with `Profile.Entry`, the structure
   `ProfileCert`, `CarrierMap` with an `Equiv` of contexts, and
   `ClaimSpec.pull` elaborate as written, with the universes the plan
   states (`ClaimSpec K : Type 1`, `ProfileCert : Type 1`)? Does
   `@[reducible] def Carrier.v1` make `x.E`, `x.rho` elaborate on
   `x : Carrier.v1.Ctx I W`? Does `CarrierMap.strongV1` typecheck with
   `Equiv.refl`? Test the core declarations in a scratch file if you can.
2. **Soundness of the claims.** Is any new claim vacuous, or stronger or
   weaker than the bundle field it restates? Check each `le` direction
   against design §4's per-parameter table and each `transport` guide
   against the regime definitions. Check the late-trigger shape
   (`trigger … H`) against design §5 and the I2 gap. Check the
   triggers of the persistence claims ("a non-genesis honest read at T,
   H ≤ T") for inhabitability by real protocols.
3. **The equivalence theorems (Task 9).** Are `ac43_iff` and
   `strong1_iff` true as stated? Do the regimes of the new claims agree
   with the bundle's regimes by `Iff.rfl` when the constants record is
   `zeroConstants` with only the read fields set? Is the use of
   `Δ_pos` right, and is anything else needed (for example a validator
   type, or the `monotone` field)? Is the strong claims' `valid := True`
   for the recovery constants correct given that `StrongClaims` has no
   `Constants.Valid`?
4. **The I1 witness (Task 5).** Does `clockChain` really pass every core
   claim at `D = 0`, including safety across different nodes and times
   and inclusion at the proposal time, under the v1 engine's semantics
   (`Run.readAt`, `emittedAt`, `ScheduleWellFormed.tick_total`,
   `PartialSynchrony` with the exclusion exemption, `RootInjective`)?
   If it fails, is there a simple protocol that shows I1?
5. **Design conformance.** Does the plan change an approved section
   (§0–§6, §9) of the design, or only select a representation that the
   design leaves open (§3: "Phase 0 selects an extensible representation
   for FacetBundle, …")? Name every point where the plan departs from
   §3's `Instance` sketch or §4's `ClaimSpec` sketch, and say whether it
   is a representation choice or a design change. Is dropping
   `ProtocolParams` from `Instance` acceptable?
6. **Lock and registry.** Does the hardened lock (by-name compare,
   generated-name skip, axiom check) close PHASE0-REPORT §6's Lock items
   without opening a hole (for example: can a changed claim hide behind
   a skipped generated name)? Is the one regeneration described so that
   a reader can audit what changed? Does the registry change (row kinds
   `profile-cert`, `Candidate`, pulled claims, `KNOWN-GAP`, `--check`)
   work with the type-scanning design?
7. **Scope and ordering.** Is the split into plans 1a, 1b and 2 sound?
   Does 1a leave the repository in a consistent state after each task
   (build green; the lock check "exit 1 until Task 6" rule)? Is anything
   that 1b or 2 needs missing from 1a's interfaces?

## Output

Write a table (Unicode box drawing in a fenced `text` block) with one row
per finding: id (P1a-NN), severity (BLOCKING / MAJOR / MINOR), task,
finding, evidence (file:line), proposed fix. Then give a counterexample or
a scratch-file result for each BLOCKING and MAJOR finding. Then the
answers to questions 1–7, one short paragraph each. End with a verdict
line: ADOPT, ADOPT WITH FIXES, or REVISE, and the final line
`AUDIT COMPLETE: <b> blocking, <m> major, <n> minor`. Write in ASD-STE100
Simplified Technical English.
