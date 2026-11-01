# Phase 1a: Framework Gate and v1 Catalog Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the framework able to carry the full v1 catalog, and fill it. First, one lock-breaking gate: claims over a claim domain (facets and engines), late triggers (I2), shared profile constants (g), `depsPresent` in the hooks (h), and a compiled witness of the no-input gap (I1). Then the standard and strong catalog tiers, the profiles `ac-4.3` and `strong-1`, and their proposition equivalences with today's bundles.

**Architecture:** All changes are in `AvailableChainFramework` (L1–L3) and `AvailableChainRegistry` (L4), plus `scripts/CatalogLock.lean` and `scripts/Registry.lean`. A `ClaimDomain` names the kind of instance that a claim speaks about and the type of its run contexts. `ClaimSpec K`, `Cert`, `Refutation` and `Profile K` become generic over the claim domain. The v1 claim domain is today's `Instance` with an environment and a v1 run. A facet (for example the strong output) is a structure that extends `Instance`, with its own claim domain and a claim domain map to v1, so base claims and certificates pull back to it. No protocol library (`AvailableChainGridCO`, `…SA`, `…SAPC`, `…LStar`, `…Witnesses`) changes in this plan.

**Tech Stack:** Lean 4 v4.30.0-rc2 and Mathlib v4.30.0-rc2, Lake, the module system (`module`, `public import`, `@[expose] public section`).

**Spec:** `docs/FRAMEWORK-DESIGN.md` v7: §2 E4 (hooks), §3 (instances and facets), §4 (claim catalog, tiers, profiles, the core floor), §5 (certificates, inhabitation, refutations, registry, freeze), §8 (migration, row 1), §12 (known gaps I1, I2). `docs/PHASE0-REPORT.md` §5.1 (deviations (d), (g), (h), (i)) and §6 (open items). Today's bundles: `AvailableChainStatements/Generic/Claims.lean` (`AvailableChain`) and `AvailableChainStatements/Strong/Claims.lean` (`StrongClaims`).

## Scope and the Phase 1–2 split

Design §8 has Phase 1 (full catalog on v1, eligibility per migrated instance, `MATRIX.md`) and Phase 2 (engine v2 and the lift). They are three plans, in this order. Each later plan depends on the shapes that this plan fixes, so it is written after this plan lands.

```text
┌──────┬───────────────────────────────────┬────────────────────────────────────────┐
│ Plan │ Scope                             │ Needs from earlier plans               │
├──────┼───────────────────────────────────┼────────────────────────────────────────┤
│ 1a   │ THIS PLAN. Gate (claim domain, I2, g,  │ Phase 0 (done)                         │
│      │ h, I1 witness, lock and registry  │                                        │
│      │ hardening); standard and strong   │                                        │
│      │ tiers; ac-4.3 and strong-1 with   │                                        │
│      │ their equivalences                │                                        │
│ 1b   │ Instance migration: E4 excludes   │ 1a: ClaimDomain.v1, ClaimSpec K, Profile K,│
│      │ for Grid CO, SA, SA-PC (and the   │ HooksSound with deps_stable, ac-4.3,   │
│      │ SA-PC receipt_acceptedRelay       │ strong-1, the equivalence theorems     │
│      │ re-check, which relies on         │                                        │
│      │ excludes = false today);          │                                        │
│      │ HooksSound, EmitWellFormed,       │                                        │
│      │ HandlerCoverage, Deliverable,     │                                        │
│      │ RelayFeasible, WindowMargin;      │                                        │
│      │ Kit.Engine run extension from     │                                        │
│      │ every valid prefix; inhabitation; │                                        │
│      │ Instance values and certificates  │                                        │
│      │ for Grid CO, SA, SA-PC, L*;       │                                        │
│      │ MATRIX.md; the Kit library split; │                                        │
│      │ eligibility as `Eligible I`, a    │                                        │
│      │ structure indexed by the instance │                                        │
│      │ (NOT an Instance field); search   │                                        │
│      │ admission = Candidate × Eligible  │                                        │
│ 2    │ Engine v2 (E1–E6), the lift       │ 1a: claim domain (a v2 claim domain is a new     │
│      │ simulation (a ONE-WAY claim domain     │ ClaimDomain value); 1b: Kit.Engine,        │
│      │ relation, not a DomainMap), a    │ Eligible                               │
│      │ toy Linked, self-visible, restart │                                        │
│      │ protocol; the I1 fix: a run-      │                                        │
│      │ chosen proposer input AND a floor │                                        │
│      │ claim that binds the proposal to  │                                        │
│      │ that input, with a refutation of  │                                        │
│      │ this plan's clockChain against it │                                        │
└──────┴───────────────────────────────────┴────────────────────────────────────────┘
```

The FG module is not connected to the search in any of the three plans (user direction 2026-09-28: fix the floor first).

## Rulings in this plan

The user approved this plan on 2026-09-28 ("Go"). Before execution, three independent reviews ran (Astra: `docs/audit/phase1a-plan-audit-report.md`, REVISE 0/5/3; opus: `docs/audit/phase1a-plan-opus-review.md`, ADOPT WITH FIXES 0/2/14; async session: `docs/audit/phase1a-plan-async-review.md`). This version applies their findings; the section "Audit disposition" at the end lists each one.


- **Claim domains replace type-class facets** (the Phase 0 report calls this the "carrier generalization"; the Lean name is `ClaimDomain`, because the FG module already uses "carrier" for a row carrier, async m4). Phase 0 deviation (d) made a facet a type class over `Instance`. A claim `∀ I [HasStrong I], …` is vacuous for an instance without the class, and two class instances can attach to one `I` (PHASE0-REPORT §6, Facet row). In this plan a facet is a structure that extends `Instance` (`StrongInstance`), so the facet value is a field and is bound once. A claim that needs the facet is a `ClaimSpec ClaimDomain.strong`: only a `StrongInstance` can hold a certificate of it. A new facet is an addition: a new structure, its claim domain and a `DomainMap` to v1. Existing claims and certificates pull back through the map (G2). Deviation (d) is superseded.
- **The same claim domain generalizes the engine (I5).** A claim quantifies over `K.Ctx I W` (for v1: an environment and a v1 run). Engine v2 (plan 2) adds a new claim domain value. It does not change `ClaimSpec`. A `DomainMap` (an equivalence of contexts) is for facets only; the v1 → v2 lift is a simulation and needs a one-way relation with its own transport lemmas (plan 2).
- **`Instance` is frozen after the gate.** A new `Instance` field changes the hash of `Instance` and of almost every locked declaration, so it is NOT an addition (design §3: "adding a field to a frozen Lean structure changes its declaration"). Later per-instance data enters as a separate structure indexed by the instance, in its own module: eligibility as `Eligible (I : Instance) : Prop` (plan 1b: `Deliverable`, `RelayFeasible`, `EmitWellFormed`, `HandlerCoverage`, `WindowMargin`, isolation), facet data as a structure that extends `Instance` with its claim domain. This departs from the §3 sketch, where `deliv` and `iso` are `Instance` fields; it is the representation that §3 leaves open ("Phase 0 selects an extensible representation").
- **`ProtocolParams` stays inside the protocol.** A protocol value is built from its parameters (`sapc p`), so `Instance` gets no `pparams` field. A later explicit parameter interface is a separate indexed structure, as above. Profile constants (`Shared`) are the shared constants of design §3–§4 (deviation (g)).
- **`Instance` gets `Δ_pos : 0 < Δ`.** Without it an instance with `Δ ≤ 0` has no admissible context, and every `holds` is vacuous. `Cert.inhabited` already rejects such an instance, but the equivalence theorems (Task 9) need the field.
- **Two lock writes, one break.** Task 0 hardens the lock script BEFORE the gate and rewrites the lock in the new format with no declaration changed (a format change: order-independent hashes, generated names by metadata). Tasks 1–5 then break the lock on purpose, and Task 6 writes it once more: that diff shows only the gate's changes. Both writes get a dated entry in the design's §8 lock change log. Approval of this plan is the user's approval of both, as for the receipt-relay lock rewrite (`0dd5993`).
- **The I1 gap becomes a compiled witness, not a fix.** Task 5 proves that a protocol that reads no input (`clockChain`) is a `Candidate`. The fix is plan 2's: a run-chosen proposer input is NOT enough (a protocol can ignore it, Astra A05); plan 2 needs a floor claim that binds the proposal to that input, and its regression test is a REFUTATION of `clockChain` (lifted) against that claim, not an elaboration failure. The v1 witness stays as a record. It lives in `AvailableChainRegistry/Gaps/`, and the registry marks its rows `KNOWN-GAP`, not `LEAN`.
- **The id rule for pulled and restated claims** (async M6). `ClaimSpec.pull` keeps the claim's id, and it exists only along a `DomainMap`: an equivalence of contexts that keeps admissibility (↔) and the horizon. A claim over another domain, or over a domain with a stronger `admissible` (for example a v1 domain with a `LinkedFG` run premise), is a NEW claim with a new id and a relation lemma to the old one. The optional pointwise `transport` (pull along any admissibility-keeping function) is NOT taken: it departs from the approved design text (§4, `transport` over all runs), and the id rule covers the FG-SA needs (async recommendation).
- **KNOWN-GAP consumer contract** (async M1). Registry rows with the status `KNOWN-GAP` are records, not results: `MATRIX.md` (plan 1b), Pareto sets and the explorer ignore them. After plan 2, a v1 `Candidate` is not the floor; `core.v2` (new id, new floor profile with an input-inclusion claim) is.
- **HooksSound stays run-level** (deviation (i)); `deps_stable` has the same shape as `processed_stable`.

## Global Constraints

- Toolchain and Mathlib v4.30.0-rc2. Do not run `lake update`.
- Committed proofs use no `sorry`, no `admit`, no project axioms and no `native_decide`. A `sorry` is allowed only between a task's statement step and its CHECKPOINT. `lake build --wfail` fails on every `sorry`. `scripts/Registry.lean` rejects every axiom outside `propext`, `Classical.choice`, `Quot.sound` in a certificate row.
- Work on `main` in `lean/available-chain` (user decision 2026-09-28: commit the work frequently). Commit only the task's files, by explicit path, with a message `Framework: <task title>`. Never stage `log.md`, `state.md`, `docs/FG-COMPOSITION.md`, or any file of `AvailableChainSimplexFG`, `AvailableChainKitFG`, or the FG scripts.
- Do not change `AvailableChainModel`, `AvailableChainStatements`, `AvailableChainGridCO`, `AvailableChainSA`, `AvailableChainSAPC`, `AvailableChainLStar` or `AvailableChainWitnesses`. `AvailableChainRegistry/GridCOHooks.lean` is in the registry and changes in Task 3.
- Layer rule (design §1): `AvailableChainFramework` modules other than `Kit/` import nothing from `AvailableChainRegistry` or `Kit/`. Catalog helper lemmas that a `transport` proof needs go in `AvailableChainFramework/Catalog/Mono.lean` (L3), not in `Kit/`.
- Builds. During the work: `lake build --wfail AvailableChainFramework AvailableChainRegistry`. At the end (Task 10): the full `lake build --wfail`. The Mac `lean` has 3 machine-wide slots: run `pgrep -fl lean` before a build and wait if 3 compiles run. Scripts run with `lake env lean --run <file>`, never through a `lean_exe`.
- Lock and registry during the gate. `lake env lean --run scripts/CatalogLock.lean --check` exits 0 after Task 0, exits 1 from Task 1 until Task 6 (expected), and exits 0 at every CHECKPOINT from Task 6 on (the hardened script exits 0 on additions only; run `--write` after the check to record them). `lake env lean --run scripts/Registry.lean` must run at every CHECKPOINT (Task 1 updates it for the new `Cert` arity).
- Lock stability of claims. The lock hashes a definition's body, so a `transport` proof written inline in a `ClaimSpec` definition is part of that claim's hash. Every new claim (Tasks 7, 8) puts its `transport` proof in a named theorem (`<claim>_transport`) and its `le_trans` proof in a named theorem (`<claim>_le_trans`), and the definition refers to them: a theorem enters the closure by its statement only (deviation (e)).
- `Time` is `abbrev Time := Int` in another module. `omega` does not unfold it in this toolchain: use `linarith`, `Int` order lemmas, or an explicit `(x : Int)` cast (PHASE0-REPORT §5.2, Tasks 4 and 9).
- Root imports. A task that creates a `.lean` file adds `public import <module>` for it to its library root (`AvailableChainFramework.lean` or `AvailableChainRegistry.lean`) in the same commit.
- Each task ends at a CHECKPOINT: the build is green; the registry script runs; the lock check has the result that this section states; the task is committed.
- Prose in comments and docs: ASD-STE100 Simplified Technical English. Tables: Unicode box drawing in fenced `text` blocks.
- Claim ids are immutable. A changed statement of an existing claim keeps its id only in this gate (the Task 6 regeneration is the one approved break); after Task 6 a changed statement is a new id.
- Axioms. From Task 0 on, `lake env lean --run scripts/CheckFrameworkAxioms.lean` exits 0 at every CHECKPOINT: every constant of `AvailableChainFramework` and `AvailableChainRegistry` uses only `propext`, `Classical.choice`, `Quot.sound` (async M3). Task 10 also greps `sorry|admit|native_decide` and `^axiom` in both libraries and the scripts.
- Lock diff per task (async M2). Each CHECKPOINT of Tasks 1–5 saves `CatalogLock --check` output against the Task 0 lock in the task report; the Task 6 change log is the last of these.
- `docs/REGISTRY.md` is regenerated and committed at every CHECKPOINT where its content changes.
- Lock diff hygiene (Task 0 review). `git diff docs/catalog.lock` at a CHECKPOINT has no `-` line unless the task's change log (Task 0 or Task 6) lists it: a deleted lock line turns a `CHANGED` into an `ADDED` (exit 0), and only the diff shows it.
- Scratch tests of the lock never define a second claim with an existing id (for example `eq_def := safeConfirmed`); the id-uniqueness check rejects it. Use a claim with its own id (Task 0 test (e2)).
- Late triggers. Every catalog claim whose trigger is not `True` has a lemma `<claim>_trigger_late` that shows the trigger time is at least `H` (the `ClaimSpec` shape cannot force it).

## Review Focus

1. **An early trigger for every horizon (I2).** Today `inhabited` accepts one trigger at slot 1 for every `H`. After Task 1, `trigger … H` must put the trigger at a time `≥ H`. Test: Task 1, `includedConfirmed_trigger_late`, and the rebuilt Counter certificate uses a slot `≥ H`.
2. **A facet claim that holds vacuously.** A claim that needs the strong output must not hold for an instance that has no strong output, and it must be refutable for an instance whose strong output is bad. Test: Task 4, `badStrong` refutes the test strong-safety claim.
3. **Profile certificates at different constants.** A profile certificate must use one shared constant for all its claims, and cross-claim conditions (`fastArmingLag ≤ armingLag`) must be checked once. Test: Task 2 (`certs` carry `x.const = e.share shared`), Task 9 (`ac43_valid_cross`).
4. **The lock hides a changed claim.** A changed or removed lock line must fail; an added claim must pass with a notice. Test: Task 6, three scratch runs of the hardened `--check`.
5. **An instance with no admissible context.** With `Δ ≤ 0` there is no environment, so every `holds` is vacuous. Test: Task 1 adds `Δ_pos`; Task 9's equivalence theorems use it.
6. **An empty outage window.** At `budget = 0` (valid) the Outage regime forces `b₁ = b₀`, so `PersistsThrough` is vacuous for every instance; a trigger without `b₀ < b₁` would let a vacuous certificate pass inhabitation. Test: Task 7, the persistence triggers require `b₀ < b₁`, and `persistOutage_no_witness_at_zero_budget` shows that no inhabitation witness exists at `budget = 0`.
7. **A lock that moves when a declaration is added.** The Phase 0 lock memoizes partial hashes inside dependency cycles, so adding one unrelated declaration changed 104 of 121 hashes (Astra A02). Test: Task 0, a scratch environment with one added declaration leaves every old hash unchanged.

---

### Task 0: Lock and registry hardening (before the gate)

**Files:**
- Modify: `scripts/CatalogLock.lean`, `scripts/Registry.lean`, `docs/catalog.lock`, `docs/REGISTRY.md`, `docs/FRAMEWORK-DESIGN.md` (§8 lock change log only)

**Interfaces:**
- Consumes: Phase 0 framework (no declaration changes in this task).
- Produces: `CatalogLock --check` by name with stable hashes, `--lock <path>`; `Registry --check`; `instanceLibraries` that drive the imports.

This task changes only the two scripts and the lock FORMAT. No Lean declaration changes. Doing it first makes the Task 6 lock diff show only the gate (opus P1a-13).

- [ ] **Step 1: Order-independent hashes** (Astra A02; PHASE0-REPORT M7). The Phase 0 `closureHash` memoizes partial hashes inside dependency cycles, so the hash of a root depends on the traversal order and on which other roots exist. Replace it:
  - `ownHash ci` stays (a theorem: its statement only; a definition: type and body; an inductive: its constructors).
  - `closure n` = the set of all constants reachable from `n` by `deps` (a DFS with a visited set, no memo of hashes).
  - `lockHash n` = the fold of `mixHash` over the `ownHash` of the names of `closure n ∪ {n}`, in `Name.lt` order.
  This depends only on the reachable set, not on the order or on other roots. To keep the run time low, cache `ownHash` per name (not the closure hash).
- [ ] **Step 2: Generated names by metadata, and claims always locked** (Astra A03; opus P1a-12; M6).
  - A constant is "generated" if the environment says so, not by its name: `isAuxRecursor env n`, `isNoConfusion env n`, `n.isInternal`, a `Lean.Meta.Match` matcher (`Match.isMatcherCore env n`), a declaration with no declaration range (`findDeclarationRanges?` returns `none`, run in `CoreM`), or an equation lemma that `Lean.Meta.isEqnThm?`/`getEqnsFor?` reports. A generated constant gets no lock line, but its `ownHash` still enters every closure that reaches it.
  - A constant whose type is `ClaimSpec …`, `Profile …`, `Profile.Entry …` or `ClaimDomain` is ALWAYS locked, whatever its name.
  - Locked modules: add `AvailableChainFramework.ClaimDomain`, `AvailableChainFramework.DomainMap` and the prefix `AvailableChainFramework.Facets` (L2) to the list now; the modules do not exist yet, and the list tolerates that.
- [ ] **Step 3: A separate axiom check** (Astra A04; M5). The hash stays proof-independent. Separately, for every locked name, run `Lean.collectAxioms` (proof-aware) and fail with exit 2 on any axiom outside `propext`, `Classical.choice`, `Quot.sound`. A missing constant in a closure still exits 2.
- [ ] **Step 4: Compare by name** (I8). Add `--lock <path>` (default `docs/catalog.lock`). `--check` reads the old lines into a map. For each old name: missing now → `REMOVED <name>`; a different hash → `CHANGED <name>`. For each new name → `ADDED <name>`. Exit 1 on any `REMOVED` or `CHANGED`; else exit 0 with the `ADDED` lines as a notice. A malformed line → exit 2.
- [ ] **Step 5: Tests (Review Focus 4 and 7)**, in scratch files under the session scratchpad, not in the repository:
  - (a) a lock copy with one hash changed → exit 1, `CHANGED`; (b) one line deleted → exit 0, `ADDED`; (c) one extra line with a name that does not exist → exit 1, `REMOVED`.
  - (d) Addition stability: a scratch module that imports `AvailableChainFramework` and adds one unrelated locked declaration (for example `def AvailableChain.Framework.AuditAddition : Bool := Nat.testBit 1 0` in a module under a locked prefix, or run the script's functions on that environment): every old hash is unchanged, and the only difference is `ADDED AuditAddition`.
  - (e) A hand-written `def AvailableChain.Framework.Catalog.eq_def : ClaimSpec := safeConfirmed` gets a lock line.
  - (f) `axiom auditBadAx : False; theorem auditBadTheorem : False := auditBadAx; def auditBadDefinition : True := False.elim auditBadTheorem` in a locked scratch module → exit 2.
  Record every output in the task report.
- [ ] **Step 6: Registry hardening** (PHASE0-REPORT §6, Registry rows; Astra A08; opus P1a-15).
  - `instanceLibraries : List Name := [`AvailableChainRegistry]` drives BOTH the `importModules` list and the module-prefix filter. The script prints the list in the REGISTRY.md header.
  - `--check`: compute the text and compare with `docs/REGISTRY.md`; exit 1 if different, 0 if the same. Without an argument, write the file (as now).
- [ ] **Step 6b: Additions from the async review** (M3, m7, m9, m11).
  - `scripts/CheckFrameworkAxioms.lean` (modelled on `scripts/CheckFGAxioms.lean`): every non-internal constant of the modules under `AvailableChainFramework` and `AvailableChainRegistry` has only `propext`, `Classical.choice`, `Quot.sound` as axioms (`collectAxioms`); else exit 1; print `checked N constants`.
  - Catalog id uniqueness: two different locked Lean names whose type is `ClaimSpec …` with the same `id` → exit 2 (a pulled claim keeps its base id and is exempt).
  - `--write` refuses (exit 1, prints the names) when the diff has a `CHANGED` or `REMOVED` name, unless `--allow-changes` is given; additions alone write normally. Test: change one definition body in a scratch copy; its line is `CHANGED`, and its generated `eq_def` has no line.
  - Registry `KNOWN-GAP`: a row from a module under `AvailableChainRegistry.Gaps` gets `KNOWN-GAP` only if its axiom check gives `LEAN`; `UNSOUND` and `CONDITIONAL` stay.
  - Locked modules and always-locked types use the names `ClaimDomain`, `DomainMap` (async m4).
- [ ] **Step 7: Rewrite the lock and log it.** Run `--write --allow-changes`. Record the git blob id of the old lock (`git rev-parse HEAD:docs/catalog.lock`) in the change log. Add a dated entry to `docs/FRAMEWORK-DESIGN.md` §8 "Lock change log": "Format change (plan 1a Task 0): order-independent hashes, generated names by metadata, claims always locked, a separate axiom check. No declaration changed; every line hash changes because the hash function changed; lines of generated names are gone." List the removed generated names in one line.
- [ ] **Step 8: CHECKPOINT.** `lake build --wfail AvailableChainFramework AvailableChainRegistry` is green (no Lean change). `CatalogLock --check` exits 0. `CheckFrameworkAxioms` exits 0. `Registry.lean` writes the same 8 rows; `Registry --check` exits 0. Commit `Framework: lock and registry hardening (format only)`.

### Task 1: Claim domains and domain-generic claims with late triggers

**Files:**
- Create: `AvailableChainFramework/ClaimDomain.lean`
- Modify: `AvailableChainFramework/Instance.lean`, `AvailableChainFramework/Claim.lean`, `AvailableChainFramework/Cert.lean`, `AvailableChainFramework/Pareto.lean`, `AvailableChainFramework/Profile.lean` (only the `ClaimSpec` → `ClaimSpec ClaimDomain.v1` change; Task 2 rewrites it), `AvailableChainFramework/Catalog/Core.lean`, `AvailableChainFramework.lean`
- Modify: `AvailableChainRegistry/Sanity.lean`, `AvailableChainRegistry/Counter.lean`, `AvailableChainRegistry/CounterRun.lean`, `AvailableChainRegistry/CounterIncluded.lean`, `AvailableChainRegistry/Tests/Pareto.lean`, `AvailableChainRegistry/Tests/NewFacet.lean` (delete its content except a module docstring that points to Task 4; Task 4 replaces it)
- Modify: `scripts/Registry.lean` (the `Cert K c I` arity)

**Interfaces:**
- Consumes: Phase 0 framework.
- Produces: `Validators`, `ClaimDomain` (`Inst`, `Ctx`, `admissible`, `horizon`), `V1Ctx`, `ClaimDomain.v1`, `Instance.Δ_pos`, `ClaimSpec K` with `trigger … (H : Time)`, `ClaimSpec.holds`, `ClaimSpec.inhabited`, `Cert c I`, `Refutation c I`, `RefutationFamily c I` for `c : ClaimSpec K`, `I : K.Inst`.

- [ ] **Step 1: Write `ClaimDomain.lean`.** Move `Validators` here from `Instance.lean` (same text).

```lean
module
public import Mathlib.Data.Fintype.Defs
public import AvailableChainModel.Objects.Time

@[expose] public section

namespace AvailableChain.Framework

/-- A finite validator type, bundled so that claims can quantify over it. -/
structure Validators where
  V : Type
  dec : DecidableEq V
  fin : Fintype V

attribute [instance] Validators.dec Validators.fin

/-- What a claim speaks about (design §3; carrier generalization, PHASE0-REPORT
§6 I3 and I5): a type of instances and, for each instance and validator type,
a type of run contexts. The v1 claim domain has an environment and a v1 run. A
facet or a new engine is a new claim domain value, not a change to `ClaimSpec`. -/
structure ClaimDomain where
  /-- A stable name (async m6), for example `v1`, `strong`. -/
  id : Lean.Name
  Inst : Type 1
  Ctx : Inst → Validators → Type
  /-- The contexts that a certificate covers (v1: the environment has the
  instance's Δ). -/
  admissible : (I : Inst) → (W : Validators) → Ctx I W → Prop
  /-- The last time of the run of a context. -/
  horizon : (I : Inst) → (W : Validators) → Ctx I W → Time

end AvailableChain.Framework

end
```

- [ ] **Step 2: Rewrite `Instance.lean`.** Import `ClaimDomain` and `Hooks`. Keep the `Instance` fields and add `Δ_pos`. Add the v1 context and claim domain. `ClaimDomain.v1` is `@[reducible]`, so that `x.E` and `x.rho` elaborate on `x : ClaimDomain.v1.Ctx I W`.

```lean
structure Instance where
  n : Nat
  P : ProtocolSpec n
  /-- Every certified environment has this Δ. -/
  Δ : Time
  Δ_pos : 0 < Δ
  iface : Interface P
  hooks : HooksSound P

/-- A v1 run context: an environment and a run of the instance's protocol. -/
structure V1Ctx (I : Instance) (W : Validators) where
  E : Env W.V
  rho : Run W.V I.P

/-- The v1 claim domain: today's instances with an environment and a v1 run. -/
@[reducible] def ClaimDomain.v1 : ClaimDomain where
  id := `v1
  Inst := Instance
  Ctx := V1Ctx
  admissible := fun I _ x => x.E.Δ = I.Δ
  horizon := fun _ _ x => x.rho.horizon
```

- [ ] **Step 3: Rewrite `Claim.lean` over a claim domain.** Import `ClaimDomain` only. The structure keeps its fields; `regime`, `conclusion` and `trigger` take `(I : K.Inst)` and `(x : K.Ctx I W)`. `trigger` gets a last argument `H : Time`.

```lean
variable {K : ClaimDomain}

structure ClaimSpec (K : ClaimDomain) where
  id : Lean.Name
  Const : Type
  valid : Const → Prop
  le : Const → Const → Bool
  le_refl : ∀ k, le k k = true
  le_trans : ∀ a b c, le a b = true → le b c = true → le a c = true
  Point : Type
  /-- The runs that the claim speaks about. -/
  regime : (I : K.Inst) → Const → (W : Validators) → K.Ctx I W → Point → Prop
  /-- What the claim states about such a run. -/
  conclusion : (I : K.Inst) → Const → (W : Validators) → K.Ctx I W → Point → Prop
  /-- `trigger I k W x p H`: the event that makes the claim non-vacuous occurs
  in the run at a time at least `H`, with its deadline inside the run
  (design §5; PHASE0-REPORT §6, I2). -/
  trigger : (I : K.Inst) → Const → (W : Validators) → K.Ctx I W → Point → Time → Prop
  /-- A weaker constant keeps the claim. A proof, not metadata. -/
  transport : ∀ (I : K.Inst) (k k' : Const), valid k → valid k' → le k k' = true →
    (∀ (W : Validators) (x : K.Ctx I W), K.admissible I W x → ∀ p,
      regime I k W x p → conclusion I k W x p) →
    (∀ (W : Validators) (x : K.Ctx I W), K.admissible I W x → ∀ p,
      regime I k' W x p → conclusion I k' W x p)
  refutable : RefutationKind

namespace ClaimSpec

/-- The claim holds for an instance at a constant. -/
def holds (c : ClaimSpec K) (I : K.Inst) (k : c.Const) : Prop :=
  ∀ (W : Validators) (x : K.Ctx I W), K.admissible I W x → ∀ p,
    c.regime I k W x p → c.conclusion I k W x p

/-- For every time `H`, the regime has an admissible run of the instance with
a horizon of at least `H`, in which the trigger occurs at a time of at least
`H` (design §5; I2). -/
def inhabited (c : ClaimSpec K) (I : K.Inst) (k : c.Const) : Prop :=
  ∀ H : Time, ∃ (W : Validators) (x : K.Ctx I W) (p : c.Point),
    K.admissible I W x ∧ H ≤ K.horizon I W x ∧ c.regime I k W x p ∧
      c.trigger I k W x p H

end ClaimSpec
```

- [ ] **Step 4: Generalize `Cert.lean` and `Pareto.lean`.** Add `variable {K : ClaimDomain}` and write `(c : ClaimSpec K) (I : K.Inst)` in `Cert`, `Refutation`, `RefutationFamily`, `Cert.weaken`, `Cert.not_refuted`, `Refutation.family_of`, and `c : ClaimSpec K` in every Pareto declaration. No other change. In `Profile.lean`, add `public import AvailableChainFramework.Instance` (Claim no longer imports it), and write `claims : List (ClaimSpec ClaimDomain.v1)` and `ProfileCert (p : Profile) (I : Instance)`; Task 2 replaces the file.

- [ ] **Step 5: Rewrite `Catalog/Core.lean` over `ClaimDomain.v1`.** Every claim is `ClaimSpec ClaimDomain.v1`. `sleepy` keeps its signature. In `safeOf` and `includedConfirmed`, `regime := fun I _ W x t₀ => sleepy I W x.E x.rho t₀`, and `conclusion` reads `x.E`, `x.rho`. `prefixOrder` stays UNCONDITIONAL (Astra A01): `Point := Unit`, `regime := fun _ _ _ _ _ => True`, `conclusion := fun I _ _ x _ => OutputOrder I.P I.iface x.rho`; only its context arguments change (the bundle's `nested` field covers every run). Safety and prefix triggers are `fun _ _ _ _ _ _ => True` (the regime's `H ≤ horizon` carries the time). The inclusion trigger:

```lean
  trigger := fun I D _ x t₀ H =>
    ∃ s : Slot, t₀ < I.P.proposalTime s ∧ H ≤ I.P.proposalTime s ∧
      HonestAwakeProposer x.E x.rho s ∧ I.P.proposalTime s + D ≤ x.rho.horizon
```

Add this lemma after `includedConfirmed`:

```lean
/-- Review Focus 1 (I2): an inhabitation witness of `includedConfirmed` puts
its proposal at a time of at least `H`. -/
theorem includedConfirmed_trigger_late {I : Instance} {D : Time} {H : Time}
    (h : includedConfirmed.inhabited I D) :
    ∃ (W : Validators) (x : ClaimDomain.v1.Ctx I W) (s : Slot),
      H ≤ I.P.proposalTime s ∧ HonestAwakeProposer x.E x.rho s := by
  sorry
```

Proof guide: `obtain ⟨W, x, t₀, _, _, _, s, _, hH, hp, _⟩ := h H; exact ⟨W, x, s, hH, hp⟩`.

`core`, `Candidate` and `not_candidate_of_family` keep their Phase 0 form in this task (Task 2 replaces them).

- [ ] **Step 6: Update the registry instances.** `Sanity.sanity` and `Counter.counterInst` add `Δ_pos := by norm_num` (or `zero_lt_one`). Every certificate's `inhabited` proof changes to the new shape `∃ W x p, admissible ∧ H ≤ horizon ∧ regime ∧ trigger … H`, with `x := ⟨E, rho⟩`. Every `proof` field takes `W x hΔ p hreg` and uses `x.E`, `x.rho`.
  - `Counter.certIncluded`: the trigger slot must be at least `H`. Use the canonical run `canonical 0 N` with `N := (max H 2).toNat + 1` and the slot `s := N - 1`; then `H ≤ s`, `0 < s`, and `s + 1 ≤ N`. Replace `horizon_ge` by a lemma that gives these three facts. `Time` rule of the Global Constraints applies.
  - `Sanity.refutedIncluded` and `Sanity.not_candidate`: only the context shape changes.
  - `Tests/Pareto.lean`: `armedToy : ClaimSpec ClaimDomain.v1`, with `regime` and `conclusion` of 5 binders (`fun _ _ _ _ _ => True`), `trigger` of 6 (`fun _ _ _ _ _ _ => True`), and the `transport` intro `intro _ _ _ _ _ _ _ W x hΔ p _`.
  - `Tests/NewFacet.lean`: remove `HasStrong` and `safeStrong`; keep a module docstring "Replaced by the strong claim domain test (Task 4)." and an empty section, so the root import stays valid.

- [ ] **Step 6b: Meaning pins** (async M2). Create `AvailableChainFramework/Catalog/Meaning.lean` (L3, locked). For each of the four existing claims, two theorems that state `holds` and `inhabited` in the Phase 0 form, with L1 predicates only. Example:

```lean
theorem includedConfirmed_holds_iff (I : Instance) (D : Time) :
    includedConfirmed.holds I D ↔
      ∀ (W : Validators) (E : Env W.V), E.Δ = I.Δ → ∀ (rho : Run W.V I.P) (t₀ : Time),
        SleepyRegime I.P E I.iface rho t₀ →
          IncludedFrom I.P E I.iface rho I.iface.confirmed t₀ D :=
  ⟨fun h W E hE rho t₀ hr => h W ⟨E, rho⟩ hE t₀ hr,
   fun h W x hx t₀ hr => h W x.E hx x.rho t₀ hr⟩
```

  The `inhabited` pins state the Phase 0 form plus the late-trigger condition; the only intended difference from Phase 0 (`Claim.lean:52-60` at `505b14a`) is `H ≤ proposalTime s` in `includedConfirmed`. A reviewer compares each pin with the Phase 0 definitions. Add the module to the library root.

- [ ] **Step 7: Update `scripts/Registry.lean`.** `Cert`, `Refutation` and `RefutationFamily` now have the arguments `K c I`. Read the claim from `args[1]!` and the instance from `args[2]!`. Everything else stays.

- [ ] **Step 8: CHECKPOINT.** `lake build --wfail AvailableChainFramework AvailableChainRegistry` is green. `lake env lean --run scripts/Registry.lean` regenerates `docs/REGISTRY.md` with the same 8 rows, all `LEAN`. `scripts/CatalogLock.lean --check` exits 1 (expected; Task 6 regenerates). `CheckFrameworkAxioms` exits 0. Save the lock diff against the Task 0 lock in the report. Commit with `Framework: claim domains, domain-generic claims, late triggers`, staging the files above, `Catalog/Meaning.lean` and `docs/REGISTRY.md`.

### Task 2: Profiles with shared constants

**Files:**
- Modify: `AvailableChainFramework/Profile.lean`, `AvailableChainFramework/Catalog/Core.lean`, `AvailableChainRegistry/CounterIncluded.lean`, `AvailableChainRegistry/Sanity.lean`

**Interfaces:**
- Consumes: Task 1 (`ClaimSpec K`, `Cert`, `ClaimDomain.v1`).
- Produces: `Profile.Entry K S`, `Profile K` (`id`, `Shared`, `valid`, `entries`), `ProfileCert p I` (a structure: `shared`, `valid`, `certs`), `Profile.holdsAt`, `ProfileCert.holdsAt`, `Catalog.core : Profile ClaimDomain.v1`, `Catalog.Candidate`, `Catalog.not_candidate_of_family`.

- [ ] **Step 1: Rewrite `Profile.lean`.**

```lean
variable {K : ClaimDomain}

/-- One claim of a profile, with the projection of the shared constants to the
claim's own constant (design §4, profiles; PHASE0-REPORT §5.1 (g)). -/
structure Profile.Entry (K : ClaimDomain) (S : Type) where
  spec : ClaimSpec K
  share : S → spec.Const

/-- A named set of catalog claims with shared constants. `valid` holds the
conditions that relate constants of different claims (for `ac-4.3`, all of
`Constants.Valid`). -/
structure Profile (K : ClaimDomain) where
  id : Lean.Name
  Shared : Type
  valid : Shared → Prop
  entries : List (Profile.Entry K Shared)

/-- One certificate per claim of the profile, all for one instance, all at the
projections of ONE shared constant. -/
structure ProfileCert (p : Profile K) (I : K.Inst) : Type 1 where
  shared : p.Shared
  valid : p.valid shared
  certs : ∀ e ∈ p.entries, {x : Cert e.spec I // x.const = e.share shared}

/-- The claims of a profile hold at one shared constant (no inhabitation). -/
def Profile.holdsAt (p : Profile K) (I : K.Inst) (C : p.Shared) : Prop :=
  p.valid C ∧ ∀ e ∈ p.entries, e.spec.valid (e.share C) ∧ e.spec.holds I (e.share C)

theorem ProfileCert.holdsAt {p : Profile K} {I : K.Inst} (pc : ProfileCert p I) :
    p.holdsAt I pc.shared := by
  sorry
```

Proof guide: `refine ⟨pc.valid, fun e he => ?_⟩`; take `⟨x, hx⟩ := pc.certs e he`; rewrite with `hx` in `x.valid` and `x.proof`.

- [ ] **Step 2: Rewrite `core`, `Candidate` and `not_candidate_of_family` in `Catalog/Core.lean`.** The core shares one constant, the inclusion delay `D`.

```lean
/-- The core floor (design §4): every candidate certifies all four claims.
The shared constant is the inclusion delay `D`. -/
def core : Profile ClaimDomain.v1 where
  id := `core.v1
  Shared := Time
  valid := fun D => 0 ≤ D
  entries :=
    [⟨safeConfirmed, fun _ => ()⟩, ⟨safeStable, fun _ => ()⟩,
     ⟨prefixOrder, fun _ => ()⟩, ⟨includedConfirmed, fun D => D⟩]

/-- A candidate protocol passes the core floor. -/
def Candidate (I : Instance) : Type 1 := ProfileCert core I

/-- A refutation family of a core claim rejects the instance. -/
theorem not_candidate_of_family {I : Instance} {e : Profile.Entry ClaimDomain.v1 Time}
    (he : e ∈ core.entries) (r : RefutationFamily e.spec I) : Candidate I → False := by
  sorry
```

Proof guide: `intro pc; exact (pc.certs e he).1.not_refuted r`.

- [ ] **Step 3: Rebuild the registry users.** `Counter.candidate : Candidate counterInst` is a `ProfileCert` with `shared := (1 : Time)` (a bare `1` needs `OfNat core.Shared`, which fails), `valid := zero_le_one`, and `certs`. The membership `he : e ∈ core.entries` is a `Prop` and cannot be eliminated into data, so use the Phase 0 pattern (PHASE0-REPORT §5.2, Task 9): `classical`, then `if h1 : e = ⟨safeConfirmed, fun _ => ()⟩ then (by subst h1; exact ⟨certSafeConfirmed, rfl⟩) else if …`, and in the last branch derive `e = ⟨includedConfirmed, fun D => D⟩` from `he` and the three negations. `simp [core]` and `tauto` do not work on this membership (the element type `Profile.Entry … core.Shared` does not unfold at reducible transparency): first `change e ∈ ([_, _, _, _] : List (Profile.Entry ClaimDomain.v1 Time)) at he`, then `simp only [List.mem_cons, List.not_mem_nil, or_false] at he`; or use `List.mem_cons.1` in term mode (tested in `/private/tmp/p1a-scratch/Core.lean`, `testCandidate`). `candidate` stays `noncomputable`. `Sanity.not_candidate` proves the membership of `⟨includedConfirmed, fun D => D⟩` the same way.

- [ ] **Step 4: Add a Review Focus 3 test** in `CounterIncluded.lean`:

```lean
/-- Review Focus 3: every certificate of Counter's candidate is at the
projection of the one shared delay. -/
example (e : Profile.Entry ClaimDomain.v1 Time) (he : e ∈ core.entries) :
    (candidate.certs e he).1.const = e.share candidate.shared :=
  (candidate.certs e he).2
```

- [ ] **Step 5: CHECKPOINT.** Build green; the registry has 8 rows, all `LEAN` (`ProfileCert` values are not rows until Task 6). Lock `--check` exits 1 (expected). Commit `Framework: profiles with shared constants`.

### Task 3: `depsPresent` in `HooksSound`

**Files:**
- Modify: `AvailableChainFramework/Hooks.lean`, `AvailableChainRegistry/Sanity.lean`, `AvailableChainRegistry/Counter.lean`, `AvailableChainRegistry/GridCOHooks.lean`

**Interfaces:**
- Consumes: Task 1.
- Produces: `HooksSound.deps_stable`.

- [ ] **Step 1: Add the field** after `processed_stable` (PHASE0-REPORT §5.1 (h); design E4: `depsPresent` is monotone within one epoch; v1 has one epoch per run):

```lean
  /-- `depsPresent` is monotone along a run (design E4). -/
  deps_stable : ∀ {V : Type} [DecidableEq V] [Fintype V] (E : Env V)
    (rho : Run V P), ScheduleWellFormed E rho → ∀ v o i j, i ≤ j →
      P.depsPresent (Run.stateBefore P rho i v) o = true →
      P.depsPresent (Run.stateBefore P rho j v) o = true
```

- [ ] **Step 2: Prove it for the three protocols.**
  - Sanity (`alwaysGenesis`): `depsPresent = true`; the proof is `fun … h => h` (as `processed_stable`).
  - Counter: `depsPresent st o = decide (o.payload ≤ st + 1)`; use `stateBefore_mono rho hij v` (as `counter_hooks.processed_stable`).
  - `gridCOx`: `depsPresent st o` is `true` for a HEAD and `blockKnown st b.parent` for a proposal. Use `stateBefore_stable` with the predicate `fun st => depsPresent st o = true`, `clock_blocks` for the clock step and `process_blocks_subset` for the process step, as in the proposal case of `processed_stable`.

- [ ] **Step 3: CHECKPOINT.** Build green; registry unchanged. Lock `--check` exits 1 (expected). Commit `Framework: depsPresent in HooksSound`.

### Task 4: Facets as claim domains (the strong output)

**Files:**
- Create: `AvailableChainFramework/Facets/Strong.lean`, `AvailableChainFramework/DomainMap.lean`
- Modify: `AvailableChainFramework.lean`, `AvailableChainRegistry/Tests/NewFacet.lean`

**Interfaces:**
- Consumes: Tasks 1–2.
- Produces: `DomainMap K' K` (`inst`, `ctx`, `admissible`, `horizon`), `ClaimSpec.pull`, `ClaimSpec.holds_pull`, `ClaimSpec.inhabited_pull`, `Cert.pull`, `StrongInstance` (extends `Instance` with `strong`), `StrongInstance.sface`, `ClaimDomain.strong`, `DomainMap.strongV1 : DomainMap ClaimDomain.strong ClaimDomain.v1`.

- [ ] **Step 1: Write `DomainMap.lean`.** A map from claim domain `K'` to claim domain `K` sends each `K'` instance to a `K` instance and identifies their contexts. Base claims then pull back.

```lean
variable {K K' : ClaimDomain}

/-- A claim domain map from `K'` to `K` (a facet claim domain to its base, design G2):
an instance map and an equivalence of contexts that keeps admissibility and
the horizon. -/
structure DomainMap (K' K : ClaimDomain) where
  inst : K'.Inst → K.Inst
  ctx : ∀ I W, K'.Ctx I W ≃ K.Ctx (inst I) W
  admissible : ∀ I W x, K'.admissible I W x ↔ K.admissible (inst I) W (ctx I W x)
  horizon : ∀ I W x, K'.horizon I W x = K.horizon (inst I) W (ctx I W x)

namespace ClaimSpec

/-- The claim `c` over `K`, read on `K'` through `m`. Same id, constants and
points. -/
def pull (m : DomainMap K' K) (c : ClaimSpec K) : ClaimSpec K' where
  id := c.id
  Const := c.Const
  valid := c.valid
  le := c.le
  le_refl := c.le_refl
  le_trans := c.le_trans
  Point := c.Point
  regime := fun I k W x p => c.regime (m.inst I) k W (m.ctx I W x) p
  conclusion := fun I k W x p => c.conclusion (m.inst I) k W (m.ctx I W x) p
  trigger := fun I k W x p H => c.trigger (m.inst I) k W (m.ctx I W x) p H
  transport := by sorry
  refutable := c.refutable

theorem holds_pull (m : DomainMap K' K) (c : ClaimSpec K) (I : K'.Inst) (k : c.Const) :
    (c.pull m).holds I k ↔ c.holds (m.inst I) k := by
  sorry

theorem inhabited_pull (m : DomainMap K' K) (c : ClaimSpec K) (I : K'.Inst) (k : c.Const) :
    (c.pull m).inhabited I k ↔ c.inhabited (m.inst I) k := by
  sorry

end ClaimSpec

/-- A certificate of the base instance is a certificate of the pulled claim. -/
def Cert.pull (m : DomainMap K' K) {c : ClaimSpec K} {I : K'.Inst}
    (x : Cert c (m.inst I)) : Cert (c.pull m) I where
  const := x.const
  valid := x.valid
  inhabited := (ClaimSpec.inhabited_pull m c I x.const).2 x.inhabited
  proof := (ClaimSpec.holds_pull m c I x.const).2 x.proof
```

Proof guides: `transport` — from the `k` form on `K'`, get the `k` form on `K` by `(m.ctx I W).symm` (use `Equiv.apply_symm_apply` and `m.admissible`), apply `c.transport`, and come back with `m.ctx I W x`. `holds_pull` — both directions through the equivalence, as for `transport`. `inhabited_pull` — `→`: map the witness context with `m.ctx`, use `m.admissible` and `m.horizon`; `←`: map back with `(m.ctx I W).symm` and rewrite with `Equiv.apply_symm_apply`.

- [ ] **Step 1b: One builder for facet domains over v1** (async m5), in `DomainMap.lean`:

```lean
/-- The domain of a facet structure `J` over v1 instances: contexts, admissibility
and horizon are those of the base instance, so they cannot drift. -/
@[reducible] def ClaimDomain.ofV1 (id : Lean.Name) (J : Type 1) (base : J → Instance) :
    ClaimDomain where
  id := id
  Inst := J
  Ctx := fun I W => V1Ctx (base I) W
  admissible := fun I _ x => x.E.Δ = (base I).Δ
  horizon := fun _ _ x => x.rho.horizon

def DomainMap.ofV1 (id : Lean.Name) (J : Type 1) (base : J → Instance) :
    DomainMap (ClaimDomain.ofV1 id J base) ClaimDomain.v1 where
  inst := base
  ctx := fun _ _ => Equiv.refl _
  admissible := fun _ _ _ => Iff.rfl
  horizon := fun _ _ _ => rfl
```

  A map between two facet domains whose base instances are only propositionally equal needs a cast (`▸` fails; async scratch `Builder.lean`); say so in the docstring.

- [ ] **Step 2: Write `Facets/Strong.lean`.**

```lean
/-- An instance with the strong output (`StrongInterface`): the facet is a
field, so it is bound once (design §3). -/
structure StrongInstance extends Instance where
  strong : P.State → Block

/-- The strong interface of a strong instance. -/
def StrongInstance.sface (I : StrongInstance) : StrongInterface I.P :=
  { I.iface with strong := I.strong }

/-- The claim domain of strong instances. Its contexts are the v1 contexts of the
base instance. -/
@[reducible] def ClaimDomain.strong : ClaimDomain :=
  ClaimDomain.ofV1 `strong StrongInstance StrongInstance.toInstance

/-- Base claims pull back to strong instances. -/
def DomainMap.strongV1 : DomainMap ClaimDomain.strong ClaimDomain.v1 :=
  DomainMap.ofV1 `strong StrongInstance StrongInstance.toInstance
```

- [ ] **Step 3: Replace `Tests/NewFacet.lean`** with a test of Review Focus 2 and of the pull. Use Counter.
  - `counterStrong : StrongInstance := { counterInst with strong := counterIface.stable }`.
  - `certSafeStableStrong : Cert (safeStable.pull DomainMap.strongV1) counterStrong := Cert.pull _ certSafeStable`.
  - A test claim `testStrongSafe : ClaimSpec ClaimDomain.strong` (id `test.strongSafe.v1`, `Const := Unit`, `Point := Time`, regime `sleepy I.toInstance W x.E x.rho t₀`, conclusion `SafeFrom I.P x.rho I.strong t₀`, trigger `True`).
  - `badStrong : StrongInstance := { counterInst with strong := fun st => if st = 1 then Counter.chain 1 else .genesis }`.
  - `refutedBadStrong : RefutationFamily testStrongSafe badStrong`. Proof guide: take the canonical run `canonical 0 2` with `counterEnv 0` and `canonical_sleepy`; at the node `0` the state after time 0 is 1 and after time 1 is 2 (`stateBeforeTime_eq`, `readAt` of the canonical run; Counter delivers the proposal `t + 1` at time `t`), so the strong read is `chain 1` at `t = 0` and `genesis` at `t = 1`; `MonotoneFrom` fails because `chain 1 ⋠ genesis`.
  - A docstring: "Only a `StrongInstance` can hold a certificate of a `ClaimSpec ClaimDomain.strong`. An `Instance` without the strong output has no such claim: the vacuity of `∀ I [HasStrong I], …` (PHASE0-REPORT §6) cannot occur."

- [ ] **Step 4: CHECKPOINT.** Build green. The registry gets one new `refutation-family` row (`refutedBadStrong`, claim `NON-CATALOG`) and one `cert` row (`certSafeStableStrong`), both `LEAN`. Lock `--check` exits 1 (expected). Commit `Framework: facets as claim domains`.

### Task 5: The I1 witness (a no-input protocol passes the floor)

**Files:**
- Create: `AvailableChainRegistry/Gaps/NoInput.lean`
- Modify: `AvailableChainRegistry.lean`

**Interfaces:**
- Consumes: Tasks 1–3.
- Produces: `Gaps.NoInput.clockChain : ProtocolSpec 1`, `clockInst : Instance`, `clockCandidate : Candidate clockInst`.

This task compiles the gap of design §12 (I1). It does not fix it. Plan 2 fixes it with a run-chosen proposer input AND a floor claim that binds the proposal to that input; a run input alone is not enough, because a protocol can ignore it (Astra A05). Plan 2's regression test is a refutation of this protocol (lifted to v2) against that claim. This v1 certificate stays valid as a record of the gap.

- [ ] **Step 1: Write the protocol.** It reads no delivered object. Its state is the largest tick time so far (`max`), so the Counter sublist argument (`readAt_mono`) gives monotone reads in every run (opus P1a-16). Its outputs are the chain of all slots up to that time. Its proposal for slot `s` is the block of slot `s`, which every node can compute.

```lean
/-- The block of slot `k` on the clock chain. -/
def clockBlock : Nat → Block
  | 0 => .genesis
  | k + 1 => .node (clockBlock k) (k + 1) ⟨k + 1⟩

/-- A protocol that reads no input (design §12, I1): it excludes every
object, and its outputs depend on the clock only. -/
def clockChain : ProtocolSpec 1 where
  State := Time
  Label := Empty
  Payload := Nat
  init := 0
  clock := fun st t => max st t
  actTime := fun ℓ => ℓ.elim
  duties := fun _ => []
  duties_spec := fun ℓ _ => ℓ.elim
  duties_nodup := fun _ => List.nodup_nil
  act := fun _ ℓ => ℓ.elim
  proposalTime := fun s => s
  slotsAt := fun t => if 0 ≤ t then [t.toNat] else []
  slotsAt_spec := sorry
  slotsAt_nodup := sorry
  propose := fun _ s => some s
  gossip := fun _ _ => []
  process := fun st _ => st
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => true
  handles := fun _ o o' => o = o'
  carries := fun _ _ => False

def clockIface : Interface clockChain where
  confirmed := fun st => clockBlock st.toNat
  stable := fun st => clockBlock st.toNat
  block := fun k => some (clockBlock k)
  opening := fun _ => True
```

Proof guide for `slotsAt_spec` and `slotsAt_nodup`: copy Counter's proofs (`Counter.lean`, same `slotsAt`).

- [ ] **Step 2: Hooks and instance.** `clockHooks : HooksSound clockChain` (every field is immediate: `process` is the identity, `excludes` is always true, `processed` is always false, `depsPresent` is always true). `clockInst` with `n := 1`, `Δ := 1`, `Δ_pos := zero_lt_one`.

- [ ] **Step 3: The four certificates and the candidate.** At `D = 0`.
  - Safety of both outputs: in a run, the state of a node after its events up to `t` is the largest of `0` and its tick times at or before `t`. Every read is `clockBlock m` for some `m`; `clockBlock a ⪯ clockBlock b` when `a ≤ b`, so reads agree; the state is monotone along any sublist of events (as Counter's `readAt_mono`), so reads only extend.
  - Prefix: the two outputs are equal.
  - Inclusion at `D = 0`: for a slot `s` with `0 < s`, an honest awake proposer ticks at `s` (`tick_total`; `s` is public with `Δ = 1`), emits `⟨.proposer s, s⟩`, and `block s = clockBlock s`. Every honest node ticks at `s`, so its read at `s` is `clockBlock s`.
  - Inhabitation: a one-validator run with a tick at every integer time `0 … N` and no delivery, as `AvailableChainWitnesses/Sanity.lean` (`exampleRun`, `exampleExecution`, `exampleSynchrony`, `exampleRootInjective`, `exampleSleepy`). `PartialSynchrony` holds because `excludes` is always true and nothing is accepted. `RootInjective`: the roots of `clockBlock k` are `⟨k⟩`. For the late inclusion trigger, take the slot `max H 1` (as a natural number) and a horizon of at least that slot.
  - `clockCandidate : Candidate clockInst` with `shared := 0`.

- [ ] **Step 4: Docstring.** The module docstring also states that the gap does not depend on `excludes := true`: with `excludes := false` the same protocol still passes (its witness run then needs delivery events for broadcast), so plan 2 cannot close I1 by an exclusion rule (async M1). It states: "KNOWN GAP I1 (design §12). This protocol reads no input and still passes the core floor. The floor is too weak until engine v2 gives the proposer a run-chosen input (plan 2). The explorer stays off until then. The registry marks these rows `KNOWN-GAP` (Task 6)."

- [ ] **Step 5: CHECKPOINT.** Build green. The registry now lists `clockChain`'s four certificates as `LEAN` (Task 6 relabels them). Lock `--check` exits 1 (expected). Commit `Framework: compiled witness of gap I1`.

### Task 6: Registry row kinds and the gate lock regeneration

**Files:**
- Modify: `scripts/Registry.lean`, `docs/catalog.lock`, `docs/REGISTRY.md`, `docs/FRAMEWORK-DESIGN.md` (§8 lock change log only)

**Interfaces:**
- Consumes: Tasks 0–5.
- Produces: registry row kinds `profile-cert` and the `KNOWN-GAP` status; the post-gate lock.

- [ ] **Step 1: Registry row kinds** (PHASE0-REPORT §6, Registry rows).
  - Row kinds: add `(``AvailableChain.Framework.ProfileCert, "profile-cert")` (args `K p I`; the claim column shows the profile name) and `(``AvailableChain.Framework.Catalog.Candidate, "profile-cert")` (args `I`; the claim column shows `core.v1`). `Candidate I` is a `def`, so its type head is `Candidate`, not `ProfileCert`.
  - Pulled claims: a certificate of `ClaimSpec.pull m c` has the head `ClaimSpec.pull` with FOUR arguments (`@ClaimSpec.pull K' K m c`); print the pulled claim `c` (the LAST argument) in the claim column, with the suffix `(pulled)`.
- [ ] **Step 2: Regenerate the lock and write the change log.** First run `--check` against the Task 0 lock and save its output: the `CHANGED`, `REMOVED` and `ADDED` names are exactly the gate's changes (Task 0 removed the format noise). Then run `--write --allow-changes`. Add a dated entry to `docs/FRAMEWORK-DESIGN.md` §8 "Lock change log": the gate of plan 1a, approved with the plan; the saved `CHANGED`/`REMOVED`/`ADDED` lists; for each changed L3 claim (`safeConfirmed`, `safeStable`, `prefixOrder`, `includedConfirmed`, `core`, `Candidate`), its old and new type in one line each; no certificate conclusion changed; the registry rows after regeneration. Then run `--check`: exit 0.
- [ ] **Step 3: CHECKPOINT.** Build green. `CatalogLock --check` exits 0. `Registry.lean` writes the table with 2 `profile-cert` rows (Counter `candidate`, and `clockCandidate` with `KNOWN-GAP`) and the pulled Counter certificate with its base claim; `Registry --check` exits 0 after the write. Commit `Framework: registry row kinds; gate lock regeneration`.

### Task 7: Standard tier claims

**Files:**
- Create: `AvailableChainFramework/Catalog/Mono.lean`, `AvailableChainFramework/Catalog/Standard.lean`
- Modify: `AvailableChainFramework.lean`

**Interfaces:**
- Consumes: Tasks 1, 6.
- Produces: `Catalog.zeroConstants`, the constant records `EtaConst`, `OutageConst`, `RecoveryConst`, and the claims `includedStable`, `includedStableFast`, `persistOutage`, `persistOutageFast`, `recovered` (all `ClaimSpec ClaimDomain.v1`); the Mono lemmas.

The claims restate the fields of `AvailableChain` (`Generic/Claims.lean`) one by one. Each claim's constant is exactly the constants that its regime and conclusion read. The per-parameter directions are those of design §4: the claim is weaker when θ ↑, θrec ↑, η ↑, A ↑, A_f ↑, ρ ↑, recoveryFull false → true, G ↓, Π ↓. Exact-time inclusion delays are fixed (`le` is equality).

- [ ] **Step 1: Write `Mono.lean`** (statements; proofs in Step 3).

```lean
/-- All constants zero, `θ = θrec = 1/2`, `recoveryFull = false`. A claim sets
only the fields that it reads. -/
def zeroConstants : Constants where
  η := 0
  D_c := 0
  D_s := 0
  D_f := 0
  armingLag := 0
  fastArmingLag := 0
  budget := 0
  recoveryBound := 0
  proposerGap := 1
  θ := 1 / 2
  θrec := 1 / 2
  recoveryFull := false

/-- A larger θ or η makes the η-sleepy inequality harder. -/
theorem etaSleepy_mono {V : Type} [DecidableEq V] [Fintype V] {n : Nat}
    {P : ProtocolSpec n} {E : Env V} {C C' : Constants} {rho : Run V P} {t : Time}
    (hθ : C.θ ≤ C'.θ) (hη : C.η ≤ C'.η) (hθ0 : 0 ≤ C.θ)
    (h : EtaSleepy E C' rho t) : EtaSleepy E C rho t := by
  sorry

/-- A smaller gap makes the recurrence premise harder. -/
theorem recurrence_mono {V : Type} [DecidableEq V] {n : Nat} {P : ProtocolSpec n}
    {E : Env V} {I : Interface P} {rho : Run V P} {start g g' : Time}
    (hg : g' ≤ g) (h : HonestProposerRecurrence E I rho start g') :
    HonestProposerRecurrence E I rho start g := by
  sorry

/-- Safety from a later time. -/
theorem safeFrom_mono {V : Type} [DecidableEq V] {n : Nat} {P : ProtocolSpec n}
    {rho : Run V P} {g : Output P} {t₀ t₁ : Time} (ht : t₀ ≤ t₁)
    (h : SafeFrom P rho g t₀) : SafeFrom P rho g t₁ := by
  sorry

/-- Inclusion from a later time. -/
theorem includedFrom_mono {V : Type} [DecidableEq V] {n : Nat} {P : ProtocolSpec n}
    {E : Env V} {I : Interface P} {rho : Run V P} {g : Output P} {t₀ t₁ D : Time}
    (ht : t₀ ≤ t₁) (h : IncludedFrom P E I rho g t₀ D) : IncludedFrom P E I rho g t₁ D := by
  sorry
```

Proof guides: `etaSleepy_mono` — `awakeInClosed E H (t − C.η) t ⊆ awakeInClosed E H (t − C'.η) t` (a wider window), so the card of the union with `faulty` grows; then `C.θ * a ≤ C.θ * b ≤ C'.θ * b < …` (`mul_le_mul`, card casts are `≥ 0`). `recurrence_mono` — for `t` with `t + g ≤ horizon`, also `t + g' ≤ horizon`; the slot in `(t, t + g']` is in `(t, t + g]`. The other two restrict the quantifiers.

- [ ] **Step 2: Write `Standard.lean`.** One constant record per regime family.

```lean
structure EtaConst where
  η : Time
  θ : ℚ
  D : Time

structure OutageConst where
  η : Time
  θ : ℚ
  /-- The arming lag (`armingLag`, or `fastArmingLag` for the fast claim). -/
  lag : Time
  /-- Π, the outage budget. (`Π` is a Lean keyword, so the field is `budget`.) -/
  budget : Time

structure RecoveryConst where
  θrec : ℚ
  full : Bool
  G : Time
  ρ : Time
  D_c : Time
  D_s : Time
```

Claims (ids, constants, validity, order, point, regime, conclusion, trigger). `C(k)` is `zeroConstants` with only the listed fields set.

```text
┌────────────────────┬──────────────────────────────┬────────────────────────────────────┐
│ Claim (id)         │ Const, valid, le             │ Point; regime; conclusion; trigger │
├────────────────────┼──────────────────────────────┼────────────────────────────────────┤
│ includedStable     │ EtaConst; 0 ≤ η, 1/2 ≤ θ ≤   │ Time t₀; StableSleepyRegime with   │
│ std.included.      │ 3/4, 0 ≤ D; le: η ≤ η',      │ C(η, θ); IncludedFrom … stable t₀  │
│ stable.v1          │ θ ≤ θ', D = D'               │ D; inclusion trigger (as core)     │
│ includedStableFast │ Time D; 0 ≤ D; le: equality  │ Time t₀; FastRegime; IncludedFrom  │
│ std.included.      │                              │ … stable t₀ D; inclusion trigger   │
│ stableFast.v1      │                              │                                    │
│ persistOutage      │ OutageConst; 0 ≤ η, θ bounds,│ Time × Time × Time (T, b₀, b₁);    │
│ std.persist.       │ 0 ≤ lag, 0 ≤ budget, budget  │ OutageRegime with C(η, θ, lag as   │
│ outage.v1          │ ≤ η; le: η ≤ η', θ ≤ θ',     │ armingLag, budget);                │
│                    │ lag ≤ lag', budget' ≤ budget │ PersistsThrough … stable T b₀ b₁;  │
│                    │                              │ trigger: H ≤ T ∧ b₀ < b₁ ∧ some    │
│                    │                              │ honest read                        │
│                    │                              │ of stable at T is not genesis      │
│ persistOutageFast  │ OutageConst (lag is A_f);    │ as persistOutage, with             │
│ std.persist.       │ the same valid and le        │ FastOutageRegime and C(η, θ, lag   │
│ outageFast.v1      │                              │ as fastArmingLag, budget)          │
│ recovered          │ RecoveryConst; θrec bounds,  │ Unit; RecoveryRegime with C(θrec,  │
│ std.recovered.v1   │ 0 < G, 0 ≤ ρ, 0 ≤ D_c,       │ full, G, ρ); RecoveredAt with      │
│                    │ 0 ≤ D_s; le: θrec ≤ θrec',   │ C(D_c, D_s) at E.t_GST + ρ;        │
│                    │ (full → full'), G' ≤ G,      │ trigger: a slot s with GST + ρ <   │
│                    │ ρ ≤ ρ', D_c = D_c', D_s =    │ pt s, H ≤ pt s, honest awake       │
│                    │ D_s'                         │ proposer, pt s + max D_c D_s ≤     │
│                    │                              │ horizon                            │
└────────────────────┴──────────────────────────────┴────────────────────────────────────┘
```

Write each claim as a `def … : ClaimSpec ClaimDomain.v1 where` with all fields, as `includedConfirmed` in `Core.lean`. The `le` field is `decide (…)` of the conjunction in the table. The `le_trans` proof: `of_decide_eq_true` on both, then `decide_eq_true` of the combined facts (`le_trans`, `Eq.trans`, and for `full`: `fun h => hbc (hab h)` on `Bool` implications written as `(k.full = true → k'.full = true)`). `refutable := .family` for the three inclusion-carrying claims (`includedStable`, `includedStableFast`, `recovered`) and `.run` for the two persistence claims. The `le_trans` proofs and the `transport` proofs are named theorems (`<claim>_le_trans`, `<claim>_transport`) that the definition refers to (Global Constraints, lock stability).

The persistence triggers need `b₀ < b₁` (Review Focus 6; opus P1a-02). At `budget = 0` the regime forces `b₁ = b₀`, the window `[b₀, b₀)` is empty, and `holds` is true for every instance; without `b₀ < b₁` in the trigger, a healthy run would inhabit that vacuous claim. `valid` keeps `0 ≤ budget` (the bundle allows it, so `ac43_iff` stays true); only inhabitation changes.

`recovered`'s `RecoveredAt` reads `C.D_c` and `C.D_s` only, so write its conclusion with `{ zeroConstants with D_c := k.D_c, D_s := k.D_s }`, and its regime with `{ zeroConstants with θrec := k.θrec, recoveryFull := k.full, proposerGap := k.G, recoveryBound := k.ρ }`.

- [ ] **Step 3: Prove the `transport` fields and the Mono lemmas.** For each claim: from `holds` at `k` and a run in the regime at `k'`, show that the run is in the regime at `k` (Mono lemmas: `etaSleepy_mono`; `T + lag ≤ b₀` from `T + lag' ≤ b₀` and `lag ≤ lag'`; `b₁ − b₀ ≤ budget` from `≤ budget'` and `budget' ≤ budget`; `recurrence_mono`; `θrec` as `etaSleepy_mono`; `full`: the premise `k.full = true → …` follows from `k'.full = true → …`; `GST + ρ ≤ horizon` from `GST + ρ' ≤ horizon`), then map the conclusion (equal delays; `RecoveredAt` at `GST + ρ` gives it at `GST + ρ'` by `safeFrom_mono` and `includedFrom_mono`). The `θ` lower bound `0 ≤ θ` comes from `valid k`.

- [ ] **Step 4: Tests.** In `Standard.lean`, `example`s that the `le` of each claim has the design's direction, for example `example : persistOutage.le ⟨0, 1/2, 1, 5⟩ ⟨0, 1/2, 2, 4⟩ = true := by simp [persistOutage]` (lag ↑ and budget ↓ are weaker) and its reverse is `false`. `decide` does not reduce on `ℚ` (tested); use `simp [<claim>]`, with `norm_num` if needed.
  - `<claim>_trigger_late` for `includedStable`, `includedStableFast`, `persistOutage`, `persistOutageFast` and `recovered` (Global Constraints, late triggers).
  - Review Focus 6: `theorem persistOutage_no_witness_at_zero_budget (I : Instance) (k : OutageConst) (hk : k.budget = 0) : ¬ persistOutage.inhabited I k` (the regime gives `b₁ − b₀ ≤ 0`, the trigger gives `b₀ < b₁`).

- [ ] **Step 5: CHECKPOINT.** Build green. `CatalogLock --check` exits 0 with `ADDED` lines only. Run `--write` to record the additions. Registry unchanged. Commit `Framework: standard tier claims`, with `docs/catalog.lock`.

### Task 8: Strong tier claims

**Files:**
- Create: `AvailableChainFramework/Catalog/Strong.lean`
- Modify: `AvailableChainFramework.lean`, `AvailableChainRegistry/Tests/NewFacet.lean` (Step 3)

**Interfaces:**
- Consumes: Tasks 4, 7.
- Produces: `StrongIncConst`, `StrongRecConst`, `StrongRecIncConst`, and `strongSafe`, `strongIncluded`, `strongPersist`, `strongRecoveredSafe`, `strongRecoveredIncluded` (all `ClaimSpec ClaimDomain.strong`).

These restate the fields of `StrongClaims` (`Strong/Claims.lean`). The fault cap is weaker when it goes down (`faultCap ↓`, design §4). The regimes read `I.sface` and `I.toInstance`.

- [ ] **Step 1: Constants and claims.**

```text
┌─────────────────────────┬─────────────────────────────┬────────────────────────────────┐
│ Claim (id)              │ Const, valid, le            │ Point; regime; conclusion;     │
│                         │                             │ trigger                        │
├─────────────────────────┼─────────────────────────────┼────────────────────────────────┤
│ strongSafe              │ Nat f; True; le: f' ≤ f     │ Time t₀; SleepyRegime ∧        │
│ extra.strong.safe.v1    │                             │ FaultBound f; SafeFrom strong  │
│                         │                             │ t₀; True                       │
│ strongIncluded          │ StrongIncConst (f, D);      │ Time t₀; Sleepy ∧ FaultBound ∧ │
│ extra.strong.           │ 0 ≤ D; le: f' ≤ f, D = D'   │ FullParticipation;             │
│ included.v1             │                             │ IncludedFrom strong t₀ D;      │
│                         │                             │ inclusion trigger              │
│ strongPersist           │ Nat f; True; le: f' ≤ f     │ Time × Time (T, b₀);           │
│ extra.strong.persist.v1 │                             │ StrongArmedRegime f;           │
│                         │                             │ PersistsFrom strong T b₀;      │
│                         │                             │ H ≤ T ∧ a non-genesis honest   │
│                         │                             │ strong read at T               │
│ strongRecoveredSafe     │ StrongRecConst (f, θrec,    │ Unit; RecoveryRegime C(θrec,   │
│ extra.strong.           │ full, G, ρ); valid: True;   │ full, G, ρ) ∧ FaultBound f;    │
│ recoveredSafe.v1        │ le: f' ≤ f,                 │ SafeFrom strong (GST + ρ);     │
│                         │ θrec ≤ θrec', full → full', │ True                           │
│                         │ G' ≤ G, ρ ≤ ρ'              │                                │
│ strongRecoveredIncluded │ StrongRecIncConst (the      │ Unit; as strongRecoveredSafe;  │
│ extra.strong.           │ above and D); also 0 ≤ D;   │ IncludedFrom strong (GST + ρ)  │
│ recoveredIncluded.v1    │ le also D = D'              │ D; inclusion trigger after     │
│                         │                             │ GST + ρ                        │
└─────────────────────────┴─────────────────────────────┴────────────────────────────────┘
```

`strongRecoveredSafe` and `strongRecoveredIncluded` have `refutable := .run`, not `.family` (opus P1a-08): with `valid := True`, a constant with `θrec ≥ 1` is valid and makes the Recovery regime empty, so `holds` is vacuous there and no refutation family can exist; say this in their docstrings. The other strong claims: `strongSafe`, `strongPersist` `.run`; `strongIncluded` `.family`. Each claim with a trigger other than `True` gets `<claim>_trigger_late`, and its `le_trans` and `transport` proofs are named theorems. `strongPersist`'s window `[b₀, horizon]` is nonempty by `b₀ ≤ horizon` in the regime, so it needs no extra trigger condition.

`StrongClaims` has no `C.Valid` field (only `SC.Valid`), so the recovery constants of the strong claims have NO validity condition (`valid := True`, and `0 ≤ D` for the inclusion claim). Otherwise `strong1_iff` (Task 9) fails for a `C` that is not valid. The `transport` proofs do not need a sign of `θrec`: only the factor changes, and the card term is `≥ 0`. Record this in the file docstring.

- [ ] **Step 2: `transport` proofs**, as Task 7 Step 3; `FaultBound f'` gives `FaultBound f` for `f' ≤ f`.

- [ ] **Step 3: Test.** `refutedBadStrong` of Task 4 used a test claim. Add `refutedBadStrongSafe : RefutationFamily strongSafe badStrong` in `AvailableChainRegistry/Tests/NewFacet.lean`, with the same run (`FaultBound f` holds: no validator is faulty).

- [ ] **Step 4: CHECKPOINT.** Build green. Lock `--check` exits 0 with `ADDED` only; `--write`. Registry: one new `refutation-family` row. `Registry --check` exits 0 after the write. Commit `Framework: strong tier claims`.

### Task 9: Profiles `ac-4.3` and `strong-1`, and the equivalence theorems

**Files:**
- Create: `AvailableChainFramework/Catalog/Profiles.lean`
- Modify: `AvailableChainFramework.lean`

**Interfaces:**
- Consumes: Tasks 2, 7, 8.
- Produces: `ac43 : Profile ClaimDomain.v1` (`Shared := Constants`, `valid := Constants.Valid`), `strong1 : Profile ClaimDomain.strong` (`Shared := Constants × StrongConstants`, `valid := fun C => C.2.Valid`), `ac43_iff`, `strong1_iff`, `ac43_valid_cross`.

- [ ] **Step 1: The profiles.** `ac43.entries`: `safeConfirmed ↦ ()`, `safeStable ↦ ()`, `prefixOrder ↦ ()`, `includedConfirmed ↦ C.D_c`, `includedStable ↦ ⟨C.η, C.θ, C.D_s⟩`, `includedStableFast ↦ C.D_f`, `persistOutage ↦ ⟨C.η, C.θ, C.armingLag, C.budget⟩`, `persistOutageFast ↦ ⟨C.η, C.θ, C.fastArmingLag, C.budget⟩`, `recovered ↦ ⟨C.θrec, C.recoveryFull, C.proposerGap, C.recoveryBound, C.D_c, C.D_s⟩`. `strong1.entries`: the five strong claims with the projections of `(C, SC)` (`SC.faultCap`, `SC.strongDelay`, and the recovery fields of `C`).

- [ ] **Step 2: The equivalence theorems** (design §4: "the equivalence is between claim PROPOSITIONS").

```lean
/-- `ac-4.3` is today's bundle (design §4, profiles). -/
theorem ac43_iff (I : Instance) (C : Constants) :
    (∀ (W : Validators) (E : Env W.V), E.Δ = I.Δ → AvailableChain I.P E I.iface C) ↔
      ac43.holdsAt I C := by
  sorry

/-- `strong-1` is today's `StrongClaims`. -/
theorem strong1_iff (I : StrongInstance) (C : Constants) (SC : StrongConstants) :
    (∀ (W : Validators) (E : Env W.V), E.Δ = I.Δ → StrongClaims I.P E I.sface C SC) ↔
      strong1.holdsAt I (C, SC) := by
  sorry

/-- Review Focus 3: a cross-claim condition of `ac-4.3` is checked once, by
the profile. -/
theorem ac43_valid_cross (C : Constants) (h : ac43.valid C) :
    C.fastArmingLag ≤ C.armingLag := h.fastArmingLag_le
```

Proof guides: `ac43_iff` `→`: `C.Valid` needs one environment: use `Validators` `Fin 1` and the environment `⟨I.Δ, I.Δ_pos, 0, le_rfl, fun _ _ => true⟩` (this is why `Δ_pos` exists; Review Focus 5); each entry's `valid` follows from `C.Valid`; each `holds` is the bundle field. The regimes are NOT equal by `Iff.rfl`: a regime structure keeps its whole `Constants` argument, which is not defeq to `{ zeroConstants with … }` (tested by both audits). Write one adapter lemma per regime, `⟨fun h => { h with }, fun h => { h with }⟩`, in `Catalog/Mono.lean` (tested for StableSleepy, Outage, Recovery and RecoveredAt); `FastOutageRegime` also rebuilds its parent: `{ toOutageRegime := { h.toOutageRegime with }, highParticipation := h.highParticipation }` in both directions. `EtaSleepy` (a `def`) agrees by `Iff.rfl`. The bundle's `monotone` field comes from `SafeFrom.monotone` of the two safety claims. `←`: build `AvailableChain` field by field from the entries. Membership in the literal entry list: as in Task 2 Step 3 (`change … at he` to the literal list type, then `simp only [List.mem_cons, …]`), not `simp [ac43]`. `strong1_iff`: the same, with `SC.Valid` from the profile's `valid`.

- [ ] **Step 3: CHECKPOINT.** Build green. Lock `--check` exits 0 with `ADDED` only; `--write`. Commit `Framework: profiles ac-4.3 and strong-1 with equivalences`.

### Task 10: Documents and handoff

**Files:**
- Modify: `docs/MAP.md`, `docs/FRAMEWORK-DESIGN.md` (§8 row 0 note on (d), (g), (h); §12 I2 closed, I1 compiled), `docs/PHASE0-REPORT.md` (§6: a status column or a closing note per row that this plan closes)

- [ ] **Step 1: MAP.md.** Add rows for `ClaimDomain.lean`, `DomainMap.lean`, `Facets/Strong.lean`, `Catalog/{Mono,Standard,Strong,Profiles}.lean`, `Registry/Gaps/NoInput.lean`, and the new script modes (`CatalogLock --check` by name and `--lock`, `Registry --check`).
- [ ] **Step 2: Design and report notes.** In FRAMEWORK-DESIGN §8, below the table, add: "(d) superseded by claim domains (plan 1a); (g), (h) delivered (plan 1a); (i) kept." In §12: I2 is closed (late triggers, Task 1); I1 is compiled (`Gaps/NoInput.lean`) and stays open until plan 2. In PHASE0-REPORT §6, mark the rows that this plan closes: Facet, Registry (row kind, `--check`, library list), Lock (I8, M5, M6), Core I1 (compiled, open), Claim I2 (closed), Phase 1 gate (done). Leave the rows for plan 1b open (GridCO excludes, model facts, Engine lemmas, Kit structure, E5/E6).
- [ ] **Step 2a: Known gap I9, root collisions** (async finding, 2026-09-28; the label I3 is taken by the carrier generalization). Add to design §12 "Known gaps" and to PHASE0-REPORT §6: "I9 (reasoned; a `decide` check in the async session's scratch): every regime has the premise `RootInjective` (`Generic/Conditions.lean:28`), but the honest root formula `s * (parent.root + 1)` (Grid CO `Model/Protocol.lean:291`; SA, SA-PC `Choice.lean:87` and L* `Protocol.lean:258` reuse this form) collides on forks: slot 4 on genesis and slot 2 on the slot-1 block both get root 4; and a faulty slot-7 block with root 7 gives its honest slot-8 child root 64, the root of the honest slot-4 block on the chain 1, 4, 15, 64. So an adversary can leave every regime, and the certificates give no guarantee against a forged collision. The theorems stay sound. Fix (a design decision for the user, with a proper audit; it changes the protocol libraries): content-coded roots checked at admission (FG-SA plan D4), so that `RootInjective` follows from admission. Not in plans 1a, 1b or 2 until decided." Plan 1a does not change a protocol library for it.
- [ ] **Step 2b: "As implemented" notes** (async m12). Under design §3, §4 and §5, add dated notes "As implemented in plan 1a (2026-09-28)": `ClaimDomain` in place of `needs`/`FacetBundle`; facet structures; `Instance` closed, eligibility as `Eligible I` (plan 1b); `Δ_pos`; the late trigger; `Profile.Shared`. These are notes; the approved text does not change.
- [ ] **Step 3: Full build at handoff.** `pgrep -fl lean`; then `lake build --wfail` (every default target). `lake env lean --run scripts/CatalogLock.lean --check` exits 0. `lake env lean --run scripts/Registry.lean --check` exits 0. `lake env lean --run scripts/CheckFrameworkAxioms.lean` exits 0. `grep -rnE 'sorry|admit|native_decide|^axiom' AvailableChainFramework AvailableChainRegistry scripts/CatalogLock.lean scripts/Registry.lean scripts/CheckFrameworkAxioms.lean` finds no tactic use and no axiom (identifiers such as `admitVote` are expected).
- [ ] **Step 4: CHECKPOINT.** Commit `Framework: plan 1a documents`. Write the plan report (controller): tasks, commits, rulings, checks, and the inputs for plan 1b.

## Audit disposition

```text
┌──────────────────────────┬──────────────────────────────────────────────────────┐
│ Finding                  │ Disposition                                          │
├──────────────────────────┼──────────────────────────────────────────────────────┤
│ Astra A01 (prefix)       │ Task 1 Step 5: prefixOrder stays unconditional       │
│ Astra A02 (hash order)   │ Task 0 Step 1, test (d)                              │
│ Astra A03, opus 12,      │ Task 0 Step 2: generated by metadata; claims always  │
│ async m11 (skip list)    │ locked                                               │
│ Astra A04, async M3      │ Task 0 Steps 3, 6b; CheckFrameworkAxioms everywhere  │
│ Astra A05, async M1      │ Rulings (I1, KNOWN-GAP contract); Task 5 intro and   │
│                          │ docstring; scope table row 2                         │
│ Astra A06, opus 04,      │ Task 1 Steps 1, 4 (imports)                          │
│ async m1                 │                                                      │
│ Astra A07, opus 01,      │ Rulings: Instance closed; Eligible I (plan 1b)       │
│ async M4                 │                                                      │
│ Astra A08, opus 15,      │ Task 0 Step 6; Task 6 Step 1 (last argument)         │
│ async m8                 │                                                      │
│ opus 02, async M5        │ Task 7 triggers b₀ < b₁; Review Focus 6              │
│ opus 03, async m3        │ Task 9 adapters                                      │
│ opus 05, async m2        │ Task 2 Step 3; Task 5 typed numerals                 │
│ opus 06                  │ Task 1 Step 6 binders                                │
│ opus 07                  │ Task 7 Step 4 (simp)                                 │
│ opus 08                  │ Task 8: refutable .run for strong recovered claims   │
│ opus 09                  │ Global Constraints: <claim>_trigger_late             │
│ opus 10, async M6        │ Rulings: DomainMap for facets only; id rule; plan 2  │
│                          │ one-way lift; optional pointwise transport declined  │
│ opus 11 (generic Σ facet │ DECLINED for now: one structure per facet is enough  │
│ domain)                  │ for strong and FG; ClaimDomain.ofV1 removes the      │
│                          │ repetition (async m5)                                │
│ opus 13, async M2        │ Task 0 before the gate; per-task lock diff; meaning  │
│                          │ pins (Task 1 Step 6b); old lock blob id              │
│ opus 14, async m10       │ Global Constraints: named transport theorems         │
│ opus 16                  │ Task 5: clock := max                                 │
│ async m4, m6             │ Rename to ClaimDomain/DomainMap; `id` field          │
│ async m5                 │ Task 4 Step 1b: ClaimDomain.ofV1                     │
│ async m7                 │ KNOWN-GAP in Task 0; REGISTRY.md committed when it   │
│                          │ changes                                              │
│ async m9                 │ Task 0 Step 6b: id uniqueness                        │
│ async m12                │ Task 10 Step 2b                                      │
└──────────────────────────┴──────────────────────────────────────────────────────┘
```
