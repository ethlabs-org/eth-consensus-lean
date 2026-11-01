# Phase 0 report — protocol framework prototype

_Written for the Phase 1–2 plan. Scope: `AvailableChainFramework` and
`AvailableChainRegistry` (`docs/FRAMEWORK-DESIGN.md` v7, §8, row P = 0).
Task references (Task 1–9) point to the per-task `git log` commits
(`Framework: …`) that built this scope; the plan is
`docs/plans/2026-09-28-framework-phase0.md`._

## 1. Purpose

Phase 0 built a compiled prototype of the protocol framework design
(`docs/FRAMEWORK-DESIGN.md` §§1–7) on the v1 engine, to test the design's
interfaces with the Lean compiler before Phase 1 commits to the full v1
catalog. It added two Lake libraries: `AvailableChainFramework` (the
catalog and certificate framework, L1–L3 and a kit) and
`AvailableChainRegistry` (protocol instances with certificates and
refutations over the framework, L4). `docs/MAP.md` has the module map
for both libraries.

## 2. Headline results

```text
┌────────────────────────┬─────────────────────────────────────────────────┐
│ Result                 │ Detail                                          │
├────────────────────────┼─────────────────────────────────────────────────┤
│ Full build             │ lake build --wfail: 3555 jobs, green (no new    │
│                        │ failures).                                      │
│ No sorry/admit/        │ grep clean; the only matches are the            │
│ native_decide          │ identifiers admitVote and admitProposal.        │
│ Sanity                 │ Candidate sanity to False: the core floor       │
│                        │ refutes it (includedConfirmed has no valid D).  │
│ Counter                │ candidate : Candidate counterInst: the core     │
│                        │ floor holds, including includedConfirmed at D = │
│                        │ 1.                                              │
│ catalog.lock           │ lake env lean --run scripts/CatalogLock.lean    │
│                        │ --check: exit 0.                                │
│ REGISTRY.md            │ regenerated; unchanged (7 certs: 3 Sanity + 4   │
│                        │ Counter; 1 refutation-family; 8 rows total).    │
└────────────────────────┴─────────────────────────────────────────────────┘
```

Sanity fails the core floor exactly as the design predicts: it always
returns genesis and permanently excludes every object, so
`includedConfirmed` has no valid delay `D` (`Sanity.refutedIncluded`,
a `RefutationFamily`). Counter, a new toy height protocol built for
Phase 0, passes the core floor, including exact-time inclusion at
`D = 1` (`Counter.candidate : Candidate counterInst`).

## 3. What each interface showed

**Validators bundling.** Phase 0 bundles a run's validator type with its
`DecidableEq` and `Fintype` instances into one structure, `Validators`.
This is a Phase 0 implementation choice: design §3's `Instance` sketch
does not mention it. A claim's `regime` and `conclusion` fields quantify
over `W : Validators`, not over a bare type with separate instance
arguments. Every certificate (Sanity, Counter, the Pareto test) builds
one `Validators` value (for example `⟨Fin 1, inferInstance,
inferInstance⟩`) and both fields consume it as a single argument. Phase
0 used only one validator type per instance, so the bundling did not
need to carry a value across a "widen the electorate" transport; that
case is untested.

**Point.** `Point` holds a claim's own run parameters, apart from its
constant. `safeOf`-built claims (`safeConfirmed`, `safeStable`) and
`includedConfirmed` all use `Time` as `Point`, for the Sleepy regime's
start time `t₀` (`Catalog/Core.lean:25,70`), not a read time or a
proposal slot. `prefixOrder` uses `Unit`, for no free parameter. The
three claims share one `ClaimSpec` shape with no change to
`Claim.lean`, which is the point of the field: `Point` lets a claim's
own witness shape vary without a change to the catalog's record type.

**Type-class facets.** Deviation (d) drops `ClaimSpec.needs` as a
field. Task 6 adds a facet, `HasStrong`, as a plain Lean type class
over `Instance` (`class HasStrong (I : Instance) where strong : …`).
It compiled with no change to `Instance`, `ClaimSpec`, or any existing
declaration: a new facet is an addition, as the design predicts.

`safeStrong` is a `Prop`, not a `ClaimSpec`; the test shows only that a
facet class compiles, not that the catalog can state a claim that needs
one. `ClaimSpec` cannot yet state a claim that needs a facet
(strong-1): `regime`, `conclusion`, and `trigger` take only `I :
Instance`, and `Const` and `Point` do not depend on `I`. A type-class
facet also lets two instances attach to one `I`, which breaks "bound
once" (§3). Fix planned: Phase 1 carrier generalization. See also the
Facet row of §6, Open items, for the shape's vacuity issue.

**Cert as data.** `Cert c I` is a structure, not a bare proof term: it
carries `const`, `valid`, `inhabited`, and `proof` as fields.
`scripts/Registry.lean` finds every certificate by scanning constant
TYPES (`Cert c I`, `Refutation c I`, `RefutationFamily c I`), not by
reading `@[cert]`/`@[refutes]` attributes (deviation (a)). `Cert.weaken`
builds a new `Cert` value at a weaker constant from an old one's
`proof` field, through `ClaimSpec.transport`, with no re-proof. The
registry lists seven certificates (3 Sanity, 4 Counter) and one
refutation-family over Sanity and Counter, 8 rows total;
`Candidate`/`ProfileCert` values are not rows, because
their type is a `Pi`-type over `c ∈ p.claims`, not `Cert c I` itself
(Open items, §6).

**Type 1.** `ClaimSpec` has two `Type`-valued fields, `Const` and
`Point`. A structure with a `Type`-valued field is itself one universe
higher than an ordinary data structure, so `ClaimSpec : Type 1`.
`ProfileCert` and `Catalog.Candidate` quantify over a `List ClaimSpec`,
so both widen from the plan's `Type` to `Type 1` (deviation (f)). This
is a plan defect only: the universe is forced by `ClaimSpec`'s shape,
not by a proof gap, and no other declaration changed to accommodate
it.

## 4. The Grid CO Step 1 finding

Task 7 tested the design's E4 (permanent exclude) classification
against a Grid CO variant, `gridCOx`, whose only change from `gridCO`
is its `excludes` function. Step 1 asked whether the
equivocation-exclusion disjunct could be dropped from `excludes`: kept
only if some clock evaluation removes a vote, dropped otherwise. The
proof (`clock_votes`, `AvailableChainRegistry/GridCOHooks.lean`)
established that no clock evaluation — `expire`, `freeze`, the early
save, `release`, or `gate` — writes `st.votes`. Only `admitVote`
(called from `process`, never from `clock`) appends to it. Every clock
step reads or replays existing votes; none removes one.

The finding keeps the equivocation-exclusion disjunct in
`gridExcludes`: an already-equivocating seat stays excluded until the
epoch ends, because nothing in `clock` would ever revoke that
exclusion. `Deliverable`, `RelayFeasible`, and `WindowMargin` for Grid
CO move to Phase 1, with the `excludes` change in `gridCO` itself
(deviation (b)).

Note (2026-09-29, plan 1b). Plan 1b Task 1 (`05cec33`) removed
`gridCOx`, `gridExcludes`, `gridCOx_hooks` and `engineClockx`.
`gridCO` itself now has `excludes`
(`AvailableChainGridCO/Model/Protocol.lean`), with the equivocation
clause. `clock_votes` and the other hook facts are in
`AvailableChainGridCO/Proofs/Hooks.lean`. The Registry file moved to
`AvailableChainRegistry/Instances/GridCOHooks.lean`, and it now has only
`gridHooks : HooksSound (gridCO p)`. WindowMargin is
`AvailableChainGridCO/Proofs/WindowMargin.lean`. `Deliverable` and
`RelayFeasible` are plan 1c.

## 5. Deviations from the plan

### 5.1 Design deviations (accepted by the user, 2026-09-28)

```text
┌─────┬────────────────────────┬──────────────────────────────────────────────┐
│ #   │ Deviation              │ Reason                                       │
├─────┼────────────────────────┼──────────────────────────────────────────────┤
│ a   │ Registry: type scan    │ A type-scanning script replaces checked      │
│     │                        │ attributes (@[cert], @[refutes]). A constant │
│     │                        │ is a certificate or a refutation by its type │
│     │                        │ (Cert c I, Refutation c I, RefutationFamily  │
│     │                        │ c I); no metaprogramming in module files.    │
│ b   │ Grid CO: E4 only       │ HooksSound is checked for a Grid CO variant  │
│     │                        │ (gridCOx) with the new excludes.             │
│     │                        │ Deliverable, RelayFeasible, and WindowMargin │
│     │                        │ move to Phase 1, with the excludes change in │
│     │                        │ gridCO itself.                               │
│     │                        │ Plan 1b (2026-09-29): gridCOx is removed.    │
│     │                        │ The excludes change is in gridCO itself, and │
│     │                        │ HooksSound (gridCO p) is gridHooks (Task 1,  │
│     │                        │ 05cec33). WindowMargin is the Grid CO module │
│     │                        │ Proofs/WindowMargin.lean. Deliverable and    │
│     │                        │ RelayFeasible: plan 1c.                      │
│ c   │ Run ext.: genesis      │ The run-extension theorem is proved from     │
│     │                        │ genesis (the Counter canonical run, every    │
│     │                        │ horizon, Sleepy from 0). The general form,   │
│     │                        │ from every valid prefix, is Kit.Engine in    │
│     │                        │ Phase 1.                                     │
│ d   │ Facets: type class     │ ClaimSpec.needs is not a field. A facet is a │
│     │                        │ type class over Instance (Tests/NewFacet).   │
│     │                        │ The v1 Interface is the one field facet      │
│     │                        │ every Phase 0 instance carries.              │
│ e   │ Lock: statement only   │ A locked theorem hashes its statement (type) │
│     │                        │ only, not its proof (value), so a new proof  │
│     │                        │ of the same statement keeps the hash. Fixes  │
│     │                        │ a draft defect found in Task 6 review.       │
│ f   │ Candidate: Type 1      │ ClaimSpec has Type-valued fields (Const,     │
│     │                        │ Point), so ClaimSpec : Type 1. ProfileCert   │
│     │                        │ and Catalog.Candidate widen from Type to     │
│     │                        │ Type 1. A plan defect forced by ClaimSpec's  │
│     │                        │ shape, not a proof gap.                      │
│ g   │ Constants: not         │ Shared constants (ProtocolParams, extensible │
│     │ delivered              │ constant records, §§3, 8 row 0) are not      │
│     │                        │ delivered; `Profile` has no shared constants.│
│     │                        │ Needed by ac-4.3 (`Constants`) and strong-1  │
│     │                        │ (`Constants × StrongConstants`). Phase 1 gate│
│     │                        │ task.                                        │
│ h   │ HooksSound: no         │ `HooksSound` lacks the E4 `depsPresent`      │
│     │ depsPresent            │ monotonicity field. Phase 1 gate task, added │
│     │                        │ together with the other lock-breaking        │
│     │                        │ changes.                                     │
│ i   │ HooksSound: run-level  │ `HooksSound` states stability along well-    │
│     │                        │ formed runs, not per step as E4 does. Reason:│
│     │                        │ see its docstring.                           │
└─────┴────────────────────────┴──────────────────────────────────────────────┘
```

Deviations (a)–(d) were accepted with the plan, before implementation
(`docs/plans/2026-09-28-framework-phase0.md`, "Deviations from the
spec"). Deviations (e) and (f) surfaced during implementation and
review (Task 6, Task 1–3) and are recorded here for the first time.
Deviations (g)–(i) surfaced during the final whole-branch review and
are recorded here for the first time. Deviations (e)–(i) are recorded
in `docs/FRAMEWORK-DESIGN.md` §8.

### 5.2 Proof-level deviations (no statement changed)

Every statement (`def`, `structure`, `theorem` type) in the framework
and registry matches its brief exactly. The changes below are to proof
scripts, tactics, or witness terms only.

```text
┌────────┬────────────────────────────────────────────────────────────────┐
│ Task   │ Deviation (proof only; no statement changed)                   │
├────────┼────────────────────────────────────────────────────────────────┤
│ 4      │ The Time abbreviation does not unfold for omega across modules │
│        │ in this toolchain. horizon_ge is proved with order lemmas and  │
│        │ linarith instead. A bare numeral 0 does not resolve OfNat      │
│        │ includedConfirmed.Point 0 by instance search; the call uses an │
│        │ explicit (0 : Time).                                           │
│ 5      │ pareto_covers's sorry is replaced by a strong-induction proof. │
│        │ Three new public helper lemmas are needed (stronger_irrefl,    │
│        │ stronger_trans, stronger_count_lt) and stay public, because    │
│        │ pareto_covers needs them (Task 5 controller ruling).           │
│ 6      │ The registry scan is filtered to the AvailableChainRegistry    │
│        │ module prefix; without it, framework declarations whose type   │
│        │ ends in Cert/RefutationFamily (for example Cert.mk,            │
│        │ Cert.weaken) appear as false CONDITIONAL rows. Lock coverage   │
│        │ moved from name-prefix roots to by-module selection, fixing    │
│        │ review finding I1 (Refutation, RefutationFamily,               │
│        │ RefutationKind, Profile, ProfileCert, Validators, Outcome, and │
│        │ classify were missing). An unreadable or missing lock file on  │
│        │ --check exits 2, not 1.                                        │
│ 7      │ gridExcludes_inert and gridCOx_hooks are proved in full (see   │
│        │ the Grid CO Step 1 finding). linter.unusedSectionVars is       │
│        │ disabled file-wide, matching the existing Grid CO idiom for    │
│        │ the [LeasePolicy] section variable.                            │
│        │ Plan 1b (2026-09-29): gridExcludes_inert and gridCOx_hooks are │
│        │ removed with gridCOx (Task 1, 05cec33). gridHooks, over the    │
│        │ hook facts in AvailableChainGridCO/Proofs/Hooks.lean, replaces │
│        │ them.                                                          │
│ 8      │ toyV2's process_base witness uses Nat.max, not max: instance   │
│        │ search for Max toyV2.Base runs before the toyV2.Base           │
│        │ projection unfolds to Nat, and fails. output_tick uses the     │
│        │ brief's named fallback helper, foldl_recordOwn_base, because   │
│        │ the direct rewrite-then-induction proof leaves an unmatched    │
│        │ wrapper term.                                                  │
│ 9      │ counter.slotsAt_spec reuses alwaysGenesis.slotsAt_spec's proof │
│        │ (the same Time/omega quirk as Task 4). counter_safe uses a     │
│        │ sublist argument through readAt_mono, not stateBefore_mono     │
│        │ directly, because counter_safe quantifies over every run and   │
│        │ Run.readAt is a filter of events, not a prefix. candidate is   │
│        │ noncomputable: hc : c ∈ core.claims is an Or, which cannot     │
│        │ eliminate into Type, so it selects the certificate by a        │
│        │ classical case split on c = …; no new axiom.                   │
└────────┴────────────────────────────────────────────────────────────────┘
```

## 6. Open items for the Phase 1–2 plan

Status after plan 1a (2026-09-28): a row that plan 1a closes or changes
ends with a note "Plan 1a: …". The rows for plan 1b stay open. The last
row (I9) is new.

Status after plan 1b (2026-09-29): a row that plan 1b closes or changes
ends with a note "Plan 1b: …". The row E4 is new.

Status after plan I9 (2026-09-29): the row Roots ends with a note
"Plan I9: …".

```text
┌───────────┬────────────────────────────────────────────────────────────┐
│ Area      │ Open item                                                  │
├───────────┼────────────────────────────────────────────────────────────┤
│ Facet     │ A naive claim of the form ∀ (I : Instance) [HasStrong I],  │
│           │ … is vacuous for an instance without HasStrong I: there is │
│           │ no instance to supply, so the universal statement holds    │
│           │ trivially. Phase 1 needs an encoding for a facet-needing   │
│           │ claim that tells 'does not have the facet' apart from      │
│           │ 'holds trivially'. Facet-needing claims do not enter the   │
│           │ catalog in Phase 0 (Task 6 ruling I2).                     │
│           │ Plan 1a: CLOSED. Task 4 (`99ffe0e`): a facet is a          │
│           │ structure that extends Instance, with its own claim domain │
│           │ (Facets/Strong.lean). An Instance without the facet has no │
│           │ such claim, and Tests/NewFacet refutes a test claim on the │
│           │ strong output for badStrong.                               │
│ GridCO    │ processed and excludes can both hold for the same object   │
│           │ (the old-label clause of excludes does not check processed │
│           │ first). Must the two stay disjoint under the Phase 1       │
│           │ excludes change?                                           │
│           │ Plan 1a: open (plan 1b, with the Grid CO excludes change). │
│           │ Plan 1b: CLOSED. Task 1 (05cec33): yes, they stay          │
│           │ disjoint. excludes tests o ∉ st.votes before both clauses, │
│           │ and excludes_not_processed                                 │
│           │ (AvailableChainGridCO/Proofs/Hooks.lean) holds for every   │
│           │ state, so for every state of a run.                        │
│ GridCO    │ Grid CO model facts (gate_votes, clock_votes,              │
│           │ engineClockx) are public in the Registry namespace. Move   │
│           │ them with the Phase 1 excludes change.                     │
│           │ Plan 1a: open (plan 1b).                                   │
│           │ Plan 1b: CLOSED. Task 1 (05cec33): gate_votes,             │
│           │ clock_votes, process_votes_subset and                      │
│           │ process_blocks_subset are in                               │
│           │ AvailableChainGridCO/Proofs/Hooks.lean (namespace          │
│           │ AvailableChain.GridCO). engineClockx is removed with       │
│           │ gridCOx.                                                   │
│ Engine    │ stateBefore_stable (GridCOHooks.lean) and the run/step     │
│           │ lemmas in Registry.Counter (Counter.lean, CounterRun.lean) │
│           │ are engine-generic, for any ProtocolSpec, but live in L4.  │
│           │ Move them into Kit.Engine in Phase 1.                      │
│           │ Plan 1a: open (plan 1b).                                   │
│           │ Plan 1b: IN PART. Task 0 (c79b473): stateBefore_stable     │
│           │ moved to AvailableChainKit/Engine/Stable.lean, as          │
│           │ AvailableChain.Engine.stateBefore_stable. The Counter run  │
│           │ and step helpers stay open for plan 1c, whose              │
│           │ run-extension work generalizes them (Astra P1b-07).        │
│ Registry  │ Candidate and ProfileCert values (sanity's refutation      │
│           │ path, counterInst's candidate) are not rows of             │
│           │ REGISTRY.md: their type is a Pi-type over c ∈ p.claims,    │
│           │ not Cert c I itself. Add a row kind for them.              │
│           │ Plan 1a: CLOSED. Task 6 (`2f7a53c`, `0b8ea16`): the row    │
│           │ kind profile-cert for ProfileCert p I and Candidate I; the │
│           │ claim column shows the profile id.                         │
│ Registry  │ scripts/Registry.lean does not check axioms (a paper claim │
│           │ vs. a LEAN-checked one). Task 6 M4: add an axiom check,    │
│           │ matching AvailableChainSAPC/Tests/Axioms.lean's pattern.   │
│           │ Closed before plan 1a (`87e95f8`, I7): the status LEAN or  │
│           │ UNSOUND. Plan 1a Task 0 adds                               │
│           │ scripts/CheckFrameworkAxioms.lean for every constant of    │
│           │ both libraries.                                            │
│ Registry  │ The include-only module-prefix filter                      │
│           │ (AvailableChainRegistry) drops a future instance library   │
│           │ silently if it is not under that prefix (Task 6 M1).       │
│           │ Syntactic certificate detection also misses aliases,       │
│           │ bundles, and private certs (Task 6 M2). The Claim column   │
│           │ shows a claim's def head, not a stable claim id (Task 6    │
│           │ M3).                                                       │
│           │ Plan 1a: M1 CLOSED. Task 0 (`426009e`): instanceLibraries  │
│           │ lists the scanned libraries, and the file header names     │
│           │ them. M2 and M3 stay open.                                 │
│ Lock      │ Generated names (eq_N, mk.inj, sizeOf_spec) appear as      │
│           │ locked lines. A toolchain change, or a new declaration     │
│           │ that triggers more equation lemmas under a locked prefix,  │
│           │ can break --check with no statement change (Task 6 M6).    │
│           │ The lock does not fail on an axiomInfo or a missing body   │
│           │ (M5); a per-line hash inside a cycle is incomplete for     │
│           │ future per-declaration cert hashes (M7); Expr.hash ignores │
│           │ binder info, and --check needs a build first, to read      │
│           │ oleans (M8).                                               │
│           │ Plan 1a: M5, M6 CLOSED. Task 0 (`426009e`, `6b7155a`):     │
│           │ environment metadata, not a name suffix, identifies a      │
│           │ generated name, and a generated name has no line; a bad    │
│           │ axiom or a missing declaration exits 2. M7 is also closed: │
│           │ each line hashes its full closure, with no memo. M8 stays  │
│           │ open.                                                      │
│ Sanity    │ Time is abbrev Time := Int in                              │
│           │ AvailableChainModel/Objects/Time.lean, not '@[reducible,   │
│           │ expose] def' as an earlier report said (Task 4 report      │
│           │ nit).                                                      │
│ Style     │ stronger_count_lt's docstring and stronger_trans's proof   │
│           │ (Pareto.lean) are dense for ASD-STE100 (Task 5). Two in-   │
│           │ file deviation comments in Engine/V2Sketch.lean are dense  │
│           │ for ASD-STE100 (Task 8). emittedAt_eq (CounterRun.lean)    │
│           │ ends its proof with simp, then rfl; simp alone may be      │
│           │ fragile to a future definitional change (Task 9).          │
│ E5/E6     │ toyV2.clock is a no-op, so Isolated's clock_base law is    │
│           │ never exercised by toyV2 (the plan-mandated toy). A future │
│           │ toy, or Phase 2's real engine v2, should exercise it.      │
│           │ Plan 1a: open (plan 2).                                    │
│ Core      │ A protocol that reads no input can still pass the core     │
│           │ floor. Honest `propose` has no input, so honest proposals  │
│           │ are predictable; e.g. a Sanity-shaped engine with `excludes│
│           │ := true` certifies all four core claims at D = 0 (reasoned,│
│           │ not compiled, I1). Fix: engine v2 gives the proposer a run-│
│           │ chosen input (Phase 2); the explorer (Phase 3) stays off   │
│           │ until closed.                                              │
│           │ Plan 1a: COMPILED, still OPEN. Task 5 (`3c76e2b`):         │
│           │ Gaps/NoInput.lean; clockCandidate passes the core floor at │
│           │ D = 0; its rows have the status KNOWN-GAP. Plan 2 fixes    │
│           │ it. A run input alone is not enough (Astra A05). Plan 2    │
│           │ also needs a floor claim that binds the proposal to the    │
│           │ input, and a refutation of clockChain as its regression    │
│           │ test.                                                      │
│ Claim     │ `Claim.inhabited` (`Claim.lean:58-60`) accepts one early   │
│           │ trigger for all H (`CounterIncluded.lean:228` uses slot 1  │
│           │ for all H, I2). Fix: require the trigger at a time ≥ H.    │
│           │ Changes the L3 lock and two certificates.                  │
│           │ Plan 1a: CLOSED. Task 1 (`0e6898e`): the trigger at a time │
│           │ ≥ H; includedConfirmed_trigger_late; the Counter           │
│           │ certificate certIncluded uses a slot at a time ≥ H.        │
│ Phase 1   │ Gating task (one lock regeneration, before any new catalog │
│           │ entry): carrier generalization for facets and engine (I3,  │
│           │ I5 — claim types are engine-v1 specific: `Instance.P :     │
│           │ ProtocolSpec I.n`, `Run W.V I.P`); shared constants (g);   │
│           │ late trigger (I2); depsPresent (h). Sketch for ac-4.3:     │
│           │ `Profile` gains `Shared : Type` and `share : ∀ c ∈ claims, │
│           │ Shared → c.Const`; `ProfileCert p I := Σ C : p.Shared, ∀ c │
│           │ h, {x : Cert c I // x.const = p.share c h C}`.             │
│           │ Plan 1a: DONE. Claim domains (Tasks 1, 4), shared          │
│           │ constants (Task 2), late trigger (Task 1), deps_stable     │
│           │ (Task 3), one lock regeneration (Task 6, `2f7a53c`).       │
│ Lock      │ Hardening: I8, the lock compares by name (exit 1 on a      │
│           │ changed or removed line, exit 0 with a notice on additions │
│           │ only; test by adding a Catalog claim); a `--check` mode for│
│           │ REGISTRY.md; deferred M5–M8.                               │
│           │ Plan 1a: I8 CLOSED (Task 0; tested by three scratch runs   │
│           │ in Task 6). Registry --check CLOSED (Task 0). M5, M6, M7:  │
│           │ see the Lock row above. M8 stays open.                     │
│ Kit       │ Structure: split L5 Kit and the L0 sketch into their own   │
│           │ library. `Kit.Engine` takes the                            │
│           │ `AvailableChain.Engine` lemmas from                        │
│           │ `AvailableChainGridCO/Proofs/{Execution,EngineClock}.lean` │
│           │ and the stranded L4 lemmas. Dedupe `block_preceq_trans`    │
│           │ (`Kit/Core.lean:13` and `GridCO/Proofs/Map.lean:25`).      │
│           │ Plan 1a: open (plan 1b).                                   │
│           │ Plan 1b: CLOSED, except the stranded L4 lemmas: see the    │
│           │ Engine row (plan 1c). Task 0 (c79b473): library            │
│           │ AvailableChainKit (L5: Core, Engine/*) and library         │
│           │ AvailableChainEngineV2 (L0: Sketch); the                   │
│           │ AvailableChain.Engine lemmas are in                        │
│           │ AvailableChainKit/Engine/. No dedupe (ruling): the Kit     │
│           │ block_preceq_trans and the private one in Map.lean have    │
│           │ different statements, and both stay.                       │
│ Roots     │ I9 (reasoned; a `decide` check in the async session's      │
│           │ scratch): every regime has the premise `RootInjective`     │
│           │ (`Generic/Conditions.lean:28`), but the honest root        │
│           │ formula `s * (parent.root + 1)` (Grid CO                   │
│           │ `Model/Protocol.lean:291`; SA, SA-PC `Choice.lean:87` and  │
│           │ L* `Protocol.lean:258` reuse this form) collides on forks: │
│           │ slot 4 on genesis and slot 2 on the slot-1 block both get  │
│           │ root 4; and a faulty slot-7 block with root 7 gives its    │
│           │ honest slot-8 child root 64, the root of the honest slot-4 │
│           │ block on the chain 1, 4, 15, 64. So an adversary can leave │
│           │ every regime, and the certificates give no guarantee       │
│           │ against a forged collision. The theorems stay sound. Fix   │
│           │ (a design decision for the user, with a proper audit; it   │
│           │ changes the protocol libraries): content-coded roots       │
│           │ checked at admission (FG-SA plan D4), so that              │
│           │ `RootInjective` follows from admission. Not in plans 1a,   │
│           │ 1b or 2 until decided.                                     │
│           │ Plan 1b: DECIDED 2026-09-29 (user), not in plan 1b: a      │
│           │ derived root root(B) := H(content) with H injective; a     │
│           │ block carries its parent root, and the store accepts a     │
│           │ block only when it knows a parent with the carried root    │
│           │ (dependency lookup). It is a contract and lock break, with │
│           │ its own plan and a full audit after plan 1b                │
│           │ (FRAMEWORK-DESIGN.md §12 I9). Point 2 (2026-09-29, user,   │
│           │ via DC-simplify): the parent-root check is the store       │
│           │ dependency lookup (depsPresent/blockKnown): a block claims │
│           │ no root of its own, and an unknown parent root is a        │
│           │ temporary missing dependency. So excludes gets no clause,  │
│           │ SA-PC keeps its rfl, and wire validity has no root check.  │
│           │ Wire forwarding rules wait for a P2P spec discussion.      │
│           │ Plan I9: CLOSED (2026-09-29). Roots are derived from       │
│           │ content (nodeRoot, epair). Block.root_injective holds for  │
│           │ every block, so RootInjective is a theorem                 │
│           │ (rootInjective_all). The honest formula is removed; honest │
│           │ proposers use body 0 (FG-SA: packBody 0 rows). The regime  │
│           │ fields stay, filled by rootInjective_all; their removal is │
│           │ a later plan (plan I9 D6). Open: a root-only wire          │
│           │ refinement, and the relay feasibility question (plan 1c).  │
│           │ See FRAMEWORK-DESIGN.md §12 I9.                            │
│ E4        │ New after plan 1a. Plan 1b: Grid CO, SA, SA-PC and L* each │
│           │ have an E4 excludes and the five hook facts, in their own  │
│           │ library. Grid CO and SA: two permanent HEAD refusals (an   │
│           │ old label; a third equivocation), Task 1. L*: the third    │
│           │ equivocation and a proposal wire whose block is already    │
│           │ stored, Task 2 (41750af). SA-PC: no permanent refusal, so  │
│           │ excludes stays false, Task 3 (22e29b7). Deliverable,       │
│           │ RelayFeasible, Eligible and the run-extension theorem:     │
│           │ plan 1c.                                                   │
└───────────┴────────────────────────────────────────────────────────────┘
```

## 7. Checks run for this report

- `lake build --wfail` (all default targets): `Build completed
  successfully (3555 jobs)`.
- `grep -rn 'sorry\|admit\|native_decide' AvailableChainFramework
  AvailableChainRegistry scripts`: every match is the identifier
  `admitVote` or `admitProposal` (Grid CO's vote-admission functions);
  no tactic use.
- `lake env lean --run scripts/CatalogLock.lean --check`: exit `0`.
- `lake env lean --run scripts/Registry.lean`: `docs/REGISTRY.md`
  regenerated, unchanged from the version Task 9 left.
