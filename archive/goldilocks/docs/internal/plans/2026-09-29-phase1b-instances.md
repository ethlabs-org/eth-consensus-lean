# Phase 1b: E4 exclusion, protocol instances, Kit split — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make Grid CO, SA, SA-PC and L* framework instances with proved hooks, give Grid CO (and SA) the E4 permanent exclusion that design §2 requires, prove the `ac-4.3` and `strong-1` propositions for every protocol that has a contract proof, move the engine-generic lemmas into their own Kit library, and generate `MATRIX.md`.

**Architecture:** The contract (`AvailableChainStatements`) does not change. Grid CO's `excludes` becomes the exact set of permanent HEAD refusals of `admitVote`; relay lemmas that used `excludes = false` get an explicit premise "not excluded at any time up to the cutoff", and one WindowMargin module per protocol discharges it. Hook facts are proved in each protocol library; the Registry assembles `HooksSound`, `Instance` and `StrongInstance` values and the `holdsAt` theorems through `ac43_iff` and `strong1_iff`. Eligibility (`Eligible I`), the run-extension theorem, inhabitation and certificates move to plan 1c.

**Tech Stack:** Lean 4 v4.30.0-rc2, Mathlib v4.30.0-rc2, Lake.

**Spec:** `docs/FRAMEWORK-DESIGN.md` v7: §2 E4 (delivery outcomes, `excludes`, WindowMargin), §3 (instances), §5 (certificates, registry), §6 (Kit.Engine), §8 row 1. `docs/PHASE0-REPORT.md` §6 (open rows GridCO ×2, Engine, Kit). `docs/PHASE1A-REPORT.md` ("Inputs for plan 1b"). The contract theorems: `gridContract_from_engine` (`AvailableChainGridCO/Proofs/Contract.lean:15`), `saContract_from_engine` (`AvailableChainSA/Proofs/Contract.lean:12`), `sapcContract_from_engine` and `sapcStrong_from_engine` (`AvailableChainSAPC/Proofs/{Contract,StrongContract}.lean`).

---

## Scope: plans 1b, 1c, 2

Plan 1a's scope table gave plan 1b eligibility, the run-extension theorem, inhabitation and certificates as well. The survey for this plan (2026-09-29) splits that work in two. The reasons are in "Findings" below.

```text
┌──────┬───────────────────────────────────────┬──────────────────────────────────────┐
│ Plan │ Scope                                 │ Needs                                │
├──────┼───────────────────────────────────────┼──────────────────────────────────────┤
│ 1b   │ THIS PLAN. Kit and V2-sketch library  │ 1a (closed, a27cb92)                 │
│      │ split; Grid CO/SA and L* `excludes`   │                                      │
│      │ (E4); hook facts and HooksSound for   │                                      │
│      │ the four protocols; Instance and      │                                      │
│      │ StrongInstance values; `holdsAt`      │                                      │
│      │ theorems for ac-4.3 and strong-1;     │                                      │
│      │ ac43 → core relation lemmas; registry │                                      │
│      │ row kind profile-holds; MATRIX.md     │                                      │
│ 1c   │ `Eligible I` (EmitWellFormed,         │ 1b: instances, Kit.Engine library,   │
│      │ HandlerCoverage, Deliverable,         │ E4 excludes                          │
│      │ RelayFeasible) defined together with  │                                      │
│      │ its consumer, the Kit.Engine run-     │                                      │
│      │ extension theorem; inhabitation;      │                                      │
│      │ certificates and ProfileCerts for     │                                      │
│      │ Grid CO, SA, SA-PC; the I1 witness    │                                      │
│      │ against Candidate × Eligible; the     │                                      │
│      │ shared-C SA-PC profile certificate    │                                      │
│ 2    │ Engine v2, lift, I1 fix (unchanged    │ 1c                                   │
│      │ from plan 1a's table)                 │                                      │
└──────┴───────────────────────────────────────┴──────────────────────────────────────┘
```

## Findings that change the premises (survey, 2026-09-29)

1. **The contract needs no E4 change.** Design §2 E4 (lines 154–163) says that `AcceptedObjectRelay` and `HealthyAcceptedObjectRelay` are regime conditions without an exclusion exemption, and that Phase 1 must fix them. This text is out of date. The receipt-relay merge (`1a3f73a`) removed the `acceptedRelay` field from all five regimes (`SleepyRegime`, `OutageRegime`, `RecoveryRegime`, `StrongArmedRegime`, SA-PC's `QuorumRecoveryRegime`; `docs/CONTRACT.md:283-299`). Today every regime uses `PartialSynchrony` (`Generic/Conditions.lean:104-127`) or `HealthyPrefixDelivery` (`:129-151`). Both relay handler calls, not acceptance, and both have had the exclusion exemption since the first commit. `AcceptedObjectRelay` survives only in derived results, none of them a regime field: the SA-PC adapters (`AvailableChainSAPC/Proofs/ReceiptRelay.lean:260-306`), `healthyPrefix_acceptedRelay` (`AvailableChainGridCO/Proofs/HealthyPrefix.lean:93-95`) and Counter's `canonical_relay` (`AvailableChainRegistry/CounterRun.lean:470`). So the coverage gap that design §2 describes is already closed, and this plan does not change `AvailableChainStatements`.
2. **SA-PC has no permanent refusal.** SA-PC's `processed` for a HEAD is membership in the archive `receivedHeads` (`AvailableChainSAPC/Model/Handlers.lean:82`). `receiveHead` refuses only a future label (`:12`), which is temporary. The Grid CO old-label and equivocation refusals act only on the base cache (`:16`), not on `processed`. PCs are refused only before `pcEnvelopeReady` (temporary). Under E4, `excludes := fun _ _ => false` is therefore the correct classification for SA-PC, and `receipt_acceptedRelay` (which uses it) stays valid. Design §2's "and for SA and SA-PC too" holds for SA (the same code as Grid CO) but not for SA-PC.
3. **Grid CO and SA have two permanent HEAD refusals** in `admitVote` (`AvailableChainGridCO/Model/Protocol.lean:300-309`): a HEAD of label `r` when `r < current - 1` (line 306; the clock only goes forward), and a HEAD from a seat that already equivocates at `r` (line 307). `gridCOx` (`AvailableChainRegistry/GridCOHooks.lean:15-24`) models both, and `gridCOx_hooks` proves `HooksSound` for it. Its old-label clause does not test `processed` (PHASE0-REPORT §6, GridCO row). The E4 reason to move it into `gridCO` is the delivery classification (RelayFeasible, plan 1c): with `excludes = false`, a late HEAD refusal is a "temporary refusal" that never ends. Coverage is not the reason (finding 1).
4. **L* has two permanent refusals** (corrected by the Claude review, M3): the third equivocation (`AvailableChainLStar/Model/Protocol.lean:273-274`), and a proposal wire whose block is already stored. L* `processed` for a proposal is wire membership (`:314-315`), but `admitProposal` refuses when `b ∈ st.blocks` (`:283`): a faulty proposer can sign two well-formed wires with the same block, and the second wire is refused for good. L* admits late votes of old labels (`:270-272`). Grid CO and SA-PC do not have the proposal refusal, because their `processed` for a proposal is block-level (`blockKnown`). L* has no claim proofs (`Statements/Contract.lean:60-63` is a statement only), so it gets an instance but no `holdsAt` theorem.
5. **Eligibility belongs with its consumer.** `EmitWellFormed`, `HandlerCoverage`, `Deliverable` and `RelayFeasible` do not exist in Lean. Their only consumer is the run-extension theorem, which does not exist either: Phase 0's "run extension" is `canonical_sleepy` for Counter only (`AvailableChainRegistry/CounterRun.lean:508`), whose scheduler hard-codes the delivered objects. No append or extension lemma exists; the only prefix lemmas restrict a run (`AvailableChainGridCO/Proofs/RunPrefix.lean`). Definitions in `AvailableChainFramework` are locked on first write. Definitions written before the theorem that uses them are likely to need a lock change. So plan 1c defines `Eligible` and proves the theorem in the same plan.
6. **No proved construction of a run for every horizon exists for any of the four protocols** (a missing construction, not a proof that none exists; Astra P1b-08), and persistence certificates need `C.budget > 0`, so `η > 0` (every `Params` allows `η = 0`). Both are plan 1c inputs.
7. **The engine-generic lemmas live in the Grid CO library.** Namespace `AvailableChain.Engine` is in `AvailableChainGridCO/Proofs/{Execution (lines 1–210), EngineClock, RunPrefix, HealthyPrefix, HealthyInterior, ProtectionInduction, SourceHistory}.lean`, and `Execution.lean:2` imports `AvailableChainGridCO.Proofs.History` only for its transitive imports. SA, SA-PC and the Registry have about 124 references to it.

## Rulings in this plan

- **No contract change, no lock break.** `AvailableChainStatements` is not edited. `AcceptedObjectRelay` and `HealthyAcceptedObjectRelay` keep their text (no regime uses them). The catalog lock reaches only `AvailableChainFramework` and the Statements and Model definitions in its closure (`scripts/CatalogLock.lean:55-70`); the protocol libraries are outside it. The only lock change is ADDED lines for Task 4. If any task shows a CHANGED or REMOVED lock line, it stops.
- **Grid CO `excludes`** (Task 1) is exactly the permanent refusals of a HEAD that is not yet processed. It is disjoint from `processed` by construction (answers PHASE0-REPORT §6 GridCO row 1: yes, they stay disjoint). Proposals are never excluded.
- **The WindowMargin interface** (async M-series; DC-simplify 2026-09-29). Every Grid CO relay lemma that used `excludes = false` by `rfl` gets a premise "the reader does not exclude `o` at any time up to the lemma's cutoff" (Task 1 Step 4). One module, `AvailableChainGridCO/Proofs/WindowMargin.lean`, proves that premise for every caller. A later admission guard (I9) extends `excludes` to more objects; then only WindowMargin lemmas change, not the relay lemmas. See "Shared sites with I9".
- **Hook facts live in the protocol libraries; `HooksSound` values live in the Registry.** No protocol library imports `AvailableChainFramework` today. No written rule forbids it (Astra P1b-09); this plan CHOOSES that import boundary, so that the protocol libraries stay independent of the framework's locked types. Each library proves the five hook facts in its own namespace with the same statement shape as the `HooksSound` fields (`AvailableChainFramework/Hooks.lean:31-50`); the Registry assembles them.
- **`holdsAt` is not a certificate.** A theorem `ac43.holdsAt I C` proves the claims' propositions without inhabitation (design §5: "Transport of `holds` does not transport `inhabited`"). The registry shows it with the new kind `profile-holds`, and `MATRIX.md` shows it as `holds`, never as `cert`.
- **Kit split** (PHASE0-REPORT §6, Kit row): library `AvailableChainKit` (L5: `Core`, `Engine/*`) and library `AvailableChainEngineV2` (the L0 sketch, which plan 2 grows). Namespaces do not change (`AvailableChain.Engine` for the engine lemmas), so references do not change; only imports change. `AvailableChainFramework` does not import the Kit (Kit is L5, above the Framework's L2–L3).
- **Constraint from the FG-SA branch** (`fgsa-composition`, merge-base `d415a7c`; DC-simplify 2026-09-29). That branch uses the Grid CO and SA state functions `admitProposal`, `admitVote`, `gate`, `propose` and the voter views, and the lemmas `gate_target_origin`, `confirmation_mem`, `gate_eq_writeKeys`, `admitVote_*`, `gate_blocks`, `recordGenuine` (at `slowLeasePolicy`). It imports `AvailableChainGridCO.Proofs.{GenuineHistory, History, Map, RecordSlots, Roots}`, `AvailableChainSA.Model.Protocol` and `AvailableChainKitFG.Correspondence`. This plan does not change those function bodies, those lemma statements, or those module paths. A rebase of that branch then needs a rebuild and a lakefile merge only.

## Shared sites with I9 (root collisions; a user decision, NOT in this plan)

r194/r196 (`research/async-resilient-committees/tip-stability/codex/root-design.md`, `root-nonce.md`) propose a root check in block admission and wire validity. This plan touches some of the same code. A later I9 change must re-check these sites; this plan arranges them so that the re-check is local.

```text
┌──────────────────────────────────────┬──────────────────────┬──────────────────────────────┐
│ Site                                 │ This plan            │ I9 (later)                   │
├──────────────────────────────────────┼──────────────────────┼──────────────────────────────┤
│ Grid CO `propose` (Protocol.lean:    │ not changed          │ builds `mkBlock`; also an    │
│ 287-292)                             │                      │ FG-SA constraint site        │
│ SA-PC `propose` (Choice.lean),       │ not changed          │ builds `mkBlock`             │
│ L* `propose` (Protocol.lean:253-259) │                      │                              │
│ Grid CO `admitProposal`              │ not changed          │ adds `rootOK` before insert  │
│ Grid CO proposal `wellFormed`        │ not changed          │ adds `rootOK`                │
│ Grid CO `excludes`                   │ NEW (HEADs only)     │ unchanged in r196's minimal  │
│                                      │                      │ variant (see note); else may │
│                                      │                      │ add bad-root proposals       │
│ Grid CO relay lemmas (ClockBounds,   │ premise "not         │ unchanged: the premise       │
│ ProposalDelivery, CrossView, Paths,  │ excluded up to the   │ covers every object class    │
│ Proposals)                           │ cutoff", all five    │                              │
│ Grid CO WindowMargin.lean            │ NEW: proves the      │ `proposal_not_excluded` then │
│                                      │ premise per caller,  │ needs "an ACCEPTED proposal  │
│                                      │ all object classes   │ has a good root" (source     │
│                                      │                      │ acceptance gives it, also    │
│                                      │                      │ for a faulty proposer)       │
│ SA-PC `wellFormed`, `proposalBase`   │ not changed          │ adds `rootOK`                │
│ SA-PC `excludes`                     │ stays false          │ as Grid CO: only if admission│
│                                      │                      │ checks more than the wire;   │
│                                      │                      │ then receipt_acceptedRelay's │
│                                      │                      │ `rfl` (ReceiptRelay.lean:265,│
│                                      │                      │ 275) needs a WindowMargin    │
│                                      │                      │ lemma as in Grid CO          │
│ L* handler and wire rule             │ `excludes` added     │ adds `rootOK`                │
│                                      │ (equivocation and    │                              │
│                                      │ stored-block wire)   │                              │
│ FG-SA branch Proofs/Admission.lean   │ not affected         │ base_admitProposal_accepts   │
│ (base_admitProposal_accepts,         │                      │ and admission agreement      │
│ admission agreement)                 │                      │ compare FG and Grid CO       │
│                                      │                      │ admission: must be redone    │
│ Hook facts (Tasks 1–3)               │ NEW                  │ `excludes_inert`/`_stable`   │
│                                      │                      │ re-proved for the new clause │
└──────────────────────────────────────┴──────────────────────┴──────────────────────────────┘
```

Superseded 2026-09-29 by the user's I9 decision (design §12): no `rootOK` in `wellFormed`; the root check is the dependency lookup.

Note (Claude review m9b). In r196's minimal variant, `rootOK` is in `wellFormed` and in admission, as the same local check. A proposal with a bad root is then outside `ExecutionValid` (`DeliveryWellFormed.wire`, `Conditions.lean:55-57`), so admission never refuses a valid delivery for its root. I9 then adds no permanent refusal: neither `excludes` nor SA-PC's `rfl` sites change. They change only if admission checks more than the wire check.

## Global Constraints

- Toolchain and Mathlib v4.30.0-rc2. Do not run `lake update`.
- No `sorry`, `admit`, `native_decide`, or new axioms. Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.
- The Mac `lean` is a throttle wrapper (3 slots). Run `pgrep -fl lean` before a build. Use `lake env lean --run <file>` for scripts; never a `lean_exe`.
- Do not edit `AvailableChainStatements/**` or `AvailableChainModel/**`.
- Do not change the statement of `gridContract_from_engine`, `saContract_from_engine`, `sapcContract_from_engine`, `sapcStrong_from_engine`, or of any theorem that `AvailableChainSA/Tests/Axioms.lean` or `AvailableChainSAPC/Tests/Axioms.lean` prints. A statement change elsewhere in a protocol library is allowed only to add the premise of Task 1 Step 4 (`∀ u ≤ cutoff, ¬ excluded`; for `synchronous_block_path_at_gate` restricted to its proposal wires) and must be listed in the task report.
- The FG-SA constraint above: no change to the bodies of `admitProposal`, `admitVote`, `gate`, `propose`, the voter views; no change to the statements of `gate_target_origin`, `confirmation_mem`, `gate_eq_writeKeys`, `admitVote_*`, `gate_blocks`, `recordGenuine`; no move of `AvailableChainGridCO.Proofs.{GenuineHistory, History, Map, RecordSlots, Roots}`.
- The catalog lock: `CatalogLock --check` exits 0 even when lines are only ADDED (Claude review, lock note). So every checkpoint that says "lock unchanged" requires `--check` to exit 0 AND print nothing, and `git diff docs/catalog.lock` to be empty. Task 4 is the only task that adds lines, with `--write` (no `--allow-changes`).
- Registry: `scripts/Registry.lean` then `--check` exit 0 after every task that changes the Registry library.
- `bash scripts/check-fg.sh` exits 0 at Tasks 0 and 7 (the Kit move changes GridCO imports; KitFG must still build).
- Commit by explicit path. Never stage `log.md`, `state.md`, `docs/FG-COMPOSITION.md`. Commit messages end with the `Claude-Session:` line.
- Prose in ASD-STE100 Simplified Technical English; tables in Unicode box drawing inside fenced `text` blocks.

## Review Focus

1. **`excludes` must not over-exclude.** An object that `admitVote` would still accept later must never be excluded. Otherwise `PartialSynchrony` drops a real delivery obligation, and the regime admits runs in which a still-acceptable HEAD is never delivered; the proofs would then fail or, worse, a later weaker proof would certify those runs. Test: in Task 1, `excludes_head_iff` (both directions) and `excludes_proposal`, plus the stability of exclusion (`excludes_stable`), which shows the refusal is permanent.
2. **A HEAD accepted in the last Δ before its exclusion time.** A relay lemma that concludes a handler call at the reader for such a HEAD is now false. Every such lemma gets the premise; no caller may discharge it for a label-`r` HEAD with a deadline after `proposalTime (r + 2)`.
3. **A third HEAD from an equivocating faulty seat** is excluded at any time. A caller that relays a faulty HEAD must accept the "`∨ equivocates`" outcome (as `accepted_head_receipt_before` already does, `ReceiptRelay.lean:133-160`), or prove non-equivocation.
4. **`processed` and `excludes` stay disjoint** after every step of a run, not only in one state.
5. **The Kit move changes no statement.** Every moved declaration keeps its name and namespace; `git diff -M` shows moves, and a name-by-name check of `#print axioms` for the moved theorems passes.

---

### Task 0: Kit and V2-sketch libraries

**Files:**
- Modify: `lakefile.toml` (two `[[lean_lib]]` entries; `defaultTargets`)
- Create: `AvailableChainKit.lean`, `AvailableChainKit/Core.lean` (moved from `AvailableChainFramework/Kit/Core.lean`), `AvailableChainKit/Engine/{Execution,EngineClock,RunPrefix,HealthyPrefix,HealthyInterior,ProtectionInduction,SourceHistory,Stable}.lean`
- Create: `AvailableChainEngineV2.lean`, `AvailableChainEngineV2/Sketch.lean` (moved from `AvailableChainFramework/Engine/V2Sketch.lean`)
- Modify: `AvailableChainFramework.lean` (remove the two imports), `AvailableChainGridCO/Proofs/Execution.lean` (keeps only its Grid CO part, lines 212 onward), every importer of a moved module, `AvailableChainRegistry/GridCOHooks.lean` (remove `stateBefore_stable`), `scripts/CheckFrameworkAxioms.lean` (add `import AvailableChainKit`, `import AvailableChainEngineV2`, and both names in `libraries` at `:22`; without the imports the new libraries stay unchecked, Claude review m3), `docs/MAP.md`

**Interfaces:**
- Produces: library `AvailableChainKit` with namespace `AvailableChain.Engine` (all moved engine lemmas, names unchanged) and `AvailableChain.Framework.Kit` (`block_preceq_trans`, `includedPersist_of_safe`; the namespace does not change, Claude m2 / Astra P1b-06); `AvailableChain.Engine.stateBefore_stable`; library `AvailableChainEngineV2` (namespace `AvailableChain.Framework.V2Sketch` unchanged).

- [ ] **Step 1: Check genericity.** For each candidate file, confirm that it uses no declaration from `AvailableChain.GridCO`, `AvailableChain.SA` or `AvailableChain.SAPC`: `grep -n 'GridCO\.\|gridCO\|SAPC\.\|SA\.' <file>`. A file that uses one stays in Grid CO; record it in the report. `Execution.lean` splits at line 212: lines 1–210 (namespace `AvailableChain.Engine`) move; the `AvailableChain.GridCO` re-exports stay in `AvailableChainGridCO/Proofs/Execution.lean`, which then imports `AvailableChainKit.Engine.Execution`.
- [ ] **Step 2: Imports of the new library.** Each Kit file imports only `AvailableChainModel.*`, `AvailableChainStatements.*`, Mathlib and other Kit files. Replace `public import AvailableChainGridCO.Proofs.History` in the moved `Execution.lean` by the Statements and Mathlib modules that it needs (find them with a build error loop; start from `AvailableChainStatements.Generic.Regimes` and `Mathlib.Tactic`).
- [ ] **Step 3: Move `stateBefore_stable`** (`AvailableChainRegistry/GridCOHooks.lean:52-78`) to `AvailableChainKit/Engine/Stable.lean`, namespace `AvailableChain.Engine`, statement unchanged. `GridCOHooks.lean` imports it.
- [ ] **Step 4: Lakefile.** Add

```toml
[[lean_lib]]
name = "AvailableChainKit"
# Kit (L5): engine-generic lemmas and derived results. Imports Model and Statements only.

[[lean_lib]]
name = "AvailableChainEngineV2"
# Engine v2 sketch (L0, design §2 E5/E6). Plan 2 grows it into engine v2.
```

  and add both names to `defaultTargets`. Copy the style of the existing entries (check `lakefile.toml` first; keep their key order and options).
- [ ] **Step 5: Importers.** The moved files now reach Grid CO modules transitively (`EngineClock`, `RunPrefix` and `ProtectionInduction` import `GridCO.Proofs.Execution`, which imports `History`). An importer that switches to the Kit path can lose those transitive imports: then add the missing Grid CO import to that importer, with no proof change (Claude m4). `grep -rln 'AvailableChainGridCO.Proofs.\(EngineClock\|RunPrefix\|HealthyPrefix\|HealthyInterior\|ProtectionInduction\|SourceHistory\)\|AvailableChainFramework.Kit\|AvailableChainFramework.Engine' --include=*.lean .` and change each import to the new path. Do not change any proof.
- [ ] **Step 6: No dedupe.** The two `block_preceq_trans` have different statements: the Kit one uses `Block.Preceq` (`Kit/Core.lean:13-14`), the private Grid CO one `Block.preceq … = true` (`Map.lean:25-28`); they are only definitionally equivalent (Claude m2, Astra Q6). Keep both. Task 7 records the ruling in PHASE0-REPORT §6, Kit row.
- [ ] **Step 7: CHECKPOINT.** `lake build --wfail` (every default target) is green. `CatalogLock --check` exits 0 and prints nothing, and `docs/catalog.lock` is unchanged. `Registry` then `--check` exit 0; `docs/REGISTRY.md` unchanged. `CheckFrameworkAxioms` exits 0 (now over Framework, Registry, Kit, EngineV2). `bash scripts/check-fg.sh` exits 0. `git diff -M --stat` shows the moves as renames. Update `docs/MAP.md` (new libraries; moved files). Commit `Kit: engine-generic lemmas and the v2 sketch in their own libraries`.

### Task 1: Grid CO permanent exclusion (E4) and hook facts

**Files:**
- Modify: `AvailableChainGridCO/Model/Protocol.lean` (new `excludes`; `gridCO.excludes := excludes p`)
- Create: `AvailableChainGridCO/Proofs/Hooks.lean`, `AvailableChainGridCO/Proofs/WindowMargin.lean`
- Modify: the five Grid CO relay lemmas that used `rfl` for `excludes` — `ClockBounds.lean:139` (`synchronous_head_handled_early`), `ProposalDelivery.lean:139` (`synchronous_proposal_delivered`), `CrossView.lean:17` (`synchronous_receipt_before`), `Paths.lean:288` (`synchronous_block_path_at_gate`), `Proposals.lean:102` (`handled_before_proposal_of_ready`) — and their callers, which are only in Grid CO: `ClockBounds:176`, `CrossView:54`, `CrossView:84`, `ProposalDelivery:186`, `ProposalViewRelay:31`, `ProposalViewRelay:91`, `Paths:357` (Claude m7, Astra re-check). None of the five is in `catalog.lock`, `REGISTRY.md`, a `Tests/Axioms` file or the FG-SA branch; `AvailableChainGridCO.lean` (imports)
- Modify: `AvailableChainRegistry/GridCOHooks.lean` → rename to `AvailableChainRegistry/Instances/GridCOHooks.lean`, reduced to the `HooksSound (gridCO p)` assembly; `gridExcludes`, `gridCOx` and the model facts are removed from the Registry
- Modify: `AvailableChainGridCO.lean`, `docs/GRIDCO-STATUS.md` (one dated paragraph)

**Interfaces:**
- Consumes: Task 0 (`AvailableChain.Engine.stateBefore_stable`).
- Produces: `AvailableChain.GridCO.excludes`; in `AvailableChain.GridCO`: `excludes_inert`, `excludes_stable`, `processed_stable`, `deps_stable`, `handles_carries` (the `HooksSound` field shapes, specialized to `gridCO p`, generic in `[LeasePolicy]`); `excludes_proposal`, `excludes_head_iff`, `head_not_excluded_before`, `head_excluded_before_equivocates`, `proposal_not_excluded` and the per-caller WindowMargin lemmas; `AvailableChain.Registry.GridCO.gridHooks : HooksSound (gridCO p)`.

- [ ] **Step 1: The definition** (in `Model/Protocol.lean`, before `gridCO`):

```lean
/-- Permanent rejection (design §2 E4) of a HEAD that is not yet processed:
its label `r` is before the previous slot (the clock only goes forward), or
its seat already equivocates at `r`. `admitVote` returns the state unchanged
in both cases, and in no later state of a valid run accepts the HEAD. A
processed HEAD is not excluded, and a proposal is never excluded. "Exactly the
permanent refusals" holds for objects that pass the wire check (`wellFormed`);
an ill-formed object is also refused for good, but `DeliveryWellFormed.wire`
keeps it out of every valid run (Claude m13). -/
def excludes (p : Params) {n : Nat} (st : State n) (o : Wire n) : Bool :=
  match o.auth, o.payload with
  | .seat r i, .head _ =>
      !decide (o ∈ st.votes) &&
        (decide (r + 1 < (st.now / (4 * p.Δ)).toNat) || equivocates (votesAt st r) i)
  | _, _ => false
```

  and in `gridCO`: `excludes := excludes p`. `sa p` inherits it (`AvailableChainSA/Model/Protocol.lean:95-96`).
- [ ] **Step 2: Exactness tests** (in `Proofs/Hooks.lean`), Review Focus 1 and 4:

```lean
theorem excludes_proposal (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (B : Block) (raw support : List (HeadWire n))
    (hp : o.payload = .proposal B raw support) : excludes p st o = false

/-- A HEAD that is not processed is excluded iff `admitVote` refuses it
permanently: the old-label test or the equivocation test holds. -/
theorem excludes_head_iff (p : Params) {n : Nat} (st : State n) (r : Slot)
    (i : Fin n) (x) :
    excludes p st ⟨.seat r i, .head x⟩ = true ↔
      (⟨.seat r i, .head x⟩ : Wire n) ∉ st.votes ∧
        (r + 1 < (st.now / (4 * p.Δ)).toNat ∨ equivocates (votesAt st r) i = true)

theorem excludes_not_processed (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (h : excludes p st o = true) : processed st o = false
```

  Adapt the binder types (`HeadWire`, the `head` payload argument) to the real `Msg` constructors; the statements' meaning must not change.
- [ ] **Step 3: Hook facts.** Move `clock_votes` (`GridCOHooks.lean:108`), `gate_votes` (`:90`), `process_votes_subset` (`:209`), `process_blocks_subset` (`:234`, now public) into `Proofs/Hooks.lean`; delete `engineClockx` (`:251`), because `engineClock` (`ClockBounds.lean:48`) is already `ClockLaws (gridCO p)` (Claude m6), namespace `AvailableChain.GridCO` (PHASE0-REPORT §6, GridCO row 2). Prove the five run-level facts for `gridCO p`, each with the statement of the matching `HooksSound` field (`AvailableChainFramework/Hooks.lean:33-50`) with `P := gridCO p`. Proof guide: port `gridCOx_hooks` (`GridCOHooks.lean:257-344`); the new `!decide (o ∈ st.votes)` conjunct makes `excludes_stable` need `processed` to stay false for an excluded HEAD. That needs the old-label test at every later state, which holds only because `now` does not decrease on a valid run; `stateBefore_stable` asks for the property after every `clock st t` for any `t`, so it cannot prove this. Prove a run-indexed variant in which the clock step gets `now` monotonicity from `ScheduleWellFormed` (Claude m5; not a stop condition). The HEAD stays unprocessed because `process` on an excluded HEAD is the identity (`excludes_inert`), and a carried raw HEAD enters only through `admitVote`, which refuses it on the same tests (`handles`, `Model/Protocol.lean:364-368`). If this is false for some path, stop and report.
- [ ] **Step 4: The relay premise, for every object class.** Add to each of the five lemmas the premise

```lean
    (hx : ∀ u, u ≤ <cutoff> →
        (gridCO p).excludes (Run.stateBeforeTime (gridCO p) rho u reader) o = false)
```

  where `<cutoff>` is the lemma's own cutoff (`cut`, `proposalTime p s`, or the bound the lemma already has on its deadline). `synchronous_block_path_at_gate` has no `o` parameter: it obtains the wire inside the proof (`Paths.lean:308-309`). A premise over every `o` would be false and its caller (`Paths.lean:357`) could not discharge it. Give it the premise only for the proposal wires with its block `B`: `∀ o, (∃ raw support, o.payload = .proposal B raw support) → ∀ u ≤ earlyTime p r, ¬ excluded`, instantiated with the wire that the proof obtains at `:308`; its caller at `Paths.lean:357` discharges it with `proposal_not_excluded` (re-check N2, Astra re-check P1b-05). Add `Paths:357` to the caller list above. One deadline is not enough: two lemmas choose the network branch inside the proof, and the branches use `max t E.t_GST + E.Δ` and `t + E.Δ`; both are at most the cutoff. The `∀ u ≤ cutoff` form needs no stability argument, which `handled_before_proposal_of_ready` could not make (its `ProposalRelayReady` premise has no `ScheduleWellFormed`, `Windows.lean:138-141`) (Claude M2, Astra Q3). The two proposal lemmas also get the premise, although today `excludes_proposal` discharges it: the relay lemmas then do not depend on which object classes `excludes` covers, and a later exclusion of proposals (I9, non-minimal variant) changes only the WindowMargin lemma `proposal_not_excluded` and its callers, not the relay lemmas (Astra P1b-05). Keep the rest of each statement.
- [ ] **Step 5: WindowMargin** (`Proofs/WindowMargin.lean`). Prove, for the reader's state at a time `u`, the bound on `now` from the clock laws (`AvailableChain.Engine.stateBefore_now_le_event`, `ClockLaws` in the Kit), and then:

```lean
/-- A label-`r` HEAD whose seat does not equivocate in the reader's votes is
not excluded at any time before `proposalTime p (r + 2)`. -/
theorem head_not_excluded_before … (hu : u ≤ proposalTime p (r + 2))
    (heq : equivocates (votesAt (Run.stateBeforeTime (gridCO p) rho u w) r) i = false) :
    (gridCO p).excludes (Run.stateBeforeTime (gridCO p) rho u w) ⟨.seat r i, .head x⟩ = false
```

  and

```lean
/-- A label-`r` HEAD that the reader excludes before `proposalTime p (r + 2)`
is excluded for equivocation: the reader already holds two label-`r` HEADs
of that seat (Claude M1). -/
theorem head_excluded_before_equivocates … (hu : u ≤ proposalTime p (r + 2))
    (hx : (gridCO p).excludes (Run.stateBeforeTime (gridCO p) rho u w)
        ⟨.seat r i, .head x⟩ = true) :
    equivocates (votesAt (Run.stateBeforeTime (gridCO p) rho u w) r) i = true

/-- Today every proposal; the one place to change if `excludes` ever covers
proposals (I9, non-minimal variant). -/
theorem proposal_not_excluded … (hp : o.payload = .proposal B raw support) :
    ∀ u, (gridCO p).excludes (Run.stateBeforeTime (gridCO p) rho u w) o = false
```

  The honest caller (`ClockBounds.lean:176`) uses `honest_not_equivocating_at_event` (`Votes.lean:375`) with `head_not_excluded_before`. The two callers that relay a label-`r` HEAD of an arbitrary seat, `CrossView.lean:84` (`synchronous_accepted_head_before`) and `ProposalViewRelay.lean:91` (`stored_head_before_ready_proposal`), get an explicit case split before the call to `accepted_head_receipt_before`. Either the HEAD is not excluded at any `u ≤ cutoff`, and the premise holds; or it is excluded at some `X ≤ cutoff ≤ gateTime r`, and `head_excluded_before_equivocates` gives two stored label-`r` HEADs of that seat with stamps before `X`, which is the conclusion's existing "`∨ equivocates`" outcome. For CrossView use `stored_vote_stamp_before_cut` and `equivocates_mono`; for ProposalViewRelay, `votesAt` is monotone up to `proposalTime (r + 1)` (Claude M1). The proposal callers use `proposal_not_excluded`. The callers' cutoffs are at most `gateTime r` (t_r + 6Δ) for label-`r` HEADs (survey: `CrossView.lean:62-86`, `ProposalViewRelay.lean:67-99`), which is before `proposalTime (r + 2)` (t_r + 8Δ): the margin is 2Δ ≥ Δ (design §2, WindowMargin). Both reviews checked every caller: each caller that relays a faulty HEAD already allows "`∨ equivocates`" (Review Focus 3). If the implementer finds one that does not, stop and report it with the lemma name. Do not weaken a conclusion to make a proof go through.
- [ ] **Step 6: Registry.** `AvailableChainRegistry/Instances/GridCOHooks.lean` defines `gridHooks [LeasePolicy] (p : Params) : HooksSound (gridCO p) := ⟨excludes_inert p, …⟩`. Delete `gridExcludes`, `gridCOx`, `gridCOx_hooks`, `inWindow_not_excluded` from the Registry (`inWindow_not_excluded` becomes a Grid CO WindowMargin lemma). Registry root import updated.
- [ ] **Step 7: CHECKPOINT.** `lake build --wfail` (every default target) green. The four contract theorems keep their statements (`git diff` of `Proofs/Contract.lean` files and `Statements/` is empty). `AvailableChainSA/Tests/Axioms.lean` and `AvailableChainSAPC/Tests/Axioms.lean` build and print only the allowed axioms. Lock `--check` exit 0, unchanged. Registry and `--check` exit 0. `check-fg.sh` exit 0. The report lists every statement that gained the premise, with its callers and the WindowMargin lemma that discharges it. One dated paragraph in `docs/GRIDCO-STATUS.md`. Commit `GridCO: E4 permanent exclusion of HEADs, hook facts, WindowMargin`.

### Task 2: L* exclusion and hook facts

**Files:**
- Modify: `AvailableChainLStar/Model/Protocol.lean` (new `excludes`; `lstar.excludes := excludes`)
- Create: `AvailableChainLStar/Proofs/Hooks.lean`
- Modify: `AvailableChainLStar.lean`

**Interfaces:**
- Produces: `AvailableChain.LStar.excludes` and the five run-level hook facts for `lstar p n`.

- [ ] **Step 1:** Read `admitVote` (`Protocol.lean:266-276`), `admitProposal` (`:280-288`) and `processed` (`:312-315` and the HEAD case). Define `excludes` in the style of Task 1 Step 1 with two clauses: a HEAD that is not processed and whose seat already equivocates at `r`; and a proposal wire `o` with block `b` such that `o ∉ st.proposals ∧ b ∈ st.blocks` (the stored-block refusal at `:283`; Claude M3, Astra P1b-01). False otherwise. L* has no old-label refusal (`:270-272`); do not add one.
- [ ] **Step 2:** Prove `excludes_head_iff`, `excludes_proposal_iff` (both directions; with the test that a second well-formed wire for an already stored block is excluded and that a wire whose block is not stored is not), the permanence of both clauses (stored blocks are never removed; equivocation evidence only grows) and `excludes_not_processed`, as in Task 1 Step 2, and the five hook facts for `lstar p n`. L* has its own engine (it does not import Grid CO): prove the monotonicity of its votes, proposals and blocks under `clock` and `process` directly, then lift them with `AvailableChain.Engine.stateBefore_stable`.
- [ ] **Step 3: CHECKPOINT.** Build green; lock unchanged; `docs/MAP.md` row. Commit `LStar: E4 exclusion (third equivocation, stored-block wire), hook facts`.

### Task 3: SA-PC hook facts

**Files:**
- Create: `AvailableChainSAPC/Proofs/Hooks.lean`
- Modify: `AvailableChainSAPC.lean`

**Interfaces:**
- Produces: the five run-level hook facts for `sapc p` (with `excludes = false`, the two exclusion facts are immediate).

- [ ] **Step 1:** Prove `processed_stable` from `stateBefore_archive_mono` (`Proofs/Acceptance.lean:44`), `stateBefore_blocks_mono` (`Proofs/Paths.lean:120`) and `pcValid_mono` (`Proofs/CertificateValidity.lean:39`); `deps_stable` from `pathKnown_mono`/`pcPaths_mono` (`:21`, `:30`) and the block monotonicity; `handles_carries` from `handles` ⊆ `carries` (`Model/Handlers.lean:74-99`: `raw ++ pcMembers c` ⊆ `raw ++ support ++ pcMembers c`; check the PC branch, whose `handles` members must be among `c.witnesses`). Both reviews checked the PC branch: it handles `c.witnesses`, and `carries` uses the same list (`Handlers.lean:88-99`).
- [ ] **Step 2:** Add a docstring to `sapc`'s `excludes` field use site (a comment in `Proofs/Hooks.lean`, not in the model) that records finding 2: no permanent refusal exists at the level of `processed`, so `excludes = false` is the E4 classification, not an omission.
- [ ] **Step 3: CHECKPOINT.** Build green; `AvailableChainSAPC/Tests/Axioms.lean` unchanged output; lock unchanged. Commit `SAPC: hook facts`.

### Task 4: Relation lemmas `ac-4.3 → core`

**Files:**
- Create: `AvailableChainFramework/Catalog/Relations.lean` (locked: prefix `AvailableChainFramework.Catalog`)
- Modify: `AvailableChainFramework.lean`, `docs/catalog.lock` (ADDED lines only)

**Interfaces:**
- Produces: `core_holdsAt_of_ac43`. (`candidateOfAc43` moves to plan 1c with its first consumer, by the same rule as `Eligible`: a locked definition is written together with its consumer; Claude m8.)

- [ ] **Step 1:**

```lean
/-- The four core claims are the first four entries of `ac-4.3`, with the core
constant `D := C.D_c` (PHASE1A-REPORT, plan 1b input 3). -/
theorem core_holdsAt_of_ac43 {I : Instance} {C : Constants} (h : ac43.holdsAt I C) :
    core.holdsAt I C.D_c

```

  `core.valid` needs `0 ≤ C.D_c`: take it from `Constants.Valid` (check the field name in `AvailableChainStatements/Generic/Constants.lean`). Membership in the entry lists: the pattern in `Catalog/Profiles.lean` (`List.mem_cons.1`, typed numerals).
- [ ] **Step 2:** Task 5 uses `core_holdsAt_of_ac43` for `grid_holds_core`, `sa_holds_core` and `sapc_holds_core`; that is its test.
- [ ] **Step 3: CHECKPOINT.** Build green. Lock `--check` shows ADDED lines only (save the output); `--write`; `--check` exit 0. Commit `Framework: ac-4.3 to core relation lemma` with `docs/catalog.lock`.

### Task 5: Instances and `holdsAt` theorems

**Files:**
- Create: `AvailableChainRegistry/Instances/{GridCO,SA,SAPC,LStar}.lean`
- Modify: `AvailableChainRegistry.lean`, `lakefile.toml` only if the Registry library needs `AvailableChainSA`, `AvailableChainSAPC`, `AvailableChainLStar` added to its dependencies (Lake libraries in one package need no dependency entry; check)

**Interfaces:**
- Consumes: Tasks 1–4; `ac43_iff`, `strong1_iff` (`Catalog/Profiles.lean:95-97`, `:203-205`).
- Produces: `gridInst (p) : Instance`, `saInst (p) : Instance`, `sapcInst (p) : StrongInstance`, `lstarInst (p n) : Instance`; the row theorems `grid_holds`, `sa_holds`, `sapc_holds_ac43`, `sapc_holds_strong1`, `*_holds_core` (at `G = 1`), their `*_of_pos` forms, and `sapc_holds_shared`.

- [ ] **Step 1: Instances.**

```lean
def gridInst (p : GridCO.Params) : Instance :=
  ⟨p.n, gridCO p, p.Δ, p.deltaPos, gridInterface p, gridHooks p⟩   -- default LeasePolicy

def saInst (p : SA.Params) : Instance :=
  ⟨p.n, sa p, p.Δ, p.deltaPos, saInterface p, @gridHooks slowLeasePolicy p.engine⟩

def sapcInst (p : SA.Params) : StrongInstance :=
  { n := p.n, P := sapc p, Δ := p.Δ, Δ_pos := p.deltaPos,
    iface := (sapcInterface p).toInterface, hooks := sapcHooks p,
    strong := (sapcInterface p).strong }

def lstarInst (p : LStar.Params) (n : Nat) : Instance :=
  ⟨n, lstar p n, p.Δ, p.deltaPos, lstarInterface p n, lstarHooks p n⟩
```

  Check the field order of `Instance` (`AvailableChainFramework/Instance.lean:16-25`) and use named fields if it differs. For SA: `sa p` is `@gridCO slowLeasePolicy p.engine` and `p.engine.Δ` must be `p.Δ` by `rfl`; if not, use a cast lemma and report it.
- [ ] **Step 2: `holdsAt`.**

```lean
theorem grid_holds_of_pos (p : GridCO.Params) (G : Time) (hG : 0 < G) :
    ac43.holdsAt (gridInst p) (gridConstants p G) :=
  (ac43_iff _ _).1 fun _ E hΔ => (gridContract_from_engine p E G hG hΔ).2

/-- The registry row: every parameter record, at the proposer gap `G = 1`. -/
theorem grid_holds (p : GridCO.Params) : ac43.holdsAt (gridInst p) (gridConstants p 1) :=
  grid_holds_of_pos p 1 one_pos

theorem sa_holds (p : SA.Params) : ac43.holdsAt (saInst p) (saConstants p 1)

theorem sapc_holds_ac43 (p : SA.Params) :
    ac43.holdsAt (sapcInst p).toInstance (sapcConstants p 1)

theorem sapc_holds_strong1 (p : SA.Params) :
    strong1.holdsAt (sapcInst p) (sapcConstants p 1, sapcStrongConstants p)

/-- Both SA-PC profiles at one `C` (PHASE1A-REPORT, plan 1b input 2, at the
`holds` level; the certificate pair is plan 1c). -/
theorem sapc_holds_shared (p : SA.Params) (G : Time) (hG : 0 < G) :
    ∃ C, ac43.holdsAt (sapcInst p).toInstance C ∧
      strong1.holdsAt (sapcInst p) (C, sapcStrongConstants p)

theorem grid_holds_core … : core.holdsAt (gridInst p) (gridConstants p G).D_c
```

  (and `sa_holds_core`, `sapc_holds_core` the same way). Each row theorem (`*_holds`, `*_holds_core`) has a general `*_of_pos` form over `G` with `0 < G`. Both forms are registry rows; only the `G = 1` forms are RESULT rows (`LEAN (family)`), because the leading hypothesis `0 < G` makes the `*_of_pos` rows CONDITIONAL (Task 6; Astra re-check N2). Use `_` for unused binders in the `ac43_iff` lambdas (`--wfail`; Astra Q7). Qualify every hook-fact name (`GridCO.processed_stable`, `SAPC.processed_stable`, `LStar.processed_stable`) in the `Instances/*` files; do not open two protocol namespaces in one file (Claude m11). `strong1_iff` needs `I.sface` to be `sapcInterface p`: `StrongInstance.sface` is `{ I.iface with strong := I.strong }` (`Facets/Strong.lean:17-18`), which is `sapcInterface p` by structure eta; if `rfl` fails, prove the equality and rewrite. L*: `lstarInst` only, with a docstring: "No `holdsAt` theorem: L* has no contract proof (`Statements/Contract.lean:60-63` is a statement)." A docstring on each instance: "An instance with hooks. It is not an eligible candidate: eligibility and certificates are plan 1c" (Astra Q8).
- [ ] **Step 3: CHECKPOINT.** Build green; lock unchanged. The new theorems are not registry rows yet (their type head `Profile.holdsAt` is not in `kinds` until Task 6), so Registry and `--check` exit 0 and REGISTRY.md is unchanged. Commit `Registry: Grid CO, SA, SA-PC and L* instances with holdsAt theorems`.

### Task 6: Row kind `profile-holds` and MATRIX.md

**Files:**
- Modify: `scripts/Registry.lean`, `docs/REGISTRY.md` (regenerated)
- Create: `docs/MATRIX.md` (generated)

**Interfaces:**
- Produces: row kind `profile-holds` for a theorem of type `Profile.holdsAt p I C` (args `K p I C`; the claim column shows the profile id, as `profile-cert`); `docs/MATRIX.md`; `--check` covers both files.

- [ ] **Step 1: Row kind and the family rule.** Add `(``AvailableChain.Framework.Profile.holdsAt, "profile-holds")` to `kinds`. The claim column uses `profileColumn env K p`. Today the scanner marks a row CONDITIONAL if its type has ANY leading binder (`scripts/Registry.lean:46`, `:157`), so the Task 5 rows (binder `p`) would be CONDITIONAL (Astra P1b-02). Change the rule, narrowly (re-check N1; Astra re-check, exact rule). Open the complete binder telescope, implicit and instance binders included, and test each binder type with `Lean.Meta.isProp`. Every open row stays CONDITIONAL by default; a non-Prop binder alone is not enough. A row is a FAMILY only if (a) its kind is `profile-holds`, (b) the telescope has exactly one binder, and (c) that binder's type is in the allowlist `familyBinders : List (Name × Name)` of pairs (type, witness): `(AvailableChain.GridCO.Params, AvailableChain.GridCO.Tests.smokeParams)` (`AvailableChainGridCO/Tests/Smoke.lean:16`) and `(AvailableChain.SA.Params, AvailableChain.SA.Tests.p)` (`AvailableChainSA/Tests/Smoke.lean:9`) (Astra recheck2: the names include `Tests`). The script checks that each witness exists, has exactly that type, and uses only the allowed axioms (exit 2 otherwise); so each parameter domain is non-empty, and its Prop fields (`deltaPos`, …) stay visible as the documented domain constraints. A witness proves that the domain is non-empty; it does not prove that a run exists (plan 1c). Any other family shape needs its own domain and a checked proof over the whole domain before it can be added to the allowlist. A family's status is computed as for a closed row (axiom check included) and printed with the suffix ` (family)`. Every other leading binder (a `Prop`, a data type outside the allowlist such as `Empty` or `PLift False`, a function type) makes the row CONDITIONAL, as today. Apply the gap rule BEFORE the suffix: a family row under `AvailableChainRegistry.Gaps` is `KNOWN-GAP (family)`, never `LEAN (family)` (re-check N3; the gap test at `Registry.lean:158` compares with `"LEAN"`). Negative tests, in a scratch module outside the scanned libraries or with the script's test mode, each must scan as CONDITIONAL: a `profile-holds` theorem with a leading `(e : Empty)` binder; one with `(h : PLift False)`; Astra's `structure HiddenAssumption : Type where proof : False` as a binder, and `Nat → HiddenAssumption`; a `profile-holds` theorem with two `GridCO.Params` binders; and a `cert` with a leading `GridCO.Params` binder (FAMILY is for `profile-holds` only). Check first that every existing row keeps its status (`REGISTRY.md` diff: only the new rows). The module docstring states: "A `profile-holds` row proves the profile's claim propositions at one constant, without inhabitation; it can be vacuous. It is not a certificate. A family row holds for every value of its data binders."
- [ ] **Step 1a: Instance identity** (Astra P1b-04). The instance column of a row must name the source instance: if the instance argument is `StrongInstance.toInstance x` (or another structure projection to `Instance`), print the head of `x` (`sapcInst`), not `StrongInstance.toInstance`. Test: `sapc_holds_ac43` and `sapc_holds_strong1` show the same instance name, and MATRIX puts them on one line.
- [ ] **Step 2: MATRIX.md.** Generated by the same script run, from the same rows: one line per instance (every constant in `instanceLibraries` whose type, after the leading binders are stripped, is `Instance` or `StrongInstance`: `gridInst : GridCO.Params → Instance` counts; this includes instances without rows, such as `lstarInst`) (re-check N4), one column per catalog claim (every `ClaimSpec`-typed constant under `AvailableChainFramework.Catalog`, shown by its id, in lock order) and one column per profile (`core.v1`, `ac-4.3`, `strong-1`). A cell is computed from the rows for that (instance, claim or profile), GATED BY STATUS (Astra P1b-03): only a row with status `LEAN` or `LEAN (family)` gives a result cell (`cert`, `refuted`, `refuted-all` for a refutation family, `holds`); a `KNOWN-GAP` or `KNOWN-GAP (family)` row gives `gap`; a `CONDITIONAL` row gives `cond`; any other status gives `unsound`. Several cells join with `+`; an empty cell is `·`. Instances that take parameters (for example `gridInst p`) appear once, by their constant name. A header paragraph gives the legend with this text for `holds`: "the claim propositions at one constant; no inhabitation; can be vacuous; not a certificate and not a `Candidate`" (Claude m12), and the KNOWN-GAP consumer contract ("`gap` and `cond` cells are records, not results; MATRIX consumers ignore them"). A `holds` cell from a family row is written `holds*`, and the legend line for `*` repeats the `holds` sentence next to the table (DC-simplify ruling: no family row reads as a certificate before plan 1c proves inhabitation).
- [ ] **Step 3:** `--check` compares both files with the generated text; exit 1 names the file that differs.
- [ ] **Step 4: CHECKPOINT.** `Registry` writes both files; `--check` exit 0. REGISTRY.md gains the `profile-holds` rows of Task 5: the `G = 1` rows with status `LEAN (family)`, and the `*_of_pos` rows with status `CONDITIONAL (not a certificate)`; every earlier row keeps its status. MATRIX shows `holds` only for the `LEAN (family)` rows, and the SA-PC `ac-4.3` and `strong-1` cells on the `sapcInst` line. The profile cells of `gridInst`, `saInst` and `sapcInst` show `holds*+cond`, because the CONDITIONAL `*_of_pos` rows fall on the same cells (re-check N6). Commit `Registry: profile-holds rows and MATRIX.md`.

### Task 7: Documents and handoff

**Files:**
- Modify: `docs/FRAMEWORK-DESIGN.md` (dated "As implemented in plan 1b" notes under §2 E4, §3 and §6; the approved text does not change), `docs/PHASE0-REPORT.md` §6 (close: GridCO rows 1 and 2, Kit (with the no-dedupe ruling); Engine only in part: `stateBefore_stable` moved, the Counter run/step helpers stay open for plan 1c, whose run-extension work generalizes them (Astra P1b-07); note the L*/SA-PC E4 status), `docs/MAP.md`, `docs/CONTRACT.md` (only the stale SA-PC fast-outage line 275-276, if the survey is confirmed), `state.md` is the controller's.
- Create: `docs/PHASE1B-REPORT.md` (controller)

- [ ] **Step 1: Design notes.** Under §2 E4: the relay-condition status (finding 1), the E4 classification per protocol (Grid CO and SA: two permanent HEAD refusals; SA-PC: none; L*: third equivocation and the stored-block proposal wire), WindowMargin as a per-protocol lemma module with a premise on the relay lemmas (not a framework predicate), and that `Eligible` and the run-extension theorem are plan 1c. Under §3: the instance values. Under §6: the Kit libraries.
- [ ] **Step 2: Full build at handoff.** `pgrep -fl lean`; `lake build --wfail` (every default target); `CatalogLock --check` 0; `Registry --check` 0; `CheckFrameworkAxioms` 0; `check-fg.sh` 0; the grep of plan 1a Task 10 Step 3 over the Framework, Registry, Kit and the changed protocol files.
- [ ] **Step 3: CHECKPOINT.** Commit `Framework: plan 1b documents`. The controller writes `docs/PHASE1B-REPORT.md` with the inputs for plan 1c.

---

## Plan 1c (outline; written after plan 1b closes)

- `Eligible (I : Instance) : Prop` with `EmitWellFormed`, `HandlerCoverage`, `Deliverable`, `RelayFeasible`, defined as the hypotheses of the run-extension theorem; its module is locked on first write.
- Kit.Engine: the canonical synchronous scheduler for a general `ProtocolSpec`; append lemmas for `stateBefore`, `readAt` and the `ExecutionValid` fields; the run-extension theorem from every valid prefix; the Counter canonical run as its first instance (replaces `canonical_sleepy`'s hand-built scheduler).
- Eligibility proofs for Grid CO, SA, SA-PC (RelayFeasible uses Task 1's `excludes`); inhabitation runs for every horizon with `η > 0` parameters; certificates, `ProfileCert ac43`, `Candidate` via `candidateOfAc43`, the shared-C SA-PC certificate pair.
- The I1 witness against `Candidate × Eligible` (`clockInst`, and the `excludes := false` variant with delivery).
- `candidateOfAc43 : ProfileCert ac43 I → Candidate I`, with its first consumer (moved from 1b, Claude m8).
- Astra Q8: specify the admissible prefixes and the outstanding delivery obligations, and account for EVERY regime field. The four delivery obligations do not give `RootInjective`; for Grid CO, SA and SA-PC it fails on forks (I9), so an inhabitation run must avoid root collisions (for example an honest synchronous run with no fork), unless I9 is decided first.
- Registry M2/M3, Lock M8 if still open.

## Risks

```text
┌────┬──────────────────────────────────────┬───────────────────────────────────────────┐
│ R  │ Risk                                 │ Response                                  │
├────┼──────────────────────────────────────┼───────────────────────────────────────────┤
│ R1 │ A Grid CO proof relays a faulty HEAD │ Known discharge (both reviews): the two   │
│    │ of an equivocating seat and needs a  │ callers already conclude "∨ equivocates"; │
│    │ handler call (Review Focus 3)        │ `head_excluded_before_equivocates` and a  │
│    │                                      │ case split. Stop rule kept for surprises  │
│ R2 │ A moved Kit file uses a Grid CO      │ Task 0 Step 1: it stays in Grid CO        │
│    │ declaration                          │                                           │
│ R3 │ The SA-PC PC branch of `handles` is  │ Resolved: both reviews checked it; the    │
│    │ not inside `carries`                 │ branch is inside `carries`                │
│ R4 │ FG-SA branch rebase                  │ constraint above; the branch needs a      │
│    │                                      │ rebuild and a lakefile merge              │
│ R5 │ A task shows a CHANGED lock line, or │ stop; a lock change needs its own review. │
│    │ an ADDED line outside Task 4         │ `--check` must print nothing (it exits 0  │
│    │                                      │ on additions)                             │
│ R6 │ The registry family rule changes the │ Task 6 Step 1: the REGISTRY.md diff shows │
│    │ status of an existing row            │ only new rows                             │
└────┴──────────────────────────────────────┴───────────────────────────────────────────┘
```

## Audit disposition

Two reviews ran on the first version (`0d8d995`): Astra (`docs/audit/phase1b-plan-audit-report.md`, REVISE 1/4/4) and a Claude review by DC-simplify's Opus reviewer (`docs/audit/phase1b-plan-claude-review.md`, PASS WITH FIXES 0/3/13). This version applies every finding.

```text
┌──────────────────────────┬──────────────────────────────────────────────────────┐
│ Finding                  │ Disposition                                          │
├──────────────────────────┼──────────────────────────────────────────────────────┤
│ Astra P1b-01 (BLOCKING), │ L* stored-block proposal refusal: finding 4          │
│ Claude M3                │ corrected; Task 2 second `excludes` clause and       │
│                          │ `excludes_proposal_iff`                              │
│ Claude M1                │ `head_excluded_before_equivocates`; case split at    │
│                          │ CrossView:84 and ProposalViewRelay:91; R1 = known    │
│                          │ discharge                                            │
│ Claude M2, Astra Q3      │ premise `∀ u ≤ cutoff, ¬ excluded`                   │
│ Astra P1b-02             │ registry family rule (data binders); rows at G = 1,  │
│                          │ `*_of_pos` forms CONDITIONAL                         │
│ Astra P1b-03             │ MATRIX cells gated by status                         │
│ Astra P1b-04             │ instance column resolves `StrongInstance.toInstance` │
│ Astra P1b-05             │ premise on all five relay lemmas;                    │
│                          │ `proposal_not_excluded`; I9 table reworded           │
│ Astra P1b-06, Claude m2  │ Kit namespace unchanged; no dedupe                   │
│ Astra P1b-07             │ Engine row closed only in part                       │
│ Astra P1b-08, Claude m1  │ findings 1 and 6 reworded                            │
│ Astra P1b-09             │ import boundary stated as a choice                   │
│ Claude m3, m4            │ Task 0: CheckFrameworkAxioms imports; transitive     │
│                          │ imports allowed                                      │
│ Claude m5, m6            │ Task 1 Step 3: run-indexed stability; engineClockx   │
│                          │ deleted                                              │
│ Claude m7                │ Task 1 Files: the callers listed                     │
│ Claude m8                │ `candidateOfAc43` to plan 1c                         │
│ Claude m9                │ I9 table: `propose` sites; minimal-variant note      │
│ Claude m10               │ FG-SA import list completed                          │
│ Claude m11               │ Task 5: qualified names                              │
│ Claude m12               │ MATRIX legend text for `holds`                       │
│ Claude m13               │ `excludes` docstring: scope is well-formed objects   │
│ Claude lock note         │ Global Constraints: `--check` must print nothing     │
│ Astra Q7                 │ `_` binders; "not an eligible candidate" docstrings  │
│ Astra Q8                 │ plan 1c outline: every regime field; RootInjective   │
│ Re-check N1 (MAJOR)      │ FAMILY only for profile-holds with allowlisted,      │
│                          │ witnessed binder types; negative tests               │
│ Re-check N2              │ block-path premise restricted to its proposal wires  │
│ Re-check N3              │ gap rule before the family suffix                    │
│ Re-check N4              │ instance lines: types after leading binders          │
│ Re-check N5              │ stale text fixed                                     │
│ Re-check N6              │ `holds*+cond` profile cells stated                   │
│ Astra re-check P1b-05    │ block-path premise over its proposal wires; caller   │
│                          │ Paths:357                                            │
│ Astra re-check N1        │ exact family rule: full telescope, one allowlisted   │
│                          │ binder, axiom-checked witness; HiddenAssumption test │
│ Astra re-check N2, N3    │ Task 5 row wording; L* summary (N3 = DC N5)          │
│ DC-simplify ruling       │ `holds*` marker on family cells                      │
│ Astra recheck2 (3 minor) │ witness names with `Tests`; KNOWN-GAP (family) →     │
│                          │ gap; `holds*+cond`                                   │
└──────────────────────────┴──────────────────────────────────────────────────────┘
```

## Reviews before execution

This plan changes protocol libraries (Grid CO, SA through Grid CO, L*). Under the rule for this session (user, relayed by DC-simplify 2026-09-29: "act independently; get review from DC-simplify and Astra before big decisions, and a proper audit before really major ones"), it runs only after:
1. a proper independent audit by Astra (`docs/audit/phase1b-plan-audit.md`, xhigh, read-only), and
2. a review by DC-simplify,

with every BLOCKING and MAJOR finding resolved in the plan text and recorded in "Audit disposition" above. DC-simplify re-checks the revision diff against the findings; execution starts after that check passes.
