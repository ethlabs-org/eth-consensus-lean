# FG-SA Model and Store Facts (Composition T3–T6) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task by task. Steps use checkbox (`- [ ]`) syntax for tracking. Gate G0 is closed (Task 0, Step 5: the re-audit r188 of revision 2 gave PASS WITH MINORS; revision 2.1 applies its minors N1–N6). Task 1 can start.

**Goal:** Build the composite FG-SA node model as pure Lean definitions, and prove its store facts. The model is the plain SA base (GridCO/SA state functions) plus the DC-fj FG store of the FG module, with the filtered base (`act(Σ)`), `reconcile_with_finality`, the `F ⋠ B` refusal, the cumulative tree `Σ.T`, `fastWrite` and the FG source `C_fg`. The proofs are: the local carrier bridge K5 and its cross-node form under a NAMED content premise (DQ3); the store facts K1–K4, with K1 in the blueprint form (no fastWrite premise) and K4 with its metadata part; the six items of `bp.activeView.v1`; the SA bridge for the tick AND for a block delivery; acceptance sufficiency for K8; and the store form of output nesting (`comp.outputNesting.v2`, K2). This plan covers tasks T3, T4, T5 and T6 of the composition plan. It has no run layer and no engine binding. Its objects are engine-v1 typed (J1; see "Q1 boundary").

**Architecture:** One new Lake library, `AvailableChainFGSA`, with the SA layout:
- `Model/` (LM): definitions and nothing else. `Objects`, `Store`, `Handlers`, `Clock`, `Frame`.
- `Statements/`: the invariants and the public statements (`Prop` values).
- `Proofs/`: the theorems. `BlockAncestry`, `Carrier`, `Fields`, `ActView`, `Nesting`, `Reconcile`, `Admission`, `StoreInv`, `Metadata`, `CrossNode`.
- `Tests/`: `Smoke` (`decide` examples) and `Axioms` (`#print axioms`).

The composite state keeps the SA base as a `GridCO.State n` value (field `base`) and the FG part as a `SimplexFG.Store (Fin n)` value (field `fg`), as SA-PC keeps `base` (`AvailableChainSAPC/Model/Objects.lean:58`). Every SA read and write runs unchanged on `actView st`, the base with its block list filtered to `act(Σ)`. The stored block list stays cumulative. The FG part changes only through `SimplexFG.on_block`. `reconcile` writes only SA fields. Every function that takes `p : Params` works on `State p.n`, `Wire p.n` and `Fin p.n` (M11). Every auth match is in the decoders of `Objects` (J1).

**Tech Stack:** Lean 4 v4.30.0-rc2 and Mathlib v4.30.0-rc2 (`lean-toolchain`). Lake, the module system (`module`, `public import`, `@[expose] public section`).

**Worktree and branch:** `/Users/francesco/worktrees/available-chain-fgsa`, branch `fgsa-composition` (base `d415a7c`). Do not touch `/Users/francesco/ethereum/lean/available-chain`: another session works there on framework plan 1a.

## Sources

`R/` means `/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/`. `AC/` means this worktree.

```text
┌────────────┬──────────────────────────────────────────────┬──────────────────────────────┐
│ Key        │ File                                         │ Version                      │
├────────────┼──────────────────────────────────────────────┼──────────────────────────────┤
│ spec       │ R/spec/archive/fgsa-protocol-2e884811.tex    │ sha256 2e884811…dc5599adb9787│
│            │ (AUTHORITY for rules and line anchors); the  │ (see note 1); adopted file   │
│            │ adopted R/spec/fgsa-protocol.tex has the     │ sha256 dbcb7f05…             │
│            │ same frozen rules                            │                              │
│ comp       │ R/codex/lean-composition-plan.md             │ sha256 228dbe98…             │
│ bp00       │ R/blueprint/archive/00-outline-03afa5ae.md   │ sha256 03afa5ae… (note 4)    │
│            │ (fixed stage-1 source)                       │                              │
│ bp01       │ R/blueprint/01-foundations.md                │ sha256 989289cc…             │
│ FG plan    │ AC/docs/plans/2026-09-28-fg-module.md        │ branch base d415a7c          │
│ SA, GridCO │ AC/AvailableChainSA, AC/AvailableChainGridCO │ branch base d415a7c          │
│ FG module  │ AC/AvailableChainSimplexFG,                  │ branch base d415a7c          │
│            │ AC/AvailableChainKitFG                       │                              │
│ audits     │ AC/docs/audit/fgsa-model-store-plan-audit-   │ Astra r185, REVISE;          │
│            │ report.md; …-plan-opus-review.md             │ Opus, REVISE (both on 7af69aa│
│            │ …-plan-reaudit-report.md                     │ r188, PASS WITH MINORS (on   │
│            │                                              │ 5801ce6)                     │
└────────────┴──────────────────────────────────────────────┴──────────────────────────────┘
```

Notes:
1. The spec sha256 is `2e88481117ba3e663c559f95218ce545aba5639f201063c1942dc5599adb9787`. Update (G4, 2026-09-29): the spec revision is adopted, and `R/spec/fgsa-protocol.tex` is now sha256 `dbcb7f05106cff51070fc767de45e3fedf45d0c74c8b5aeeca794a6110978864`. Its Complete-protocol section (2e884811 lines 337–1417), its preamble (macros) and its Relay paragraph are byte-identical to `2e884811`; the new file adds a Leak-identification section after the protocol section, and in the model section changes only the R ≥ 3 remark (2e884811 lines 210–214) and the parameter and derived-constant lines (310–332). So the model does not change. Line numbers shift (the protocol section starts at line 442 instead of 337). Rule: `2e884811` stays the line-anchor authority. Every "spec N" in this plan and every `[spec N]` docstring tag is a line of the archive file `R/spec/archive/fgsa-protocol-2e884811.tex`. Do not renumber the docstrings. Its archive copy is identical. In this plan, "spec N" is a line number of that file. A revision is in draft (`R/spec/drafts/fgsa-protocol-next.tex`, identical to the frozen file on 2026-09-28). It changes the recovery premises and adds a leak section. It does not change the store or the state machine. Update (G1, 2026-09-29): the draft now differs from the frozen file (draft sha256 `b62364ae…` on 2026-09-29). Inside the modeled lines (spec 160–1414) the diff changes only the R ≥ 3 remark (spec 210–214; `R ≥ 2` stays the parameter bound) and the symbol rows and derived recovery constants of the parameter section (spec 310–332). The protocol section (spec 337–1417) has no change. The frozen file `2e884811` is unchanged, so this has no effect on the model. The model follows `2e884811` until the coordinator gives a new frozen hash. If a new frozen version appears before execution, diff it against `2e884811`. Report each changed line in a rule that this plan models. Do not resolve a difference yourself.
2. The FG module pins `alfs4` (`bd942ca0`). The diff from `bd942ca0` to `2e884811` has 56 lines. It changes no FG chain transition, client, finality-acceptance or FJ-frame rule, so the old `KitFG/Pins.lean:99–100` spec pin stays usable for that unchanged FG code (with this note as the version bridge; it is not the authority for the composite rules). It changes three things that this plan models: (a) no rule deletes a block of `Σ.T` (spec 372–377; the FG module and this plan keep the cumulative tree); (b) the signatures of an admitted proposal count in the HEAD merge through the proposal, also when the proposal leaves the active view (spec 190–193); (c) the carried-support arm of the HEAD merge tests `H' ∈ Σ.T`, not `act(Σ)` (spec 423–429).
3. The composition plan cites `bd942ca0` line numbers. This plan cites `2e884811` line numbers.
4. bp00 full sha256: `03afa5ae814606ac7c75525766f8b17926616a8e858b26deef1a59152fb64ad5`. Revision 1 of this plan pinned `6057f9b5`; that version is archived as `R/blueprint/archive/00-outline-6057f9b5.md`. The diff (checked 2026-09-28) changes only §2.5 (later-stage constants, lines 326–386), §3.4 (stage-2b healing statements) and the §3.5 negatives text. §2.1–2.4, §3.1 and §3.2 are unchanged. Every id that this plan pins exists in the current file: `bp.carrier.v1` (line 410), `bp.store.v1` (433), `bp.activeView.v1` (446), `bp.leaseOrigins.v1` (455), `bp.reconcile.v1` (465), `comp.outputNesting.v1` (475), `comp.outputNesting.v2` (480), `bp.frame.v1` (487), `bp.sourceDiscipline.v1` (530), `bp.receiptCoverage.v1` (541). bp00 §2.4 (tree reads) is at lines 188–214; §3.1 is at lines 408–555. bp01 is not changed.
   Revision 2.1 (re-audit r188, N1): the fixed stage-1 source is the verified archive copy `R/blueprint/archive/00-outline-03afa5ae.md` (sha256 `03afa5ae…`, as above). All bp00 line numbers in this plan refer to that file. After revision 2, the current `R/blueprint/00-outline.md` changed to sha256 `5a89d1687ba093643cabe7e7d69e232ef7f234f1809511269a2b5e4f6925fb91`. Its diff from `03afa5ae` changes later recovery bounds and first-finality results. It does not change the stage-1 statements that this plan uses (r188). Task 0 checks the hash of the archive copy, not of the current file.

Spec lines that this plan models:

```text
┌──────────────────────────────────────────┬────────────────┐
│ Rule                                     │ spec lines     │
├──────────────────────────────────────────┼────────────────┤
│ relay, receiver exclusion, distinct roots│ 160–193        │
│ schedule, a_r = d_{rR}, rows, blocks,    │ 197–263        │
│ well formedness, deepest tie rule        │                │
│ parameters                               │ 265–335        │
│ store tuple, Trees, act(Σ)               │ 339–379        │
│ block states, FG caches                  │ 381–412        │
│ pools (vote, row), resolution            │ 414–439        │
│ SA fields, fastWrite                     │ 441–461        │
│ reconciliation (prose)                   │ 474–484        │
│ initialization                           │ 486–503        │
│ input validation, acceptance, inclusion  │ 505–556        │
│ outputs, F ⪯ S                           │ 558–575        │
│ HEAD view, frame, walk start, FG action  │ 598–681        │
│ tick order                               │ 683–694        │
│ on_tick, expire, release                 │ 709–752        │
│ update_confirmation, advance, outputs    │ 754–802        │
│ on_block, on_goldfish_vote,              │ 804–857        │
│ on_attestation                           │                │
│ update_finality, reconcile               │ 859–894        │
│ resolution_time … get_head               │ 973–1114       │
│ SA gate helpers                          │ 1118–1206      │
│ duties (voter tree … get_fg_vote)        │ 1210–1338      │
│ client                                   │ 1342–1414      │
└──────────────────────────────────────────┴────────────────┘
```

## Scope and user decisions

This plan does the composition-plan tasks below (comp §7.1, lines 496–549). The composition plan is the design; the blueprint gives the statements and paper proofs (bp00 §3.1, bp01 §§2, 4–7, 10.1).

```text
┌──────┬──────────────────────────────────────────┬──────────────────────────────┐
│ comp │ Content                                  │ Tasks of this plan           │
├──────┼──────────────────────────────────────────┼──────────────────────────────┤
│ T3   │ Model (LM), comp §4.2–4.6, smoke tests   │ 1, 3, 4, 5, 6                │
│ T4   │ Carrier bridge K5: local algebra (2);    │ 2, 12                        │
│      │ cross-node form under ContentAgree (12)  │                              │
│ T5   │ Store facts K1–K4 (K4 with metadata);    │ 7, 9, 10, 11, 12             │
│      │ base = Σ.T erased; actView laws (six     │                              │
│      │ items); SA bridges; F monotone; K8       │                              │
│      │ acceptance sufficiency                   │                              │
│ T6   │ Output nesting, store form (K2)          │ 8                            │
└──────┴──────────────────────────────────────────┴──────────────────────────────┘
```

What this plan does NOT complete: the run form of T6 (nesting over a run), the run premise that gives `ContentAgree` for honest stores (DQ3), the hooks binding, and every other run lift. They are T7 inputs (Task 13 report). Comp T4 is complete here only in the store-pair form: the cross-node lemmas take `ContentAgree` as a hypothesis.

User decisions that this plan uses:

```text
┌────┬────────────────────────────────────────┬────────────────────────────────────┐
│ Q  │ Status                                 │ Effect on this plan                │
├────┼────────────────────────────────────────┼────────────────────────────────────┤
│ Q1 │ OPEN (engine v1 or v2)                 │ No ProtocolSpec, no Run, no hooks  │
│    │                                        │ binding, no Λ field, no pendingRow.│
│    │                                        │ BUT the objects are v1-typed       │
│    │                                        │ (Auth, Signed; J1). On v2, T7 adds │
│    │                                        │ a decode adapter v2 object → Wire  │
│    │                                        │ p.n (keeps the internal API), or   │
│    │                                        │ re-types the objects natively (T7  │
│    │                                        │ sets its scope; r188 N5). See "Q1  │
│    │                                        │ boundary".                         │
│ Q2 │ Clean first                            │ No effect on T3–T6. K1 and the SA  │
│    │                                        │ compatibility invariant feed (b1). │
│ Q3 │ ANSWERED: FG module re-pinned on the   │ K4 core is short: the FG part IS a │
│    │ filtered base (fj.frame.v3, one tree)  │ SimplexFG.Store value, changed     │
│    │                                        │ only by on_block. No raw-tree      │
│    │                                        │ correspondence. The metadata part  │
│    │                                        │ of K4 is new (Task 12).            │
│ Q4 │ DONE (blueprint)                       │ Statements follow bp00 §3.1 and    │
│    │                                        │ bp01 §§2, 4–7, 10.1.               │
│ Q5 │ OPEN (additive companion)              │ No dependency. No Interface, no    │
│    │                                        │ Claims, no contract bundle.        │
└────┴────────────────────────────────────────┴────────────────────────────────────┘
```

### Q1 boundary

These items depend on the engine version. This plan does not define them, except the first row, which it defines in the v1 form. Composition task T7 binds them after Q1.

```text
┌──────────────────────────────────────┬─────────────────────────────────────────┐
│ Deferred item                        │ What this plan gives instead            │
├──────────────────────────────────────┼─────────────────────────────────────────┤
│ object types (J1): Auth Label n with │ v1 types, and ONE place that reads an   │
│ .proposer s and a global n; Signed   │ auth: HeadWire.decode?, RowWire.decode?,│
│ (FRAMEWORK E1 on v2: Auth = seat ℓ   │ Wire.decode (Task 1). Handlers, checks, │
│ (i : Fin (seats ℓ)) | none; no       │ round?, toRow?, baseHead read wires only│
│ global n; proposal = one-seat label) │ through them. v1: no change in T7. v2   │
│                                      │ (r188 N5): a decode adapter v2 object → │
│                                      │ Wire p.n keeps the internal API: Store, │
│                                      │ Statements and Proofs stay. A native    │
│                                      │ re-typing is NOT limited to Objects and │
│                                      │ its decoders: handlers build .seat s i  │
│                                      │ and .proposer s wires, proposalRows     │
│                                      │ compares .auth values, and the SA base  │
│                                      │ (GridCO.State) stores v1 wires. T7 sets │
│                                      │ the scope of a native re-typing.        │
│ ProtocolSpec fgsa, duties, act       │ pure duty functions headVote, propose,  │
│                                      │ attest (Task 6)                         │
│ where Λ lives; when Λ is recorded    │ attest takes Λ and returns (row, Λ′);   │
│ (v1: at the clock tick; v2: E5)      │ State has no Λ field (DQ4)              │
│ own row processed at once (spec 681) │ admitRow is a plain handler (Task 4)    │
│ signer identity of a row (LinkedFG   │ the row signer is the seat index of the │
│ premise on v1; E2 on v2)             │ fg-label signature (RowWire.decode?)    │
│ hooks excludes, handles, depsPresent,│ the store predicate blockExcluded and   │
│ processed, carries                   │ its stability lemma (Tasks 3, 7);       │
│                                      │ wellFormed as a pure input check; for a │
│                                      │ proposal, processed is "root in Σ.T"    │
│                                      │ (DQ9)                                   │
│ run form of nesting, all run facts   │ Reachable closure of the local steps    │
│ content premise ContentRootInjective │ the store-pair form ContentAgree and    │
│ (DQ3)                                │ the cross-node carrier (Task 12)        │
└──────────────────────────────────────┴─────────────────────────────────────────┘
```

## Review status

REVISION 2, 2026-09-28. Revision 1 (`7af69aa`) had two independent audits:

- Astra r185, `docs/audit/fgsa-model-store-plan-audit-report.md`: REVISE (B1; M1–M6; N1–N5).
- Opus, `docs/audit/fgsa-model-store-plan-opus-review.md`: REVISE (B1 confirmed with the compiler; J1–J3; agrees with M1–M6 with two refinements, M3 as a local invariant and M5 as the direct-import rule; minors m1–m8).

This revision applies every blocking, major and minor finding, or records a reasoned rejection. The table "Disposition of audit findings" at the end maps each finding to its change. Both verdicts were REVISE, so G0 needs a second audit of the changed sections (Task 0, Step 5) before Task 1.

REVISION 2.1, 2026-09-29. The second audit of revision 2 (`5801ce6`):

- Astra r188, `docs/audit/fgsa-model-store-plan-reaudit-report.md`: PASS WITH MINORS (0 blocking, 0 major; minors N1–N6). All earlier blocking and major findings are closed. The report maps to G0's older term ADOPT WITH FIXES. This closes G0.

Revision 2.1 applies N1–N6 (record and interface corrections; no design change). The table "Disposition of the re-audit findings" at the end maps each one to its change.

Compiler checks of this revision (scratch file `/private/tmp/fgsa-rev2/Check.lean`, outside the repository, `lake env lean` from the worktree root; a negative control confirmed that the file elaborates):

```text
┌──────────────────────────────────────────────┬──────────────────────────────┐
│ Check                                        │ Result                       │
├──────────────────────────────────────────────┼──────────────────────────────┤
│ controls (p) (st : State p.n) with p.E       │ OK                           │
│ a `State 4` fixture where `State pT.n` is    │ OK (pT is an abbrev; defeq)  │
│ expected; `decide` on a field                │                              │
│ Wire.decode, RowWire.decode?, RowWire.valid, │ OK; height 0 fails in both   │
│ wellFormed (p) (o : Wire p.n): the same row  │ forms, height 1 passes in    │
│ alone and in a block                         │ both (decide)                │
│ deepest with the tie rule (greater root)     │ OK; decide picks the greater │
│ through pickPair                             │ root at equal depth          │
│ DQ10 collisions of the GridCO root formula   │ decide: honest fork          │
│                                              │ root(g,4) = root(g1,2) = 4;  │
│                                              │ adversarial: a faulty slot-7 │
│                                              │ block with fresh root 7 gives│
│                                              │ its honest slot-8 child the  │
│                                              │ root 64 of the honest slot-4 │
│                                              │ block                        │
└──────────────────────────────────────────────┴──────────────────────────────┘
```

The Opus scratch files (`/private/tmp/fgsa-rev/`) already showed the `LeasePolicy` trap and `actView_onView`; this revision did not repeat them.

## Global Constraints

- Toolchain and Mathlib v4.30.0-rc2. Do not run `lake update`.
- Committed proofs use no `sorry`, no `admit`, no project axioms and no `native_decide` (also no `decide +native`, no `ofReduceBool`). A `sorry` body is allowed only between the statement step and the CHECKPOINT of one task. `lake build --wfail` fails on `sorry`. `scripts/CheckFGSAAxioms.lean` (Task 2) rejects every axiom outside `propext`, `Classical.choice`, `Quot.sound`. `scripts/check-fgsa.sh` (Task 1) scans for native evaluation outside comments.
- Kernel checks use `decide`, `decide +kernel`, `decide_cbv` or `rfl`. If `decide` is slow on a smoke test, first make the test a `Bool` value (`def t : Bool := …` and `example : t = true := by decide`, as `AvailableChainSA/Tests/Smoke.lean`), then try `decide +kernel`. Report each fallback. A `Bool` form does not cure a type error.
- New code goes only in the new library `AvailableChainFGSA`, in new scripts `scripts/check-fgsa.sh` and `scripts/CheckFGSAAxioms.lean`, in one appended `[[lean_lib]]` block of `lakefile.toml`, and (Task 13) in `defaultTargets` and one new section of `docs/MAP.md`. Do not edit any file of another library. Do not edit `docs/FG-COMPOSITION.md`, `docs/FRAMEWORK-DESIGN.md`, the FG scripts, or `decoupled-consensus/`.
- Imports (M5, Opus route). No file of `AvailableChainFGSA` DIRECTLY imports `AvailableChainFramework`, `AvailableChainRegistry`, `AvailableChainStatements`, `AvailableChainWitnesses` or `AvailableChainSAPC`. The allowed direct imports are: `AvailableChainModel.*`, `AvailableChainGridCO.Model.Protocol`, `AvailableChainGridCO.Proofs.*` (in `Proofs/` only), `AvailableChainSA.Model.Protocol`, `AvailableChainSimplexFG.*`, `AvailableChainKitFG.*` (in `Statements/` and `Proofs/` only), and Mathlib. Import the smallest module that has the declaration.
  - Disclosed transitive dependency: every `AvailableChainGridCO.Proofs.*` module that this plan uses (`Map`, `History`, `Basic`, `RecordSlots`, `GenuineHistory`, `Roots`) reaches `AvailableChainStatements` through `GridCO/Proofs/Basic.lean:2` → `GridCO/Statements/Contract.lean:3` → `AvailableChainStatements.Generic.Claims`. This is allowed: plan 1a does not change `AvailableChainStatements` (`docs/plans/2026-09-28-phase1a-gate-catalog.md:65`). The closure of these modules reaches no module of `AvailableChainFramework`, `AvailableChainRegistry`, `AvailableChainSAPC` or `AvailableChainWitnesses` (checked 2026-09-28 from the source import lines). `scripts/check-fgsa.sh` checks both rules: from G13 (Astra M2, Opus m1) the direct rule is this allowlist with its directory rules on parsed import headers (comments and line breaks handled), and the closure rule and build coverage are checked on the compiled import graph by `scripts/CheckFGSAAxioms.lean`. Do not copy GridCO lemmas into this library to avoid the transitive dependency.
- Model files (`Model/`) hold definitions only. No theorem with a proof goes in `Model/`. Examples go in `Tests/Smoke.lean`. `Statements/` holds invariant definitions and `Prop` statements. `Proofs/` holds the theorems (lean/AGENTS.md: keep executable definitions, public statements and proofs apart).
- Namespace `AvailableChain.FGSA` for `Model`, `Statements` and `Proofs`; `AvailableChain.FGSA.Tests` for `Tests`.
- Every new `.lean` file of the library starts with `module`, the `public import` lines, a blank line, `@[expose] public section`, a blank line, `namespace …`. It ends with `end …` then `end`. Exception: `scripts/CheckFGSAAxioms.lean` is an executable script; it keeps the `import`/`def main` form of `scripts/CheckFGAxioms.lean`.
- Parameter indexing (M11; audit B1). Every definition, statement and theorem that takes `p : Params` uses `State p.n`, `Wire p.n`, `RowWire p.n`, `HeadWire p.n` and `Fin p.n`. A definition keeps a free `{n : Nat}` only if it does not take `p` (for example `eraseFG`, `actView`, `onView`, `normalizeS`, `reconcile`, `leaseOf`, `fastWriteAt`, `blockExcluded`, `parentFG`, `fgBlock`, `deepest`). Do not add a cast or an equality premise `n = p.n`. Test fixtures are typed `State 4` or `State pT.n`; the two are the same type (`pT` is an `abbrev`).
- Root imports. Each task that creates a `.lean` file adds `public import <module>` to `AvailableChainFGSA.lean` in the same commit. At each CHECKPOINT this must print nothing:
  `comm -23 <(find AvailableChainFGSA -name '*.lean' | sed 's/\.lean$//; s|/|.|g' | sort) <(grep -o 'import [A-Za-z.]*' AvailableChainFGSA.lean | sed 's/import //' | sort)`
- Builds. The Mac `lean` has 3 machine-wide slots (`LEAN_SLOTS=3`). Before each build run `pgrep -fl lean`; if 3 compiles run, wait (use `ps -o etime,%cpu -p <pids>` to tell a slow build from a blocked one). During a step, build one module: `lake build --wfail AvailableChainFGSA.Model.Store` (module targets build only that module and its imports). At each CHECKPOINT: `bash scripts/check-fgsa.sh`, which builds the library once; do not run a second identical `lake build` before it. At Task 13 only: the full project target `lake build --wfail`. Do not add a `lean_exe` target. Run scripts with `lake env lean --run <file>.lean`.
- Faithfulness. The spec is the authority. Each model definition has a docstring that names its spec lines, for example ``[spec 804–829]``. A proof docstring names its blueprint id and K id, for example ``[bp bp.reconcile.v1; K3]``, or ``[helper]``. Do not change a statement to make a proof pass. A difference from the spec, the blueprint or the composition plan is a finding: report it in the task report and do not resolve it.
- `LeasePolicy` instances (Opus §1, compiled). `SA.gate` and `SA.clock` are `@GridCO.gate GridCO.slowLeasePolicy …` and `@GridCO.clock GridCO.slowLeasePolicy …`. The DEFAULT instance is `gridLeasePolicy` (`GridCO/Model/Protocol.lean:17`). So `GridCO.gate_blocks p.engine v r` elaborates silently for the GRID gate and does not match `SA.gate`. Rule (r188 N3): inspect the actual declaration (`#check @GridCO.<lemma>`). If it has a `[LeasePolicy]` argument and it is used for the SA base, apply it as `@GridCO.<lemma> GridCO.slowLeasePolicy p.toParams.engine …`. The surrounding `variable [LeasePolicy]` of a file does not decide this: Lean omits an unused section variable from a declaration. Correction (G11 M1, `#check`): `GridCO.admitVote_blocks`, `GridCO.confirmation_mem` and `GridCO.ghostWalk_mem` DO have a policy argument (`∀ [GridCO.LeasePolicy] …`), as `gate_blocks` and `gate_target_origin` do; a section `variable [LeasePolicy]` is included when the file does not let Lean omit it. So `#check @GridCO.<lemma>` decides, never the file's `variable` line. `scripts/CheckFGSALease.lean` (run by `check-fgsa.sh`, with a negative control) checks every use in the compiled FGSA constants. A reviewer rejects a proof that uses a lease-dependent GridCO lemma without the explicit instance.
- Leak-ledger readiness. A later revision adds a leak ledger as a DERIVED function of the chain (`R/codex/round-leak.md`: "All snapshots and charges are derived from the chain"; the ledger "does not change weights"). So: the model stores no derived value that the spec does not store, except the declared model-only caches below; `σ[B]` stays `SimplexFG.derive E cfg B` (never a cached field); each FG block keeps its full ordered row list; the stored proposals keep the full signed rows with their rounds; the electorate stays a parameter. Then `leakLedger : FGBlock (Fin n) → …` can be added in a new file without a change to `State` or to a handler.
- Model-only caches (Opus m6; DQ8). The SA base has five fields that the spec store does not have: `frozen`, `early`, `releaseSnapshots` (the spec derives the frozen and early pools at read time, spec 463–471, and its `on_tick` has no freeze or early step, spec 709–730), `goldfishRecord` (G; the spec has no G) and `base.proposals` (the GridCO copy of the admitted wires; the composite reads `st.proposals`). They stay because the exact SA bridge (Task 7) needs the SA step shape. No FG-SA duty, output or statement reads them. A reviewer checks this in Task 6 (G6) and Task 13. In particular (G3 minor 4), `frozen` holds saved resolved pools and a frozen block domain, and `reconcile` does not clear them. GridCO `act`, `voterView`, `voterSupportView` and `voterTree` read `frozen`, so no composite duty may reuse them.
- Q1/Q5 independence. No file of this plan mentions `ProtocolSpec`, `Run`, `World`, `Env`, `Interface`, `Claims`, `pendingRow` or an engine field. `grep -rnE 'ProtocolSpec|Generic\.Run|World|pendingRow' AvailableChainFGSA` must print nothing at each CHECKPOINT. From G13 (Opus m5), `check-fgsa.sh` greps the comment-free text for these words and also for `Run`, `Env` (whole words), `Interface` and `Claims`. The v1 object types are the one declared engine dependency (J1).
- Each task ends at a CHECKPOINT:
  - `bash scripts/check-fgsa.sh` exits 0 (from Task 1; it builds the library; from Task 2 it also runs the axiom check);
  - the root-import check and the Q1/Q5 grep print nothing (the script runs both);
  - the independent review gate of the task is passed (see "Review gates");
  - the task is committed on `fgsa-composition` with the message `FGSA model: <task title>` (Tasks 1–6) or `FGSA store: <task title>` (Tasks 7–13), and only the task's files are staged. Each commit message ends with the attribution line of the executing session.
- Shared files (audit N5). `AvailableChainFGSA.lean`, `Tests/Smoke.lean` and `Statements/*.lean` have ONE writer at a time. The only parallel pair is Task 2 with Tasks 3–6; Task 2 does not edit `Tests/Smoke.lean` or `Statements/`, and its one root-import line is added by the coordinator at the Task 2 commit. All other tasks run in the order of the task list.
- Prose in comments and docs: ASD-STE100 Simplified Technical English. Tables: Unicode box drawing in fenced `text` blocks.

## Design decisions of this plan

These decisions refine comp §4. Each one names what it changes in comp §4, if anything.

```text
┌─────┬───────────────────────────────────┬────────────────────────────────────────────┐
│ ID  │ Decision                          │ Reason                                     │
├─────┼───────────────────────────────────┼────────────────────────────────────────────┤
│ M1  │ base : GridCO.State n (cumulative │ comp D2, D3. GridCO proofs need a growing  │
│     │ erased Σ.T); fg : SimplexFG.Store │ block list (ReceiptPrefix). K4 core is the │
│     │ (Fin n) (the FG caches and Σ.T)   │ FG module's own StoreInv (Q3 answered).    │
│ M2  │ actView st = base with blocks     │ comp §4.2 last item; spec 363–366.         │
│     │ filtered to compatibility with    │ resolvedBefore, confirmation, gate,        │
│     │ eraseFG F; onView f runs a GridCO │ release, prefix support then read act(Σ)   │
│     │ step on actView and restores the  │ with no change to SA code. Limit (J3): a   │
│     │ cumulative block list             │ GridCO invariant proved by induction over  │
│     │                                   │ GridCO steps (ReceiptPrefix, "every block  │
│     │                                   │ has a stamp") applies to base, not to the  │
│     │                                   │ view: the view's list shrinks when F moves │
│     │                                   │ and keeps the stamp rows of inactive       │
│     │                                   │ blocks.                                    │
│ M3  │ The proposal wire carries the     │ comp §4.2 Msg. The FG block is built at    │
│     │ erased Block b, the vote lists    │ admission from the stored parent (spec     │
│     │ and its own signed rows; the FG   │ 519–522). Locally sound; across nodes it   │
│     │ block is .node P b.slot b.root    │ needs the content premise (DQ1, DQ3).      │
│     │ rows′ with P the stored parent    │                                            │
│ M4  │ A row wire is Signed Label n      │ spec 230–237: a = (valindex, round, …).    │
│     │ RowBody with auth .seat (.fg r) i:│ The round is the label; the identity is    │
│     │ round r, identity i : Fin n. All  │ the seat index (comp D5). How i binds to a │
│     │ auth matching is in the decoders  │ validator is a run premise (Q1). One       │
│     │ HeadWire.decode?, RowWire.decode?,│ decode place makes a v2 adapter local (J1).│
│     │ Wire.decode (J1)                  │                                            │
│ M5  │ The duplicate test of on_block    │ spec 167, 521: roots are distinct. With    │
│     │ refuses a block whose ROOT is     │ this test Σ.T is root-injective by         │
│     │ already in Σ.T                    │ construction; ViewRootInj Σ.T follows with │
│     │                                   │ no hypothesis. This is LOCAL; it gives no  │
│     │                                   │ cross-node content equality (DQ2, DQ3).    │
│ M6  │ reconcile runs inside the         │ comp D7; spec 867–871. It writes only SA   │
│     │ accepted branch of admitBlock,    │ fields and S.                              │
│     │ right after on_block, when F      │                                            │
│     │ changed; the row handlers run     │                                            │
│     │ after it                          │                                            │
│ M7  │ The composite gate: evaluate once │ spec 756–781 (the "s ∉ dom genuine" test   │
│     │ (skip if the label is saved);     │ and the final S rule). SA.gate already     │
│     │ SA.gate on actView; fastWrite[s]  │ writes genuine once (recordGenuine under   │
│     │ from the fast test, also empty;   │ slowArming); the composite guard also      │
│     │ then S := F if F ⋠ S              │ skips the S, G, lease and fastWrite        │
│     │                                   │ writes. See DQ5.                           │
│ M8  │ The clock follows GridCO.clock    │ SA-PC precedent (AvailableChainSAPC/Model/ │
│     │ step by step: expire on base;     │ Protocol.lean:48). clockPre is the tick    │
│     │ freeze, early, release on         │ before the gate, so that the bridge can    │
│     │ actView (clockPre); then the      │ name the exact fastWrite set (m1). The     │
│     │ composite gate                    │ freeze and early caches are model-only.    │
│ M9  │ Duties are pure functions of the  │ comp §4.5; spec 1210–1338. The HEAD reads  │
│     │ state; they read the live frame   │ resolution at read time (spec 429–430).    │
│     │ storeControls and derive every    │                                            │
│     │ pool from stamps at read time     │                                            │
│ M10 │ No Λ field and no pendingRow      │ spec 352–353 (Λ is not part of the store); │
│     │                                   │ Q1. See DQ4.                               │
│ M11 │ Every p-dependent definition and  │ audit B1 (compiled): storeControls p.E on  │
│     │ statement is indexed by p.n       │ a Store (Fin n) with a free n is a type    │
│     │                                   │ error. One consistent API, no casts.       │
│ M12 │ One row check RowWire.valid       │ spec 234–237, 505–518; audit M1. The same  │
│     │ (body: empty, or a vote with      │ row passes or fails in both delivery       │
│     │ h ≥ 1) for a row alone and for    │ forms. wellFormed is the complete input    │
│     │ every row that a block carries    │ check; process stays separate from it, as  │
│     │                                   │ in the spec (DQ14).                        │
│ M13 │ Inherited FG reductions, declared │ Astra coverage note. The FG module omits   │
│     │                                   │ σ.nj (always false in this spec: spec 501, │
│     │                                   │ 940–960), so its client uses the false-ν   │
│     │                                   │ branch; Record omits Λ.timeouts (written,  │
│     │                                   │ never read: spec 1409–1411). attest is a   │
│     │                                   │ projection of the client, not a full       │
│     │                                   │ record equality.                           │
└─────┴───────────────────────────────────┴────────────────────────────────────────────┘
```

## Open design questions

Each question has a recommended answer. The plan follows the recommendation. Both audits agree with DQ1–DQ12 under the conditions given here. The second G0 audit (r188) accepted DQ1–DQ14 with the corrections N1–N6. The user can still change an answer.

- **DQ1. Block wire form.** (a) Flat: the wire carries the erased `Block b` and its own rows; the FG block is built from the stored parent (M3; comp §4.2). (b) Recursive: a new inductive `FullBlock n` with full rows at every ancestor, and two projections `fg` and `erase` (bp01 §2.1). **Recommendation: (a).** The HEAD walk and the proposer work on erased blocks (`GridCO.ghost`), so the proposer's parent is an erased block in both forms, and (b) needs a lookup anyway. (a) keeps one erasure (`eraseFG`), and the local K5 is about `eraseFG` only. The rows of stored blocks stay available with their rounds in `st.proposals`. The blueprint's `eraseFG (fg B) = erase B` becomes `eraseFG (fgBlock P b rows) = b` (Task 10, `eraseFG_fgBlock`). Condition (audits): `eraseFG_fgBlock` is necessary but it does not give a common meaning of a parent across nodes. That needs the content premise of DQ3 and the cross-store reconstruction of Task 12. The flat wire carries the full erased parent chain, which is more than the spec's root reference; the two agree under `RootInjective`, because `BlockInRun` holds all ancestors.
- **DQ2. Duplicate test.** (a) By root: refuse if some `Y ∈ Σ.T` has `Y.root = b.root` (M5). (b) By erased block: refuse if `b` is in the base list, and carry `ViewRootInj Σ.T` as a hypothesis of every store lemma. **Recommendation: (a).** Under the spec's root idealization (spec 167, 521) the two tests agree. (a) makes `Σ.T` root-injective by construction, so `KitFG.storeInv_on_block` gets its `ViewRootInj` premise from the invariant, and no store fact needs a collision hypothesis. With (b), a same-root, different-parent block breaks root injectivity of `TF`, and `lexMax`, `pickPair` and `storeInv_on_block` become conditional in every store lemma. The price of (a): a faulty block with a reused root is refused even if its content is new. That is outside the spec's model. At run level, `RootInjective` (on erased blocks; genesis and the ancestors of every processed or emitted payload) makes the extra refusal never fire for ANY processed block, honest or faulty (Opus m4); every AC regime (`SleepyRegime`, `OutageRegime`, `RecoveryRegime`, `AvailableChainStatements/Generic/Regimes.lean:19,49,75`) contains that premise. Task 10 proves the local form `rootTest_iff_blockTest`, and Task 11 proves that the base list satisfies GridCO's `RootInjectiveBelow`. Local freshness does NOT give cross-node content equality: two nodes can admit the same erased block with different rows (audit M2). That is DQ3, not DQ2.
- **DQ3. Content-bound roots (comp D4).** (a) A model check `b.root = code(parent root, slot, rows)` (comp D4). (b) No model check; a named content premise. **Recommendation: (b).** This REVERSES comp D4, which says "No new run premise is needed". Under (b) there IS a new premise, and every FG-SA claim that compares FG state across nodes must list it (comp T8, T10, T12; Task 13 report). The premise:
  - Store-pair form, in this plan (`Statements/Invariants.lean`, Task 12): `ContentAgree st st'`: two stored proposal wires whose blocks have equal roots have the same erased block (with its parent chain) and the same ordered signed rows (with their rounds). Narrowed at G12 (coordinator decision, option (a)): the first form also asked for equal raw votes and support lists, which no cross-node proof reads and which no I9 root design (a root code over parent root, slot and nonce, with a row code) can supply; the narrower premise is weaker and the four theorems are stronger.
  - Run form, for T7: `ContentRootInjective`: over genesis and every proposal payload that the run processes or emits (honest or faulty), with all ancestors, equal roots of the erased blocks give equal payloads. T7 derives `ContentAgree st st'` for every two honest stores of a run from it, with the metadata invariant (Task 12) and the run lemma "every stored wire is a payload that the node processed" (G12).
  - Obligations that this plan discharges under `ContentAgree` (Task 12): cross-store reconstruction (a stored FG block at one node and a stored FG block at another node with the same erasure are equal) and row-position correspondence (the FG rows are `rows.filterMap RowWire.toRow?` of the stored wire, and a checked row list loses no occurrence: Task 10, `toRow_forall₂`).
  - Reason for (b): a code check needs an injective `Nat` encoding of rows and votes and makes every smoke-test root a computed code. Composition task T1 already asks the registry for the content-root idealization. See DQ10 for the cost of (b): the root premise is then a real restriction, not only collision resistance.
- **DQ4. Where Λ lives.** (a) Not in `State`; `attest` takes `Λ` and returns `(row, Λ′)`; T7 defines the node state (for example `structure NodeState extends State n where record : Record`). (b) A `record` field in `State`. **Recommendation: (a).** Spec 352–353 says Λ is not part of the store. `SimplexFG.Record` holds functions, so a `State` with it has no `Repr`. The choice of the write point (v1 clock tick or v2 `recordOwn`) is Q1. The record/emission order and the own-row admission (spec 681) stay mandatory T7 obligations. (a) agrees with FRAMEWORK v2 E5: `recordOwn` does not change `base`.
- **DQ5. Evaluate-once guard at the gate.** (a) The composite gate skips the SA gate when `savedGenuine st.base s` is `some _` (spec 756). (b) Call `SA.gate` always, as SA does. **Recommendation: (a).** It is the spec text. It also makes `fastWrite[s]` "created once" (spec 458–460). Correction (Opus m5): `SA.gate` is not without a once-guard: `recordGenuine` under `slowArming` already writes `genuine` only once (`GridCO/Model/Protocol.lean:441–446`). The composite guard adds the skip of the S, G, lease and fastWrite writes. An empty or vetoed label stays evaluated. On a run with one tick per public time the two agree. Task 7 proves `clock_eq_saClock_gate` with the premise "the label is not saved" (`hnew`). For T7: `ScheduleWellFormed` (`nodup`, `tick_public`) gives one tick per node and public time, and only the tick at `gateTime s` writes label `s`, so `hnew` is easy. Caveat for v2: a restart (`restore`) that loses `genuine` would allow a second evaluation.
- **DQ6. HEAD block view.** (a) Compute the spec's `voter_processed_block_tree` from `Σ.T` and the base block stamps at read time. (b) Read GridCO's `frozen` block cache. **Recommendation: (a).** It is the spec form (spec 1219–1226). The freeze cache holds only active blocks at `z_{s−1}`; (a) and (b) give the same filtered tree because F only grows and the filter requires `F ⪯ B`, but that is a lemma that no task needs. No duty reads a frozen resolved flag.
- **DQ7. Output-nesting reading for T6.** The task text says "F ⪯ S ⪯ available". **Recommendation:** read it as `comp.outputNesting.v2` (bp00 §3.1): at every reachable state `F ⪯ S`, and both available accessors (`confirmed`, `stable`) equal S. The spec has no third output (spec 558–569). Task 8 also proves the accessor form `comp.outputNesting.v1`. The accessor conjuncts are `rfl`. The stored theorem does not assert global safety or S monotonicity. Comp T6 is complete only after the T7 run lift.
- **DQ8. The SA record G (`goldfishRecord`) and the other model-only caches.** The spec has no G. SA keeps it. **Recommendation:** keep the field (the SA gate writes it through `onView`); `reconcile` does not touch it; no FG-SA output reads it. The same holds for `frozen`, `early`, `releaseSnapshots` and `base.proposals` (Global Constraints, "Model-only caches"). Report them as declared model fields, not spec rules.
- **DQ9. Hooks.** **Recommendation:** define no engine hook in this plan. Give the store predicate `blockExcluded` (DC `NamedReceipt.excludes`: a proposal block incompatible with F) and prove its stability (Task 7). Give the spec input check as the pure function `wellFormed` (Task 4). T7 binds both. For T7 (Opus m3): define `processed` for a proposal by root (`∃ Y ∈ Σ.T, Y.root = b.root`), so that the DQ2 refusal is "already processed" and not a permanent refusal without a report. On a checked wire, the refusals of `blockAccepted` are then only: temporary (future slot, missing parent), duplicate (root), and `F ⋠ B` (Task 10, `blockAccepted_of_wellFormed`). This helps the E4 outcome classification on v2 (`RelayFeasible`).
- **DQ10. Honest proposal root.** **Recommendation:** keep the GridCO formula `⟨s * (parent.root.value + 1)⟩` (`GridCO.propose`, `GridCO/Model/Protocol.lean:292`) in this plan, and state its limit. The formula is not a content encoder, and it collides (compiled, Review status):
  - Honest fork: `node(genesis, 4)` and `node(node(genesis, 1), 2)` both get root 4. An honest slot-4 proposer that has not received the slot-1 and slot-2 blocks (asynchrony before GST, or an outage) builds on genesis and makes this collision.
  - Adversarial: the honest chain of slots 1–4 has roots 1, 4, 15, 64. A faulty slot-7 block with the fresh root 7 makes its honest slot-8 child get root `8·(7+1) = 64`, the root of the honest slot-4 block. A faulty proposer that otherwise follows the protocol can do this in any regime.
  - Consequence: `RootInjective` and `ContentRootInjective` (DQ3) can fail on a run because of honest proposals, and a faulty proposer can make them fail on purpose. Every theorem with that premise is vacuous on such a run. On a single honest chain the roots strictly increase (`s·(r+1) > r` for `s ≥ 1`), so an honest-only collision needs a fork. Do not claim fresh honest roots.
  - Existing Lean theorems: this limit is INHERITED, not new. `GridCO.propose` (`Protocol.lean:292`), SA (`SA.propose` is `GridCO.propose`), SA-PC (`AvailableChainSAPC/Model/Choice.lean:87`) and L* (`AvailableChainLStar/Model/Protocol.lean:258`) use the same formula, and their run theorems take `RootInjective` (a field of every regime in `AvailableChainStatements/Generic/Regimes.lean:19,49,75` and `Strong/Regimes.lean:25`; an explicit hypothesis in GridCO `CleanInclusion`, `Recovery`, `RecoveryRepair`, `ProposalHeads`, `HealthyPrefix`, `HealthyInterior`, and SA-PC `HealthyCoverage`, `Paths`). Those theorems stay sound. Their coverage excludes every run with such a collision, including the two runs above.
  - Alternative (a user decision, not done here): an honest root that is an injective code of the full content, with the check of DQ3(a) at admission. Then root injectivity of accepted blocks is a theorem, not a premise. It changes `GridCO.propose` too if the SA base must agree, so it is a cross-library change outside this plan.
- **DQ11. Pin tags.** The blueprint ids (`bp.*`, `comp.outputNesting.v2`) are not yet in `docs/FG-COMPOSITION.md` (composition task T1). **Recommendation:** use docstring tags ``[bp <id>; K<k>]`` and ``[spec <lines>]`` now. Build a pin table and a checker in composition task T15, after T1, from the corrected sources (bp00 archive copy `03afa5ae`).
- **DQ12. A carried row with a wrong signature form.** **Recommendation:** `blockAccepted` refuses a block that carries a row that does not decode as a row (`RowWire.decode? = none`). Then `fgBlock` never drops a row (Task 10, `toRow_forall₂`). Also (audit M1): a carried row BODY passes the same check as a row alone (`RowWire.valid`, M12), in `wellFormed`. The resulting store fact is "every row of a stored block decodes" (Tasks 10 and 12: `blockAccepted`, `MetaInv.wireTree`). The decoded-key grouping of `proposalRows` equals that of `admitRow` (G6 item 9) on EVERY store, for a different reason (G12 m2): the `round?` filter of `proposalRows` and `blockWireRows` drops every row that does not decode, so no candidate has the key `none`.
- **DQ13. `deepest` tie rule** (audit N2; Opus m8). **Recommendation:** implement the spec rule (spec 260–262: the largest depth; ties: the greater root wins), as `liveRoot` does. `deepest X` is `pickPair` of the member that is maximal in the order (depth of the erasure, root value). `deepest ∅ = none`. For a nonempty `X`, it is `none` only if two distinct maximal candidates have the same depth and root; a tie between members that are not maximal does not cause `none` (r188 N6). Task 11 proves that `none` does not occur for a nonempty `X ⊆ Σ.T` (`deepest_spec`). Task 11 also proves `fgBlockOf_spec` and `fgHead_stored`, so the fallback head fields of `fgInputs` are unreachable. The alternative, "each fastWrite set is a chain", is a true store fact (its members are prefixes of one result, and reconcile only filters), but it is not needed with the tie rule.
- **DQ14. Input check and handlers** (audit M1; Opus m3). **Recommendation:** keep `process` separate from `wellFormed`, as in the spec (spec 505–518: the ingress check drops an object before any handler). So `Reachable` covers unchecked inputs; it is an over-approximation, and every store fact holds on it. T7 must show that each actual handler call has a checked input (`DeliveryWellFormed` on v1). `blockAccepted` keeps every acceptance test in the spec's place (spec 530–536, 806–817), also the parent-slot, proposer and row-round tests. Because the flat wire carries `b.parent.slot` and the row rounds, `wellFormed` ALSO has these three tests (Opus m3). The duplication is harmless, and it gives `blockAccepted_of_wellFormed` (DQ9). Opus m3 asked to MOVE the tests out of `blockAccepted`; this plan copies them instead, because a move would make the store invariants depend on `wellFormed` over the unchecked `Reachable` closure.

## Tree-read inventory (Review Focus 1)

Every consumer must read the right block set. This is bp00 §2.4 with the Lean name of each read.

```text
┌───────────────────────────┬──────────────────────────────────┬─────────────────────────────────┐
│ Consumer                  │ Spec read                        │ Lean (this plan)                │
├───────────────────────────┼──────────────────────────────────┼─────────────────────────────────┤
│ Confirmation / gate       │ act(Σ), walk from genesis, no FJ │ SA.gate via onView (actView)    │
│                           │ band                             │                                 │
│ Release / resolution      │ active heads, original stamps    │ SA.release via onView;          │
│                           │                                  │ GridCO.resolvedBefore (actView) │
│ Late count / equivocation │ signed votes, no active test     │ base.votes (actView keeps them) │
│ H / contest / frame       │ cumulative Σ.T and live caches   │ storeControls p.E p.cfg st.fg   │
│ V_s block view            │ pre-z_{s−1} blocks ∪ current     │ voterBlocks (st.fg.TF, base     │
│                           │ proposal paths                   │ block stamps)                   │
│ HEAD raw merge            │ frozen votes + every current     │ headVotes (st.proposals, no act │
│                           │ proposal in Σ.T                  │ filter; spec 190–193)           │
│ Frozen support            │ active resolution before z_{s−1},│ headSupport, frozen arm, on     │
│                           │ tested at read time              │ actView                         │
│ Carried support           │ original declaration; head in    │ headSupport, carried arm,       │
│                           │ Σ.T, valid slot                  │ blockKnown st.base              │
│ Proposal / finality head  │ full filtered tree D_Σ(Σ.T);     │ getHead with fullTree;          │
│                           │ active resolved support          │ support on actView              │
│ live_root                 │ deepest live lease in D_Σ(Σ.T),  │ liveRoot (tie: greater root)    │
│                           │ else Z                           │                                 │
│ C_fg at a_r               │ deepest live fastWrite[rR]       │ fgSource (deepest, tie: greater │
│                           │ member in D_Σ(Σ.T)               │ root; DQ13)                     │
│ Row inclusion             │ row pool + original rows of      │ proposalRows (rowPool,          │
│                           │ blocks in Σ.T                    │ st.proposals)                   │
└───────────────────────────┴──────────────────────────────────┴─────────────────────────────────┘
```

## Review Focus

1. **The tree-read inventory above.** A reviewer checks each row against the Lean definition.
2. **Refusal before any write** (spec 530–536, 806–817). A refused block changes nothing: no base block, no stamp, no carried vote, no row, no FG change. Test: Task 4, a conflicting block that carries a vote and a row that separate calls WOULD admit.
3. **reconcile writes only SA fields and S** (spec 474–484, 874–894; K3). It keeps the evaluated label of an emptied result; it never moves a lease or writes `F` into a saved result. Test: Task 4 (through a block delivery) and Task 3 (direct).
4. **S := F after every gate and every F advance** (spec 563–568, 778–781, 890–892). Also after an empty or vetoed gate. Test: Task 5.
5. **fastWrite[rR] is created at the gate, also empty; there is no older-set fallback** (spec 458–460, 669–677). A renewal counts also when the deadline does not change; a slow-only renewal does not enter fastWrite. Test: Tasks 5 and 6.
6. **The live frame comes from the full store** (spec 616–646). The HEAD applies it to its own block view; it does not recompute controls from the view. Test: Task 6, a HEAD that takes a child by band eligibility.
7. **Resolution at read time** (spec 429–430). The HEAD's frozen support tests the CURRENT `act(Σ)`, not the one at the freeze. The raw merge keeps the votes of a proposal that left `act(Σ)` (spec 190–193). Test: Task 6.
8. **The root-based duplicate test** (DQ2). Test: Task 4, a new block with a stored root and a different parent is refused.
9. **One row check in both delivery forms** (M12). Test: Task 4, the same height-0 row alone and in a block.
10. **Parameter indexing** (M11). No `State n` with a free `n` next to `p : Params`.
11. **Explicit lease policy** (Global Constraints). Every lease-dependent GridCO lemma for the SA base is applied with `@… GridCO.slowLeasePolicy`.

## File structure

```text
┌───────────────────────────────────────────────┬──────────────────────────────────────────┐
│ File                                          │ Responsibility                           │
├───────────────────────────────────────────────┼──────────────────────────────────────────┤
│ lakefile.toml                                 │ one appended lean_lib block; default     │
│                                               │ target at Task 13                        │
│ AvailableChainFGSA.lean                       │ library root (imports every file)        │
│ AvailableChainFGSA/Model/Objects.lean         │ Params, Label, RowBody (valid), wires,   │
│                                               │ Msg, Input, the decoders, eraseFG, base  │
│                                               │ conversions, rounds                      │
│ AvailableChainFGSA/Model/Store.lean           │ State, initial, outputs, actView,        │
│                                               │ onView, normalizeS, reconcile, lease and │
│                                               │ fastWrite reads, blockExcluded           │
│ AvailableChainFGSA/Model/Handlers.lean        │ admitHead, admitRow, parentFG, fgBlock,  │
│                                               │ blockAccepted, admitBlock, process,      │
│                                               │ wellFormed                               │
│ AvailableChainFGSA/Model/Clock.lean           │ fastSet, gateStep, clockPre, clock       │
│ AvailableChainFGSA/Model/Frame.lean           │ controls, fullTree, liveRoot, eligible,  │
│                                               │ headInTree, voterBlocks, headVotes,      │
│                                               │ headSupport, headVote, getHead,          │
│                                               │ proposalRows, propose, fgHead, deepest,  │
│                                               │ fgSource, fgInputs, attest               │
│ AvailableChainFGSA/Statements/Invariants.lean │ Reachable, NestOK, SACompat, FastOrigin, │
│                                               │ CStoreInv, Inv0, MetaInv, ContentAgree   │
│ AvailableChainFGSA/Statements/Store.lean      │ OutputNestingStored, StoreInvariant,     │
│                                               │ FMonotone, MetadataInvariant             │
│ AvailableChainFGSA/Proofs/BlockAncestry.lean  │ public Block ancestry lemmas             │
│ AvailableChainFGSA/Proofs/Carrier.lean        │ K5, local carrier algebra                │
│ AvailableChainFGSA/Proofs/Fields.lean         │ write sets of every step                 │
│ AvailableChainFGSA/Proofs/ActView.lean        │ actView laws (bp.activeView.v1 items     │
│                                               │ 1–6); SA bridge of the tick              │
│ AvailableChainFGSA/Proofs/Nesting.lean        │ K2, comp.outputNesting.v1/v2             │
│ AvailableChainFGSA/Proofs/Reconcile.lean      │ K3, exact effects, idempotence; K1       │
│                                               │ (helper and origin form)                 │
│ AvailableChainFGSA/Proofs/Admission.lean      │ refusal and accept-branch agreement;     │
│                                               │ block-step SA bridge (J3); acceptance    │
│                                               │ sufficiency (K8)                         │
│ AvailableChainFGSA/Proofs/StoreInv.lean       │ K4 core, base = Σ.T erased, F monotone,  │
│                                               │ SACompat, FastOrigin, K1 at a block      │
│                                               │ step, selector facts                     │
│ AvailableChainFGSA/Proofs/Metadata.lean       │ K4 metadata (MetaInv), cumulative steps  │
│ AvailableChainFGSA/Proofs/CrossNode.lean      │ K5 cross-node under ContentAgree         │
│ AvailableChainFGSA/Tests/Smoke.lean           │ decide examples (grown by Tasks 1–6)     │
│ AvailableChainFGSA/Tests/Axioms.lean          │ #print axioms of every public theorem    │
│ scripts/check-fgsa.sh                         │ build, root imports, native scan, import │
│                                               │ rules, Q1 grep, axiom check              │
│ scripts/CheckFGSAAxioms.lean                  │ axioms of every compiled FGSA constant   │
│ scripts/CheckFGSALease.lean                   │ lease-instance check (G11 M1; G13)       │
│ AvailableChainFGSA/Tests/RootCollision.lean   │ DQ10/I9 witness (G13 Opus m4)            │
│ docs/FGSA-STORE-REPORT.md                     │ the Task 13 report with the G13 fixes    │
└───────────────────────────────────────────────┴──────────────────────────────────────────┘
```

## Task list

```text
┌─────┬──────────────────────────────────┬──────┬──────────┬──────────┬────────────────┐
│ #   │ Task                             │ comp │ Size     │ Depends  │ Parallel with  │
├─────┼──────────────────────────────────┼──────┼──────────┼──────────┼────────────────┤
│ 0   │ Preconditions; plan audits (G0)  │ —    │ —        │ —        │ —              │
│ 1   │ Library skeleton and objects     │ T3   │ S 0.2k   │ 0        │ —              │
│ 2   │ Block ancestry and local carrier │ T4   │ S–M      │ 1        │ 3–6            │
│     │ (K5, local)                      │      │ 0.3–0.5k │          │                │
│ 3   │ Store: state, act(Σ), reconcile, │ T3   │ S 0.2k   │ 1        │ 2              │
│     │ outputs                          │      │          │          │                │
│ 4   │ Handlers: votes, rows, blocks    │ T3   │ M 0.35k  │ 3        │ 2              │
│ 5   │ Clock and composite gate         │ T3   │ S 0.25k  │ 4        │ 2              │
│     │                                  │      │          │ (stA)    │                │
│ 6   │ Frame reads and duties; Astra    │ T3   │ M        │ 5        │ 2              │
│     │ model check (G6)                 │      │ 0.45–0.55│          │                │
│ 7   │ Write sets, actView laws (items  │ T5   │ M        │ 2, 6     │ —              │
│     │ 1–6), tick SA bridge             │      │ 0.5–0.7k │          │                │
│ 8   │ Output nesting (K2), store form  │ T6   │ S 0.2k   │ 7        │ —              │
│ 9   │ Reconcile facts (K3; K1 helper   │ T5   │ M        │ 7        │ —              │
│     │ and origin form)                 │      │ 0.4–0.5k │          │                │
│ 10  │ Admission agreement, block-step  │ T5   │ M–L      │ 2, 7, 9  │ —              │
│     │ SA bridge (J3), sufficiency (K8) │      │ 0.45–0.6k│          │                │
│ 11  │ Composite store invariant (K4    │ T5   │ M–L      │ 8, 9, 10 │ —              │
│     │ core), F monotone, K1 at a step, │      │ 0.6–0.9k │          │                │
│     │ selector facts                   │      │          │          │                │
│ 12  │ Metadata invariant (K4 metadata) │ T4,  │ M        │ 11       │ —              │
│     │ and cross-node carrier (K5)      │ T5   │ 0.4–0.6k │          │                │
│ 13  │ Axiom audit, full build, MAP,    │ —    │ S        │ 12       │ —              │
│     │ handoff                          │      │          │          │                │
└─────┴──────────────────────────────────┴──────┴──────────┴──────────┴────────────────┘
```

Sizes are Lean lines, with tests. Total: about 4.3–5.6k lines (model 1.2–1.4k, proofs 2.7–3.8k, tests 0.4k). Revision 1 estimated 3.3–4.3k. The increase (about 1.0–1.3k) is: the six activeView items and the block-step bridge (J2, J3; Tasks 7, 10), the fast-write origin invariant and the K1 origin form (M3; Tasks 9, 11), the acceptance sufficiency and selector facts (m2, N2; Tasks 10, 11), the metadata invariant and the cross-node carrier (M2, M4; Task 12), and the new tests (N1; Tasks 4–6). Opus estimated +0.3–0.5k for J2, J3, M3, M4 and m2 alone; Task 12 and the tests are the rest. The composition plan estimated 0.8–1.2k (T3), 0.3–0.6k (T4), 0.8–1.5k (T5) and S (T6). Critical path: 0 → 1 → 3 → 4 → 5 → 6 → 7 → 9 → 10 → 11 → 12 → 13.

---

### Task 0: Preconditions and the plan audits (G0)

**Files:** none in Lean. The audit reports are in `docs/audit/`: `fgsa-model-store-plan-audit-report.md` (Astra r185) and `fgsa-model-store-plan-opus-review.md` (Opus). The second audit (Astra r188) wrote `docs/audit/fgsa-model-store-plan-reaudit-report.md`.

- [x] **Step 1: Check the base.** Done for revision 2 on 2026-09-28: branch `fgsa-composition`; spec `2e884811…` (since G4: the hash of the archive copy `R/spec/archive/fgsa-protocol-2e884811.tex`, the line-anchor authority; the adopted `R/spec/fgsa-protocol.tex` is `dbcb7f05…` and has the same frozen rules, Sources note 1); comp `228dbe98…`; bp01 `989289cc…`; bp00 re-pinned to `03afa5ae…` (Sources, note 4; since revision 2.1, the hash of the archive copy `R/blueprint/archive/00-outline-03afa5ae.md`). At execution, repeat: `git status` is clean; `git log -1` contains the revision-2 commit; the four hashes agree. If not, stop and report.
- [x] **Step 2: Check the FG module state.** Done (both audits): `Store` has one tree `TF`; `storeInv_init`, `on_block_of_refused`, `on_block_of_accepted`, `on_block_F_mono`, `storeInv_on_block`, `storeControls_eq_fjControls`, `update_finality_TF`, `update_finality_h_max`, `update_finality_pair`, `pickPair_eq_of_unique`, `ancestor_closed_of_parent_closed` exist (`KitFG/Correspondence.lean`); `pickPair` is at `SimplexFG/Frame.lean:81`. Repeat the grep at execution: `grep -n 'theorem storeInv_on_block\|theorem storeControls_eq_fjControls\|theorem on_block_F_mono\|def pickPair\|theorem pickPair_eq_of_unique\|theorem ancestor_closed_of_parent_closed' AvailableChainKitFG/Correspondence.lean AvailableChainSimplexFG/Frame.lean`.
- [x] **Step 3: First plan audits.** Done: Astra r185 and Opus, both REVISE.
- [x] **Step 4: Apply the audits.** Done: this revision; see "Disposition of audit findings". Commit `FGSA plan: revision 2 after the Astra and Opus audits`.
- [x] **Step 5: Second audit of the changed sections (gate G0).** Start a Codex job with the astra model (memory: "use astra freely when beneficial"; see the `codex-teammate` skill), or an independent reviewer agent. The job reads this plan, both reports, the disposition table and the Lean sources that the changed sections name. It checks that each finding is closed as the table says, and that the changes add no new error (types: M11; the decoders; `FastOrigin`; `MetaInv`; `ContentAgree`; the J3 statements; the axiom command). Output: a report with a verdict. G0 closes on ADOPT or ADOPT WITH FIXES, with each blocking and major fix applied. Record the result under "Review status".
  DONE, 2026-09-29: Astra r188, `docs/audit/fgsa-model-store-plan-reaudit-report.md` (the output path of that job), verdict PASS WITH MINORS: 0 blocking, 0 major, minors N1–N6. PASS WITH MINORS maps to ADOPT WITH FIXES. Revision 2.1 applies N1–N6. **G0 is closed.** The three audit reports: `docs/audit/fgsa-model-store-plan-audit-report.md` (Astra r185), `docs/audit/fgsa-model-store-plan-opus-review.md` (Opus), `docs/audit/fgsa-model-store-plan-reaudit-report.md` (Astra r188).

---

### Task 1: Library skeleton and objects

**Files:**
- Modify: `lakefile.toml` (append the block below; do NOT add it to `defaultTargets` until Task 13)
- Create: `AvailableChainFGSA.lean`, `AvailableChainFGSA/Model/Objects.lean`, `AvailableChainFGSA/Tests/Smoke.lean`, `scripts/check-fgsa.sh`

**Interfaces:**
- Consumes: `SA.Params`, `SA.gateTime`, `SA.voteTime`, `GridCO.HeadWire`, `GridCO.Wire`, `GridCO.fromHead`, `GridCO.{headLabel?, headSeat?, headTarget?}`, `SimplexFG.{NamedHeightPair, FinalityPair, Row, FGBlock, Electorate, FGConfig}`, `AvailableChain.{Block, Signed, Auth}`.
- Produces: `Params` (with `E`, `cfg`, `round`, `actionTime`, `slotOf`), `Label` (with `actTime`), `RowBody` (with `ofRow`, `valid`), `HeadWire` (with `decode?`), `RowWire` (with `decode?`, `round?`, `toRow?`, `valid`), `Msg`, `Wire`, `Input`, `Wire.decode`, `Wire.block?`, `eraseFG`, `baseHead`, `baseVote`, `liftHead?`, `baseProposal`.

- [x] **Step 1: Add the library.** Append to `lakefile.toml`:

```toml
# FG-SA composite model (LM), store statements and store proofs
# (docs/plans/2026-09-29-fgsa-model-store.md). No engine binding.
[[lean_lib]]
name = "AvailableChainFGSA"
```

- [x] **Step 2: Write the failing tests.** Create `AvailableChainFGSA.lean` with `public import AvailableChainFGSA.Model.Objects` and `public import AvailableChainFGSA.Tests.Smoke`. Create `AvailableChainFGSA/Tests/Smoke.lean` (imports `AvailableChainFGSA.Model.Objects`; namespace `AvailableChain.FGSA.Tests`; `open AvailableChain.SimplexFG`) with the fixture and the object tests:

```lean
/-- The test parameters: Δ = 1, n = 4, k = 2, R = 2, w_F = 1, δ_t = 1.
`pT.cfg` is the FG module's `cfg1` and `pT.E` is its `E4`, so the FG test
blocks `B1`, `B2`, `B3`, `B1'` of `AvailableChainSimplexFG` apply.
`pT.n` reduces to `4`, so `State 4` and `State pT.n` are one type. -/
abbrev pT : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, wF := 1, δt := 1, RLarge := by decide, wFPos := by decide }

/-- A signed FG row of round `r` by identity `i`. -/
def rw (r : Nat) (i : Fin 4) (a : Row (Fin 4)) : RowWire 4 :=
  ⟨.seat (.fg r) i, RowBody.ofRow a⟩

example : eraseFG B1 = Block.node .genesis 1 ⟨1⟩ := by decide
example : (rw 0 2 (rowT 2)).decode? = some (0, 2, RowBody.ofRow (rowT 2)) := by decide
example : (rw 0 2 (rowT 2)).toRow? = some (rowT 2) := by decide
example : (rw 0 2 (rowT 2)).round? = some 0 := by decide
/-- `a_r = d_{rR}` (spec 217–220): with R = 2, `a_1 = d_2 = 4·2 + 6 = 14`. -/
example : pT.actionTime 1 = 14 := by decide
example : (Label.fg 1).actTime pT = 14 ∧ (Label.head 3).actTime pT = 13 := by decide
/-- At `a_1 = 14` the store slot is `rR + 1 = 3`, still round 1 (spec 1306, 1317). -/
example : pT.slotOf 14 = 3 ∧ pT.round 3 = 1 := by decide
/-- The base form of a carried vote: a HEAD seat of slot `s` is a seat of base
label `s`; an FG seat is not a base signature. -/
example : baseHead (n := 4) ⟨.seat (.head 3) 1, .genesis⟩ = ⟨.seat 3 1, .genesis⟩ ∧
    baseHead (n := 4) ⟨.seat (.fg 3) 1, .genesis⟩ = ⟨.none, .genesis⟩ := by decide
/-- One row check (M12; spec 234–237): height 0 fails; height 1 and the empty
pair pass; a row with a HEAD signature fails. -/
example : (RowBody.mk (.vote 0 genesisRoot false) none).valid = false ∧
    (RowBody.mk (.vote 1 genesisRoot false) none).valid = true ∧
    (RowBody.mk .empty none).valid = true ∧
    RowWire.valid (n := 4) ⟨.seat (.head 0) 2, RowBody.mk .empty none⟩ = false := by decide
example : Wire.decode (n := 4) ⟨.seat (.fg 1) 2, .row (RowBody.ofRow (rowT 2))⟩ =
    some (.row 1 2 (RowBody.ofRow (rowT 2))) ∧
    Wire.decode (n := 4) ⟨.seat (.head 1) 2, .row (RowBody.ofRow (rowT 2))⟩ = none := by decide
```

Run: `lake build AvailableChainFGSA.Tests.Smoke`. Expected: FAIL (unknown identifiers).

- [x] **Step 3: Write `Model/Objects.lean`.** Imports: `AvailableChainSA.Model.Protocol`, `AvailableChainSimplexFG.Store`, `AvailableChainSimplexFG.Client`. Namespace `AvailableChain.FGSA`; `open AvailableChain.Generic AvailableChain.SimplexFG`.

```lean
/-- [spec 265–335] FG-SA parameters: the SA parameters (`Δ`, `n`, `k`, `η`), the
round length `R ≥ 2`, the row window `w_F ≥ 1` and the timeout delay `δ_t ≥ 0`
(`δ_t = 0` is allowed; no statement may need `δ_t > 0`). -/
structure Params extends SA.Params where
  R : Nat
  wF : Nat
  δt : Nat
  RLarge : 2 ≤ R
  wFPos : 1 ≤ wF

namespace Params
/-- [spec 154–158] Unit weights on the fixed identities `V = Fin n`. -/
def E (p : Params) : Electorate (Fin p.n) := ⟨fun _ => 1, fun _ => Nat.one_pos⟩
/-- [spec 283] The FG configuration: the timeout delay `δ_t`. -/
def cfg (p : Params) : FGConfig := ⟨p.δt⟩
/-- [spec 209] `round(s) = ⌊s / R⌋`. -/
def round (p : Params) (s : Slot) : Nat := s / p.R
/-- [spec 217–220] `a_r = T_r + 6Δ = d_{rR}`. -/
def actionTime (p : Params) (r : Nat) : Time := SA.gateTime p.toParams (r * p.R)
/-- [spec 711] `Σ.s = ⌊t / 4Δ⌋`, as `GridCO.admitProposal` computes it. -/
def slotOf (p : Params) (t : Time) : Slot := (t / (4 * p.Δ)).toNat
end Params

/-- [spec 197–220; comp §4.2; model representation of the duty labels] Duty labels: the HEAD of
slot `s` and the FG action of round `r`. -/
inductive Label where
  | head (s : Slot)
  | fg (r : Nat)
  deriving DecidableEq, Repr

/-- [spec 197–220] The act time of a label: `v_s` for a HEAD, `a_r` for an FG
action. The two families never share a time. -/
def Label.actTime (p : Params) : Label → Time
  | .head s => SA.voteTime p.toParams s
  | .fg r => p.actionTime r

/-- [spec 230–237] An FG row without its identity and round: the height pair and
the finality pair. The identity is the seat index and the round is the label of
the row's signature (M4). -/
structure RowBody where
  height_pair : NamedHeightPair
  finality_pair : Option FinalityPair
  deriving DecidableEq, Repr

def RowBody.ofRow {V : Type} (a : Row V) : RowBody := ⟨a.height_pair, a.finality_pair⟩

/-- [spec 230–237, 505–518; M12] The one row-body check, for a row alone and
for each row that a block carries: the height pair is empty or a vote at height
`h ≥ 1`. `T ≠ ⊥` and `T_f ≠ ⊥` hold by the types (`BlockId`; the empty
finality pair is `none`). The spec gives no height bound on the finality pair. -/
def RowBody.valid (a : RowBody) : Bool :=
  match a.height_pair with
  | .empty => true
  | .vote h _ _ => decide (1 ≤ h)

/-- [spec 225–228] A signed Goldfish vote, as a block carries it. -/
abbrev HeadWire (n : Nat) := Signed Label n Block
/-- [spec 230–237] A signed FG row. Its auth is `.seat (.fg r) i`. -/
abbrev RowWire (n : Nat) := Signed Label n RowBody

namespace HeadWire
variable {n : Nat}
/-- [spec 225–228, 510–511; J1] The one auth decoder of a carried vote: label `s`,
seat `i`, head. -/
def decode? (o : HeadWire n) : Option (Slot × Fin n × Block) :=
  match o.auth with
  | .seat (.head s) i => some (s, i, o.payload)
  | _ => none
end HeadWire

namespace RowWire
variable {n : Nat}
/-- [spec 230–237, 512–513; J1; M4] The one auth decoder of a row: the round `r` (the label), the
identity `i` (the seat index) and the body. -/
def decode? (a : RowWire n) : Option (Nat × Fin n × RowBody) :=
  match a.auth with
  | .seat (.fg r) i => some (r, i, a.payload)
  | _ => none
/-- The round of a row. -/
def round? (a : RowWire n) : Option Nat := a.decode?.map (·.1)
/-- The FG row: the signer is the seat index of the fg-label signature. -/
def toRow? (a : RowWire n) : Option (Row (Fin n)) :=
  a.decode?.map (fun x => ⟨x.2.1, x.2.2.height_pair, x.2.2.finality_pair⟩)
/-- [spec 505–518; M12] The row input check: an FG signature and a valid body. -/
def valid (a : RowWire n) : Bool := (a.decode?.map (fun x => x.2.2.valid)).getD false
end RowWire

/-- [spec 225–263; comp §4.2] The payloads. A proposal carries the erased block,
the previous-slot votes, the declared support subset and its own signed rows
(M3). -/
inductive Msg (n : Nat) where
  | head (target : Block)
  | proposal (b : Block) (view supportView : List (HeadWire n)) (rows : List (RowWire n))
  | row (body : RowBody)
  deriving DecidableEq, Repr

abbrev Wire (n : Nat) := Signed Label n (Msg n)

/-- [spec 505–518, 804–857; J1; model representation of a decoded input] A decoded
wire. -/
inductive Input (n : Nat) where
  | vote (s : Slot) (i : Fin n) (target : Block)
  | row (r : Nat) (i : Fin n) (body : RowBody)
  | block (s : Slot) (b : Block) (raw support : List (HeadWire n)) (rows : List (RowWire n))
  deriving DecidableEq, Repr

/-- [spec 505–518; J1] The one auth decoder of a wire. Every handler and the input check read
a wire only through `Wire.decode`, `HeadWire.decode?` and `RowWire.decode?`. On
engine v2, a decode adapter to `Wire p.n` keeps the internal API; T7 sets the
scope of a native re-typing (Q1 boundary). -/
def Wire.decode {n : Nat} (o : Wire n) : Option (Input n) :=
  match o.auth, o.payload with
  | .seat (.head s) i, .head b => some (.vote s i b)
  | .seat (.fg r) i, .row body => some (.row r i body)
  | .proposer s, .proposal b raw sup rows => some (.block s b raw sup rows)
  | _, _ => none

/-- [spec 248–255; helper] The block of a proposal wire. -/
def Wire.block? {n : Nat} (o : Wire n) : Option Block :=
  match o.decode with
  | some (.block _ b _ _ _) => some b
  | _ => none

/-- [spec 248–263, 381–403; bp bp.carrier.v1] The geometric erasure of an FG block
(bp01 §2.1 `eraseFG`). -/
def eraseFG {V : Type} : FGBlock V → Block
  | .genesis => .genesis
  | .node p s r _ => .node (eraseFG p) s r

/-- [spec 225–228; model representation of a carried vote in the SA base] The base
form of a carried vote: a HEAD seat of slot `s` becomes a
seat of base label `s`; any other auth becomes `.none`. -/
def baseHead {n : Nat} (o : HeadWire n) : GridCO.HeadWire n :=
  match o.decode? with
  | some (s, i, b) => ⟨.seat s i, b⟩
  | none => ⟨.none, o.payload⟩
def baseVote {n : Nat} (o : HeadWire n) : GridCO.Wire n := GridCO.fromHead (baseHead o)
/-- [spec 1240–1249; helper] A base vote as a composite carried vote (for the proposer's lists).
It reads the GridCO accessors; it matches no auth. -/
def liftHead? {n : Nat} (o : GridCO.Wire n) : Option (HeadWire n) := do
  let s ← GridCO.headLabel? o
  let i ← GridCO.headSeat? o
  let b ← GridCO.headTarget? o
  pure ⟨.seat (.head s) i, b⟩
/-- [spec 248–255, 820–823; model representation of a proposal in the SA base] The
base proposal of a decoded composite proposal (as SA-PC `baseProposal`). -/
def baseProposal {n : Nat} (s : Slot) (b : Block) (raw support : List (HeadWire n)) :
    GridCO.Wire n :=
  ⟨.proposer s, .proposal b (raw.map baseHead) (support.map baseHead)⟩
```

  If `structure Params extends SA.Params` does not give `p.Δ`, `p.n` and `p.toParams`, report it and use an explicit field `sa : SA.Params` with the same names in the rest of the plan. (Opus compiled the `extends` form: it works.)

- [x] **Step 4: Write `scripts/check-fgsa.sh`.**

```bash
#!/usr/bin/env bash
# FGSA checks: build (--wfail), root imports, native evaluation outside
# comments, the import rules (direct and closure), the Q1/Q5 boundary grep,
# and (once present) the axiom check.
# Run: bash scripts/check-fgsa.sh. Exit 0 when every check passes.
set -euo pipefail
cd "$(dirname "$0")/.."
echo "== lake build --wfail AvailableChainFGSA"
lake build --wfail AvailableChainFGSA
echo "== root imports"
missing=$(comm -23 \
  <(find AvailableChainFGSA -name '*.lean' | sed 's/\.lean$//; s|/|.|g' | sort) \
  <( (grep -hoE '^[[:space:]]*(public )?(meta )?import (all )?[A-Za-z0-9_.]+' AvailableChainFGSA.lean || true) | awk '{print $NF}' | sort))
[ -z "$missing" ] || { echo "NOT IMPORTED BY THE ROOT: $missing"; exit 2; }
echo "== native evaluation"
# Remove comments with a small tokenizer that knows strings, character
# literals, raw strings (r"...", r#"..."#) and nested block comments. A "--"
# in a string does not start a comment, and a "/-" in a line comment does not
# open a block comment.
strip_comments='
  local $/; my $s = <STDIN>; my $o = ""; my $d = 0;
  while ((pos($s) // 0) < length $s) {
    if ($d > 0) {
      if    ($s =~ /\G\/-/gc)   { $d++ }
      elsif ($s =~ /\G-\//gc)   { $d--; $o .= " " }
      elsif ($s =~ /\G(\n)/gc)  { $o .= $1 }
      else                      { $s =~ /\G./gcs }
    }
    elsif ($s =~ /\G--[^\n]*/gc)                         { }
    elsif ($s =~ /\G\/-/gc)                              { $d = 1 }
    elsif ($s =~ /\Gr(#*)".*?"\1/gcs)                    { $o .= "\"\"" }
    elsif ($s =~ /\G"(?:\\.|[^"\\])*"/gcs)               { $o .= "\"\"" }
    elsif ($s =~ /\G([\w\p{N}.!?][\w\p{N}.!?\x27]*)/gc)  { $o .= $1 }
    elsif ($s =~ /\G\x27(?:\\.|[^\\\x27])\x27/gc)        { $o .= "c" }
    else                                                 { $s =~ /\G(.)/gcs; $o .= $1 }
  }
  print $o;'
status=0
for f in $(find AvailableChainFGSA -name '*.lean') AvailableChainFGSA.lean; do
  if perl -CSD -e "$strip_comments" < "$f" |
      grep -nE '(^|[^A-Za-z0-9_.])native_decide([^A-Za-z0-9_]|$)|\+native|native := true|ofReduceBool|ofReduceNat' >/dev/null; then
    echo "native evaluation in $f"; status=1
  fi
done
[ $status -eq 0 ] || exit 1
echo "== direct imports"
if grep -rnE '^[[:space:]]*(public )?(meta )?import (all )?(AvailableChainFramework|AvailableChainRegistry|AvailableChainStatements|AvailableChainWitnesses|AvailableChainSAPC)' \
    AvailableChainFGSA AvailableChainFGSA.lean; then
  echo "FORBIDDEN DIRECT IMPORT"; exit 1
fi
echo "== import closure"
seen=" "
todo=$( (grep -rhoE '^[[:space:]]*(public )?(meta )?import (all )?[A-Za-z0-9_.]+' AvailableChainFGSA AvailableChainFGSA.lean || true) | awk '{print $NF}' | sort -u)
while [ -n "$todo" ]; do
  next=""
  for m in $todo; do
    case "$seen" in *" $m "*) continue ;; esac
    seen="$seen$m "
    f="${m//.//}.lean"
    if [ -f "$f" ]; then
      next="$next $( (grep -hoE '^[[:space:]]*(public )?(meta )?import (all )?[A-Za-z0-9_.]+' "$f" || true) | awk '{print $NF}')"
    fi
  done
  todo=$next
done
if echo "$seen" | tr ' ' '\n' | grep -E '^AvailableChain(Framework|Registry|SAPC|Witnesses)(\.|$)'; then
  echo "FORBIDDEN LIBRARY IN THE IMPORT CLOSURE"; exit 1
fi
echo "== Q1/Q5 boundary"
if grep -rnE 'ProtocolSpec|Generic\.Run|World|pendingRow' AvailableChainFGSA AvailableChainFGSA.lean; then
  echo "ENGINE REFERENCE"; exit 1
fi
if [ -f scripts/CheckFGSAAxioms.lean ]; then
  echo "== axioms"
  lake env lean --run scripts/CheckFGSAAxioms.lean
fi
echo "all FGSA checks pass"
```

  The closure walk reads only source files of this worktree (Mathlib has no source here, so it stops there). `AvailableChainStatements` in the closure is allowed (Global Constraints, Imports).
  Negative tests (once each, then remove them): (1) add `example : 1 = 1 := by native_decide` to `Tests/Smoke.lean`; the script must exit 1; a comment `-- native_decide` must not make it fail. (2) Add `public import AvailableChainSAPC.Model.Objects` to `Tests/Smoke.lean`; the direct-import check must exit 1. G1 additions: (3) `public meta import AvailableChainSAPC.Model.Objects` and (4) `import all AvailableChainSAPC.Model.Objects`: the direct-import check must exit 1. (5) A line comment that contains `/-`, then a `native_decide` (under `set_option linter.style.nativeDecide false in`, so that the build passes), then a later docstring: the native scan must exit 1. (6) `example : "--".length = 2 := by native_decide` (same `set_option`): the native scan must exit 1. (7) Only comments (line, nested block, docstring with `"--"`) that name `native_decide`: exit 0. G2 additions: (8) `example : r"\".length = 1 := by native_decide` (same `set_option`), with a later string literal: the native scan must exit 1; (9) a module of the library with no import line: exit 0; (10) a root line `import all AvailableChainFGSA.Proofs.Carrier`: exit 0.
- [x] **Step 5: Run it; it passes.** `lake build --wfail AvailableChainFGSA.Tests.Smoke`, then `bash scripts/check-fgsa.sh`. Expected: PASS, exit 0.
- [x] **Step 6: Review gate G1 and CHECKPOINT.** Commit `FGSA model: library skeleton and objects`.

**G1 dispositions** (review of `0fbf787`: PASS WITH FIXES; 0 blocking, 1 major, 6 minor). All are applied in the commit `FGSA model: G1 fixes (import regexes, comment scan, tests, docs)`.

```text
┌───────┬──────────┬─────────────────────────────────────────────────────────────┐
│ G1    │ Severity │ Disposition                                                 │
├───────┼──────────┼─────────────────────────────────────────────────────────────┤
│ 1     │ MAJOR    │ The three import regexes of check-fgsa.sh missed `public    │
│       │          │ meta import` and `import all`. Now `^[[:space:]]*(public )? │
│       │          │ (meta )?import (all )?`, last field. Negative tests (3),    │
│       │          │ (4) added; the old script passed both, the new one exits 1. │
│ 2     │ MINOR    │ The native scan now strips comments with a tokenizer that   │
│       │          │ knows strings, character literals and nested block          │
│       │          │ comments. Negative tests (5), (6) added; the old script     │
│       │          │ passed both, the new one exits 1; (7) exits 0.              │
│ 3     │ MINOR    │ Smoke tests added: an FG row at height 1 passes and at      │
│       │          │ height 0 fails; HeadWire.decode?; Wire.decode of a vote and │
│       │          │ a proposal and three wrong auth/payload pairs; Wire.block?; │
│       │          │ the liftHead?/baseVote round trip; baseProposal.            │
│ 4     │ MINOR    │ Docstrings with spec lines or [helper] on RowBody.ofRow,    │
│       │          │ Wire, baseVote, RowWire.round?, RowWire.toRow?.             │
│ 5     │ MINOR    │ Accepted: the Objects imports stay as the plan prescribes   │
│       │          │ (harmless).                                                 │
│ 6     │ MINOR    │ Sources note 1 updated (draft diff, no model effect);       │
│       │          │ pickPair location corrected to Frame.lean:81.               │
│ (T1)  │ —        │ The plan test `(⟨…⟩ : RowWire 4).valid` does not elaborate  │
│       │          │ (the ascribed anonymous constructor has type `Signed …`);   │
│       │          │ the test uses `RowWire.valid (n := 4) ⟨…⟩`. Plan text       │
│       │          │ updated.                                                    │
└───────┴──────────┴─────────────────────────────────────────────────────────────┘
```

---

### Task 2: Block ancestry and the local carrier bridge (K5, local)

**Files:**
- Create: `AvailableChainFGSA/Proofs/BlockAncestry.lean`, `AvailableChainFGSA/Proofs/Carrier.lean`, `scripts/CheckFGSAAxioms.lean`
- Modify: `AvailableChainFGSA.lean` (two imports; added by the coordinator at the commit if Tasks 3–6 run in parallel)

**Interfaces:**
- Consumes: Task 1 (`eraseFG`); `SimplexFG.{FGBlock.preceq, ViewRootInj}`; `KitFG.{preceq_refl, preceq_trans, preceq_total_of_common, ancestor_closed_of_parent_closed, RootInjectiveOn}`.
- Produces: `block_preceq_refl`, `block_preceq_trans`, `block_preceq_antisymm`, `block_preceq_total_of_common`, `block_compatible_comm`, `block_compatible_of_common`, `block_incompatible_of_preceq`, `block_genesis_preceq`, `block_compatible_of_preceq_compatible`; `eraseFG_slot`, `eraseFG_root`, `eraseFG_parent`, `eraseFG_eq_genesis`, `eraseFG_preceq`, `eraseFG_compatible`, `eraseFG_injOn`, `preceq_of_eraseFG_preceq`, `compatible_iff_eraseFG`, `viewRootInj_of_rootInj`, `rootInjectiveOn_of_viewRootInj`, `erase_rootInjective`.

**Blueprint:** `bp.carrier.v1` (bp00 §3.1; bp01 §2.2 steps 1–6), LOCAL part only. With DQ1 there is one erasure. Step 3 of bp01 ("full-content root injectivity gives X = Y") becomes the root injectivity of ONE view (`ViewRootInj`), which Task 11 gets by construction (DQ2). This task does not complete K5: the two-store form needs the content premise and is Task 12 (audit M2). The report says "K5 local".

- [x] **Step 1: Write the Block ancestry statements** in `Proofs/BlockAncestry.lean` (imports `AvailableChainModel.Objects.Blocks`, `Mathlib.Tactic`). The GridCO copies of these lemmas are `private` (`GridCO/Proofs/Map.lean:25`, `Goldfish.lean:81`); do not import them.

```lean
theorem block_preceq_refl (B : Block) : Block.Preceq B B
theorem block_preceq_trans {A B C : Block} (h₁ : Block.Preceq A B) (h₂ : Block.Preceq B C) :
    Block.Preceq A C
theorem block_preceq_antisymm {A B : Block} (h₁ : Block.Preceq A B) (h₂ : Block.Preceq B A) :
    A = B
theorem block_genesis_preceq (B : Block) : Block.Preceq .genesis B
/-- Two ancestors of one block are comparable. -/
theorem block_preceq_total_of_common {A B W : Block} (hA : Block.Preceq A W)
    (hB : Block.Preceq B W) : Block.Preceq A B ∨ Block.Preceq B A
theorem block_compatible_comm (A B : Block) : Block.compatible A B = Block.compatible B A
/-- Two blocks below one block are compatible. -/
theorem block_compatible_of_common {A B W : Block} (hA : Block.Preceq A W)
    (hB : Block.Preceq B W) : Block.Compatible A B
/-- bp01 §5 item 5: a block that conflicts with `X` conflicts with every descendant of `X`. -/
theorem block_incompatible_of_preceq {b X Y : Block} (hbX : ¬ Block.Compatible b X)
    (hXY : Block.Preceq X Y) : ¬ Block.Compatible b Y
/-- If `A ⪯ C` and `C` is compatible with `F`, then `A` is compatible with `F`. -/
theorem block_compatible_of_preceq_compatible {A C F : Block} (hAC : Block.Preceq A C)
    (hCF : Block.Compatible C F) : Block.Compatible A F
```

  (The last one: if `C ⪯ F` then `A ⪯ F`; if `F ⪯ C` then `A` and `F` are ancestors of `C`.)
- [x] **Step 2: Write the carrier statements** in `Proofs/Carrier.lean` (imports `AvailableChainFGSA.Model.Objects`, `AvailableChainFGSA.Proofs.BlockAncestry`, `AvailableChainKitFG.Correspondence`). `variable {V : Type} [DecidableEq V]`.

```lean
/-- [bp bp.carrier.v1; K5 local] (step 1) -/
theorem eraseFG_slot (B : FGBlock V) : (eraseFG B).slot = B.slot
theorem eraseFG_root (B : FGBlock V) : (eraseFG B).root = B.root
theorem eraseFG_parent (B : FGBlock V) : (eraseFG B).parent = eraseFG B.parent
theorem eraseFG_eq_genesis {B : FGBlock V} : eraseFG B = .genesis ↔ B = .genesis
/-- [bp bp.carrier.v1; K5 local] (step 2; DC `NamedWire.erase_preceq`) Forward ancestry. -/
theorem eraseFG_preceq {A B : FGBlock V} (h : FGBlock.Preceq A B) :
    Block.Preceq (eraseFG A) (eraseFG B)
theorem eraseFG_compatible {A B : FGBlock V} (h : FGBlock.compatible A B = true) :
    Block.Compatible (eraseFG A) (eraseFG B)
/-- [bp bp.carrier.v1; K5 local] (step 3) Erasure is injective on the ancestors
of a root-injective view. -/
theorem eraseFG_injOn {Vw : View V} (hinj : ViewRootInj Vw) {A B : FGBlock V}
    (hA : ∃ W ∈ Vw, FGBlock.Preceq A W) (hB : ∃ W ∈ Vw, FGBlock.Preceq B W)
    (h : eraseFG A = eraseFG B) : A = B
/-- [bp bp.carrier.v1; K5 local] (step 4) Erasure reflects ancestry on such a view. -/
theorem preceq_of_eraseFG_preceq {Vw : View V} (hinj : ViewRootInj Vw) {A B : FGBlock V}
    (hA : ∃ W ∈ Vw, FGBlock.Preceq A W) (hB : ∃ W ∈ Vw, FGBlock.Preceq B W)
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B
/-- [bp bp.carrier.v1; K5 local] (step 5) -/
theorem compatible_iff_eraseFG {Vw : View V} (hinj : ViewRootInj Vw) {A B : FGBlock V}
    (hA : ∃ W ∈ Vw, FGBlock.Preceq A W) (hB : ∃ W ∈ Vw, FGBlock.Preceq B W) :
    FGBlock.compatible A B = Block.compatible (eraseFG A) (eraseFG B)
/-- [bp bp.carrier.v1; K5 local] (step 6) A parent-closed, root-injective block
set satisfies `ViewRootInj`. -/
theorem viewRootInj_of_rootInj {T : Finset (FGBlock V)} (hcl : ∀ B ∈ T, B.parent ∈ T)
    (hinj : ∀ X ∈ T, ∀ Y ∈ T, X.root = Y.root → X = Y) : ViewRootInj T
/-- [bp bp.carrier.v1; K5 local] (step 6, two chains of ONE view) The
`KitFG.accountable` premise. Two chains at two nodes: Task 12,
`rootInjectiveOn_across`. -/
theorem rootInjectiveOn_of_viewRootInj {T : Finset (FGBlock V)} (hinj : ViewRootInj T)
    {B₁ B₂ : FGBlock V} (h₁ : B₁ ∈ T) (h₂ : B₂ ∈ T) : KitFG.RootInjectiveOn B₁ B₂
/-- [bp bp.carrier.v1; K5 local] The erased blocks of a root-injective view have
distinct roots (the AC `RootInjective` shape, for T7). -/
theorem erase_rootInjective {T : Finset (FGBlock V)} (hinj : ViewRootInj T) :
    ∀ b ∈ T.image eraseFG, ∀ c ∈ T.image eraseFG, b.root = c.root → b = c
```

  Run: `lake build AvailableChainFGSA.Proofs.Carrier`. Expected: builds with `sorry` warnings only.
- [x] **Step 3: Prove them.** Step-1 lemmas: `cases B <;> rfl`. `eraseFG_preceq`: induction on `B`, as DC `NamedWire.erase_preceq` (DC `DecoupledConsensusProofs/Execution/Wire.lean`). `eraseFG_injOn`: `eraseFG_root` gives equal roots; `hinj` gives `A = B`. `preceq_of_eraseFG_preceq`: induction on `B`; in the node case either `eraseFG A = eraseFG B` (then `eraseFG_injOn`) or `Block.Preceq (eraseFG A) (eraseFG B.parent)` (then the induction hypothesis with the ancestor witness of `B.parent`). `viewRootInj_of_rootInj`: `KitFG.ancestor_closed_of_parent_closed` puts every ancestor of a member in `T`.
- [x] **Step 4: Write `scripts/CheckFGSAAxioms.lean`.** Copy `scripts/CheckFGAxioms.lean`. Change exactly these parts (audit M6):
  - the two top imports `import AvailableChainSimplexFG` and `import AvailableChainKitFG` become `import AvailableChainFGSA`;
  - the `importModules` array `#[{ module := `AvailableChainSimplexFG }, { module := `AvailableChainKitFG }]` becomes `#[{ module := `AvailableChainFGSA }]` (if only the top import changes, the scanner still loads the old libraries);
  - `inFG` becomes `inFGSA`, with the one prefix test `` (`AvailableChainFGSA).isPrefixOf m ``;
  - the docstring, the usage string and the `fileName` (`"CheckFGSAAxioms"`).
  Keep the parser: ONE `--expect` followed by all names (`expected := args.drop 1`); keep the exit codes (0 clean; 1 a bad axiom; 2 nothing found, a usage error, or an expected name missing), the transitive whitelist and the build-before-scan rule.
- [x] **Step 5: Run it; it passes.** `bash scripts/check-fgsa.sh`. Expected: exit 0; the axiom step prints `checked <c> constants, <t> theorems`. Then the two `--expect` tests: `lake env lean --run scripts/CheckFGSAAxioms.lean --expect eraseFG_preceq viewRootInj_of_rootInj` exits 0; `lake env lean --run scripts/CheckFGSAAxioms.lean --expect eraseFG_preceq noSuchName` prints `NOT CHECKED: noSuchName` and exits 2.
- [x] **Step 6: Review gate G2 and CHECKPOINT.** Commit `FGSA model: block ancestry and local carrier bridge (K5, local)`.

**G2 dispositions** (review of `fec67b1` and the G1 fixes `850bade`: PASS; 0 blocking, 0 major, 3 minor). G2 is closed. The reviewer found all 21 statements identical to the plan and confirmed that the axiom check flags `sorry`, a project axiom and `native_decide` in a declaration (exit 1).

```text
┌─────┬──────────────────────────────────────────────────────────────────────────┐
│ G2  │ Disposition                                                              │
├─────┼──────────────────────────────────────────────────────────────────────────┤
│ 1   │ Closure walk: a module with no import line made `grep` exit 1 inside     │
│     │ `$(...)`, and the script stopped with no message (fails closed). Now     │
│     │ `(grep … || true) | awk`, in both places. Test (9): old exit 1, new 0.   │
│ 2   │ Tokenizer: `r"…"` was read as a string with escapes, so `r"\"` hid a     │
│     │ later `native_decide` (fails open). A raw-string rule `r#*"…"#*` now     │
│     │ runs before the string rule. Test (8): old exit 0, new exit 1. The old   │
│     │ axiom step did not catch it either: the test is an `example`, which      │
│     │ leaves no constant to scan, so the native scan is the only guard for     │
│     │ examples.                                                                │
│ 3   │ Root-import check: `import all X` gave "all" (fails closed). It now uses │
│     │ the closure regex and the last field. Test (10): old exit 2, new 0.      │
└─────┴──────────────────────────────────────────────────────────────────────────┘
```

---

### Task 3: Store: state, active view, reconcile, outputs

**Files:**
- Create: `AvailableChainFGSA/Model/Store.lean`
- Modify: `AvailableChainFGSA.lean`, `AvailableChainFGSA/Tests/Smoke.lean`

**Interfaces:**
- Consumes: Task 1.
- Produces: `State`, `initial`, `State.slot`, `finalized`, `stable`, `confirmed`, `activeCompatible`, `actView`, `onView`, `normalizeS`, `reconcile`, `leaseOf`, `fastWriteAt`, `blockExcluded`.

- [x] **Step 1: Write the failing tests** (append to `Tests/Smoke.lean`). The state `stR0` is set by hand, as `AvailableChainSA/Tests/Smoke.lean` does. It is not a reachable state.

```lean
def b1 : Block := eraseFG B1
def b1' : Block := eraseFG B1'
/-- F = B1 (the FG store of the FG module's G02 test), with a lease, a saved
result and a fast write on the conflicting `b1'`, and S = b1'. A hand-set,
NOT reachable fixture: `b1'` is in `base.blocks` but `B1'` is not in `fg.TF`,
so the correspondence "base list = Σ.T erased" (CStoreInv `baseTree`) does not
hold. Use it only for the Task 3 read and reconcile tests, never with an
invariant. -/
def stR0 : State 4 :=
  { fg := stF, base := { GridCO.initial 4 with
      blocks := [.genesis, b1, eraseFG B2, eraseFG B3, b1'],
      genuine := [(1, some b1'), (2, some .genesis)],
      obligations := [(b1', 2, 100)], stableRecord := b1' },
    fastWrite := [(1, [b1'])] }

/-- Reconcile deletes the lease, empties the conflicting result but keeps its
label, keeps the compatible result, filters fastWrite, and sets S := F (spec 874–894). -/
example : (reconcile stR0).base.obligations = [] ∧
    (reconcile stR0).base.genuine = [(1, none), (2, some .genesis)] ∧
    (reconcile stR0).fastWrite = [(1, [])] ∧
    (reconcile stR0).base.stableRecord = b1 ∧
    (reconcile stR0).base.blocks = stR0.base.blocks := by decide
/-- act(Σ) keeps the cumulative list but drops `b1'` (spec 360–361). -/
example : b1' ∈ stR0.base.blocks ∧ b1' ∉ (actView stR0).blocks ∧
    b1 ∈ (actView stR0).blocks := by decide
/-- A compatible S ahead of F stays (spec 565). -/
example : (normalizeS
      { stR0 with base := { stR0.base with stableRecord := eraseFG B3 } }).base.stableRecord =
    eraseFG B3 := by decide
example : blockExcluded stR0 b1' = true ∧ blockExcluded stR0 .genesis = false := by decide
/-- G3: `Σ.s = ⌊t / 4Δ⌋` (spec 711); with Δ = 1, times 0, 13 and 16 give slots 0, 3, 4. -/
example : State.slot pT (initial 4) = 0 ∧
    State.slot pT { base := { GridCO.initial 4 with now := 13 } } = 3 ∧
    State.slot pT { base := { GridCO.initial 4 with now := 16 } } = 4 := by decide
```

  Run: `lake build AvailableChainFGSA.Tests.Smoke`. Expected: FAIL.
- [x] **Step 2: Write `Model/Store.lean`.** Imports: `AvailableChainFGSA.Model.Objects`.

```lean
/-- [spec 339–353, 486–503; M1] The composite node store. `base` holds the SA
fields and the erased cumulative tree (`Σ.T`, stamps, vote pool, saved results
`Σ.genuine`, leases `Σ.lease` as `obligations`, `S` as `stableRecord`). `base`
also has five model-only caches that no FG-SA duty or output reads: `frozen`,
`early`, `releaseSnapshots`, `goldfishRecord` (G) and `base.proposals` (DQ8).
`fg` holds `Σ.T` with rows and the FG caches `F, J, h_j, hmax`. `proposals`
holds the admitted proposal wires with their signed rows (for the HEAD merge and
row inclusion; MetaInv, Task 12). `rowPool` is `Σ.attestations`. `fastWrite` is
`Σ.fastWrite`. `σ[B]` is `derive p.E p.cfg B`, not a field. Λ is not a field
(DQ4). -/
structure State (n : Nat) where
  base : GridCO.State n := GridCO.initial n
  fg : Store (Fin n) := Store.init
  proposals : List (Wire n) := []
  rowPool : List (RowWire n) := []
  fastWrite : List (Slot × List Block) := []

variable {n : Nat}

def initial (n : Nat) : State n := {}

/-- [spec 711] The store slot `Σ.s`. -/
def State.slot (p : Params) (st : State p.n) : Slot := p.slotOf st.base.now

/-- [spec 558–561, 789–802] The outputs. -/
def finalized (st : State n) : FGBlock (Fin n) := st.fg.F
def confirmed (st : State n) : Block := st.base.stableRecord
def stable (st : State n) : Block := confirmed st

/-- [spec 360–361] Membership in `act(Σ)` of an erased block: compatibility with F. -/
def activeCompatible (st : State n) (b : Block) : Bool :=
  Block.compatible b (eraseFG st.fg.F)

/-- [spec 363–366; M2] The SA base as the SA code reads it: the stored state with
its block list filtered to `act(Σ)`. Every other field is the stored one. -/
def actView (st : State n) : GridCO.State n :=
  { st.base with blocks := st.base.blocks.filter (activeCompatible st) }

/-- [spec 363–366; M2] Run a GridCO step on the active view, then keep the cumulative block
list. Used only with steps that do not change `blocks` (Task 7 proves it). -/
def onView (f : GridCO.State n → GridCO.State n) (st : State n) : State n :=
  { st with base := { f (actView st) with blocks := st.base.blocks } }

/-- [spec 565–566, 778–781, 890–892] `S := F` when `F ⋠ S`. -/
def normalizeS (st : State n) : State n :=
  if Block.preceq (eraseFG st.fg.F) st.base.stableRecord then st
  else { st with base := { st.base with stableRecord := eraseFG st.fg.F } }

/-- [spec 474–484, 874–894; K1, K3] `reconcile_with_finality`: delete the leases
whose target conflicts with F; filter every fastWrite set; empty each
conflicting saved result and keep its label; then `S := F` if `F ⋠ S`. It
writes no other field: not `fg`, not the blocks, stamps, pools or proposals,
not `goldfishRecord` (DQ8). -/
def reconcile (st : State n) : State n :=
  let ok := activeCompatible st
  normalizeS { st with
    base := { st.base with
      obligations := st.base.obligations.filter (fun row => ok row.1)
      genuine := st.base.genuine.map (fun row => (row.1, row.2.filter ok)) }
    fastWrite := st.fastWrite.map (fun row => (row.1, row.2.filter ok)) }

/-- [spec 293–294] `Σ.lease[B]`: the deadline of the first lease row on `b`. SA
writes one level only, so there is at most one row per target (CStoreInv
`leaseKeys`, Task 11). -/
def leaseOf (st : State n) (b : Block) : Option Time :=
  (st.base.obligations.find? (fun row => row.1 == b)).map (fun row => row.2.2)

/-- [spec 297–298, 457–461] `Σ.fastWrite[r]`, or `none` if the gate at `d_r` did
not run. There is at most one row per label (CStoreInv `fastDom`, Task 11). -/
def fastWriteAt (st : State n) (r : Slot) : Option (List Block) :=
  (st.fastWrite.find? (fun row => row.1 == r)).map Prod.snd

/-- [spec 178–182; DQ9] DC `NamedReceipt.excludes` as a store predicate: a block
that conflicts with F. A stored finalized ancestor is not excluded. -/
def blockExcluded (st : State n) (b : Block) : Bool := !activeCompatible st b
```

- [x] **Step 3: Run it; it passes.** `lake build --wfail AvailableChainFGSA.Tests.Smoke`. If a test value differs from the expected value, compute it by hand from the spec. A real difference is a finding: report it and do not change the expectation to match the code.
- [x] **Step 4: Review gate G3 and CHECKPOINT.** Commit `FGSA model: store, active view, reconcile`.
  Execution notes (2026-09-29): every planned test value agreed with the hand computation. Changes from the text above: (1) one test line is wrapped for the 100-column linter; (2) docstrings with spec lines on `initial`, `confirmed` and `stable`; (3) extra tests, added after the G1 finding on coverage: `initial`, the outputs, `leaseOf`, `fastWriteAt`, a compatible lease on F and below F that reconcile keeps, the fields that reconcile does not write (`fg`, `proposals`, `rowPool`, `goldfishRecord`), and `onView` (the step reads `act(Σ)`; the cumulative list comes back).

**G3 dispositions** (review of `68ece14`: PASS; 0 blocking, 0 major, 4 minor). G3 is closed. The reviewer confirmed that `reconcile` deletes every obligation row of a conflicting target, as the spec requires (`Σ.lease[B]` has no level; the SA readers `liveRoot`, the gate veto and `expire` ignore the level).

```text
┌─────┬──────────────────────────────────────────────────────────────────────────┐
│ G3  │ Disposition                                                              │
├─────┼──────────────────────────────────────────────────────────────────────────┤
│ 1   │ The `stR0` docstring says it breaks "base list = Σ.T erased" (b1' is in  │
│     │ base.blocks, B1' is not in fg.TF). No later task reuses stR0, so B1' is  │
│     │ not added to fg.TF.                                                      │
│ 2   │ A decide test of `State.slot` (times 0, 13, 16 give slots 0, 3, 4).      │
│ 3   │ Task 11: `leaseKeys` comes from the one constant level of                │
│     │ `writeObligation` under `slowLeasePolicy`; new result                    │
│     │ `leaseOf_eq_deadlineOf` (Task 11, Produces and Step 2).                  │
│ 4   │ G6 check list (Task 6, Step 4; Global Constraints, model-only caches):   │
│     │ `frozen` keeps saved resolved pools and a frozen domain that reconcile   │
│     │ does not clear; no composite duty may reuse GridCO `act` or the voter    │
│     │ views after an F advance.                                                │
└─────┴──────────────────────────────────────────────────────────────────────────┘
```

---

### Task 4: Handlers: votes, rows, blocks

**Files:**
- Create: `AvailableChainFGSA/Model/Handlers.lean`
- Modify: `AvailableChainFGSA.lean`, `AvailableChainFGSA/Tests/Smoke.lean`

**Interfaces:**
- Consumes: Task 3; `GridCO.admitVote`, `GridCO.admitProposal`, `SimplexFG.on_block`, `SimplexFG.pickPair`.
- Produces: `admitHead`, `admitRow`, `parentFG`, `fgBlock`, `blockAccepted`, `admitBlock`, `process`, `wellFormed`.

- [x] **Step 1: Write the failing tests.** The proposal wires carry the rows of the FG test blocks. Row rounds: `B1` (slot 1) has round-0 rows; `B2`, `B3` (slots 2, 3) have round-1 rows (`pT.round 2 = pT.round 3 = 1`).

```lean
def rowsOf (r : Nat) (B : FGBlock (Fin 4)) : List (RowWire 4) :=
  B.rows.map (fun a => ⟨.seat (.fg r) a.signer, RowBody.ofRow a⟩)
def wProp (B : FGBlock (Fin 4)) (r : Nat) (raw : List (HeadWire 4) := []) : Wire 4 :=
  ⟨.proposer B.slot, .proposal (eraseFG B) raw [] (rowsOf r B)⟩
/-- Now = 12: slot 3, round 1. -/
def st0 : State pT.n := { base := { GridCO.initial 4 with now := 12 } }
def stA : State pT.n := [wProp B1 0, wProp B2 1, wProp B3 1].foldl (process pT) st0

/-- The FG part is the FG module's store after the same blocks (K4). -/
example : stA.fg.TF = stF.TF ∧ stA.fg.F = B1 ∧ stA.fg.J = stF.J ∧
    stA.fg.h_j = stF.h_j ∧ stA.fg.h_max = stF.h_max := by decide
/-- The base holds the erased tree (spec 355–358). -/
example : stA.base.blocks = [.genesis, b1, eraseFG B2, eraseFG B3] := by decide
/-- F moved to B1: S := F (spec 890–892). -/
example : stA.base.stableRecord = b1 := by decide

/-- Review Focus 2 (audit N1). A label-2 vote and a fresh round-1 row: separate
calls admit both at stA (slot 3, round 1). -/
def v2 : HeadWire 4 := ⟨.seat (.head 2) 0, eraseFG B2⟩
def rF : RowWire 4 := ⟨.seat (.fg 1) 3, ⟨.vote 1 ⟨77⟩ true, none⟩⟩
example : (process pT stA ⟨v2.auth, .head v2.payload⟩).base.votes ≠ stA.base.votes ∧
    (admitRow pT stA rF).rowPool = stA.rowPool ++ [rF] := by decide
/-- A checked slot-3 block on genesis conflicts with F = B1. It carries `v2` and
`rF`. Refusal of `F ⋠ B` before unpacking (spec 808, 535–536): no block, no
stamp, no carried vote, no row, no FG change, no stored wire. -/
def wX : Wire 4 := ⟨.proposer 3, .proposal (.node .genesis 3 ⟨99⟩) [v2] [] [rF]⟩
example : wellFormed pT wX = true := by decide
example : (process pT stA wX).base.blocks = stA.base.blocks ∧
    (process pT stA wX).base.votes = stA.base.votes ∧
    (process pT stA wX).base.blockStamp = stA.base.blockStamp ∧
    (process pT stA wX).rowPool = stA.rowPool ∧
    (process pT stA wX).fg.TF = stA.fg.TF ∧
    (process pT stA wX).proposals = stA.proposals := by decide
/-- A duplicate block changes nothing (spec 806–807). -/
example : (process pT stA (wProp B2 1)).base.blocks = stA.base.blocks ∧
    (process pT stA (wProp B2 1)).proposals = stA.proposals ∧
    (process pT stA (wProp B2 1)).rowPool = stA.rowPool := by decide
/-- A row from the block's future (spec 815–817): a slot-1 block (round 0) with a
round-1 row fails the input check and is refused by the handler. -/
def wFut : Wire 4 := ⟨.proposer 1, .proposal (.node .genesis 1 ⟨98⟩) [] [] [rw 1 2 (rowT 2)]⟩
example : wellFormed pT wFut = false ∧ (process pT st0 wFut).fg.TF = st0.fg.TF := by decide
/-- Review Focus 9 (M12): the same height-0 row fails alone and in a block; the
height-1 row passes in both forms. -/
def r0 : RowWire 4 := ⟨.seat (.fg 1) 2, ⟨.vote 0 genesisRoot false, none⟩⟩
def r1 : RowWire 4 := ⟨.seat (.fg 1) 2, ⟨.vote 1 genesisRoot false, none⟩⟩
example : wellFormed pT ⟨r0.auth, .row r0.payload⟩ = false ∧
    wellFormed pT ⟨.proposer 3, .proposal (.node .genesis 3 ⟨97⟩) [] [] [r0]⟩ = false ∧
    wellFormed pT ⟨r1.auth, .row r1.payload⟩ = true ∧
    wellFormed pT ⟨.proposer 3, .proposal (.node .genesis 3 ⟨97⟩) [] [] [r1]⟩ = true := by decide

/-- A handler-integration fixture (NOT a reachable state: the lease, the saved
result and the fast write on `b1'` are set by hand). `B1'` enters while
F = genesis; then `B1`, `B2`, `B3` move F to `B1`, and reconcile runs inside the
handler. -/
def stR1 : State pT.n :=
  let st := process pT st0 (wProp B1' 0)
  { st with
      base := { st.base with
        genuine := [(1, some b1')], obligations := [(b1', 2, 100)], stableRecord := b1' }
      fastWrite := [(1, [b1'])] }
def stR2 : State pT.n := [wProp B1 0, wProp B2 1, wProp B3 1].foldl (process pT) stR1
example : stR2.fg.F = B1 ∧ stR2.base.obligations = [] ∧
    GridCO.savedGenuine stR2.base 1 = some none ∧ stR2.fastWrite = [(1, [])] ∧
    stR2.base.stableRecord = b1 ∧ b1' ∈ stR2.base.blocks ∧
    b1' ∉ (actView stR2).blocks := by decide

/-- DQ2: a new block whose root is already stored is refused. -/
example : (process pT stA ⟨.proposer 3, .proposal (.node b1 3 B2.root) [] [] []⟩).fg.TF
    = stA.fg.TF := by decide
/-- The row pool admits at most two distinct rows per identity and round
(spec 433–439, 852–855), and only rows in the window (spec 848–851). -/
def rA (h : Nat) : RowWire 4 := ⟨.seat (.fg 1) 0, ⟨.vote h genesisRoot false, none⟩⟩
example : ([rA 1, rA 2, rA 3].foldl (admitRow pT) st0).rowPool = [rA 1, rA 2] := by decide
example : (admitRow pT st0 ⟨.seat (.fg 2) 0, ⟨.empty, none⟩⟩).rowPool = [] := by decide
```

  Before the build, check by hand that `⟨99⟩`, `⟨98⟩`, `⟨97⟩` and `⟨77⟩` are not roots of `B1`, `B2`, `B3`, `B1'` and that `rF` is not in `stA.rowPool`; change the numbers if they are. Run the build. Expected: FAIL.
- [x] **Step 2: Write `Model/Handlers.lean`.** Imports: `AvailableChainFGSA.Model.Store`.

```lean
/-- [spec 831–842] `on_goldfish_vote`: SA's vote pool, unchanged. -/
def admitHead (p : Params) (st : State p.n) (s : Slot) (i : Fin p.n) (b : Block) : State p.n :=
  { st with base := GridCO.admitVote p.toParams.engine st.base ⟨.seat s i, .head b⟩ }

/-- [spec 433–439, 844–857] `on_attestation`: a row of round `r` enters the pool
if `r` is in the window `[max 0 (r_now − w_F), r_now]`, it is not already
there, and its identity has fewer than two rows of round `r`. -/
def admitRow (p : Params) (st : State p.n) (a : RowWire p.n) : State p.n :=
  match a.decode? with
  | some (r, i, _) =>
      let now := p.round (st.slot p)
      let mine := st.rowPool.filter (fun c => c.decode?.map (fun x => (x.1, x.2.1)) == some (r, i))
      if r + p.wF < now || now < r || decide (a ∈ mine) || 2 ≤ mine.length then st
      else { st with rowPool := st.rowPool ++ [a] }
  | none => st

/-- [spec 519–522; M3] The stored FG parent of an erased block. `pickPair`
returns `none` on two candidates; Task 10 shows there is at most one. -/
def parentFG {n : Nat} (st : State n) (b : Block) : Option (FGBlock (Fin n)) :=
  pickPair st.fg.TF (fun P => decide (eraseFG P = b.parent))

/-- [spec 818–819, 902–912; M3] The FG block of an admitted proposal: the stored
parent, the slot and root of the wire block, and its rows. -/
def fgBlock {n : Nat} (P : FGBlock (Fin n)) (b : Block) (rows : List (RowWire n)) :
    FGBlock (Fin n) :=
  .node P b.slot b.root (rows.filterMap RowWire.toRow?)

/-- [spec 530–536, 806–817; M5, DQ2, DQ12, DQ14] The acceptance tests of
`on_block`, all before any write: not genesis; `b.slot ≤ Σ.s`; no stored block
has the root of `b`; `F ⪯ B`; `b.parent.slot < b.slot`; the slot-`b.slot`
proposer signs it; every row decodes as a row with round `≤ round(b.slot)`. The
parent test is `parentFG st b = some P`. -/
def blockAccepted (p : Params) (st : State p.n) (s : Slot) (b : Block)
    (P : FGBlock (Fin p.n)) (rows : List (RowWire p.n)) : Bool :=
  b != .genesis && decide (b.slot ≤ st.slot p) &&
    !decide (∃ Y ∈ st.fg.TF, Y.root = b.root) &&
    FGBlock.preceq st.fg.F (fgBlock P b rows) &&
    decide (b.parent.slot < b.slot) && s == b.slot &&
    rows.all (fun a => match a.decode? with
      | some (r, _, _) => decide (r ≤ p.round b.slot)
      | none => false)

/-- [spec 804–829; M6] `on_block`. On refusal the state does not change. On
acceptance: the SA block admission and the carried votes (SA code on the
cumulative base, with the erased block); the FG admission (`on_block` of the FG
module: insert, then `update_finality`); the proposal wire is stored; if F
moved, `reconcile`; then the carried rows pass `admitRow`. The FG acceptance
decides; if the base admission then refused the block, the state would diverge
(a block in Σ.T but not in the base list); `base_admitProposal_accepts`
(Task 10) excludes this under the store invariant. -/
def admitBlock (p : Params) (st : State p.n) (s : Slot) (b : Block)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) : State p.n :=
  match parentFG st b with
  | none => st
  | some P =>
      if blockAccepted p st s b P rows then
        let st1 : State p.n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base
            (baseProposal s b raw support) b (raw.map baseHead)
          fg := on_block p.E p.cfg st.fg (fgBlock P b rows)
          proposals := st.proposals ++ [⟨.proposer s, .proposal b raw support rows⟩] }
        let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
        rows.foldl (admitRow p) st2
      else st

/-- [spec 804–857] The delivery handler. It reads the wire only through
`Wire.decode` (J1). It does not run the input check (DQ14). -/
def process (p : Params) (st : State p.n) (o : Wire p.n) : State p.n :=
  match o.decode with
  | some (.vote s i b) => admitHead p st s i b
  | some (.row _ _ body) => admitRow p st ⟨o.auth, body⟩
  | some (.block s b raw support rows) => admitBlock p st s b raw support rows
  | none => st

/-- [spec 247–255, 505–518; M12, DQ9, DQ14] The input check, as a pure function
(T7 binds it). A vote: a HEAD seat. A row: an FG seat and a valid body. A block:
not genesis; the proposer key of its slot; every carried vote a HEAD seat of
slot `b.slot − 1`; support ⊆ votes; every carried row passes the SAME row check
(`RowWire.valid`). The flat wire carries the parent slot and the row rounds, so
the check also has `b.parent.slot < b.slot` and `round ≤ round(b.slot)` (DQ14;
`blockAccepted` keeps both, in the spec's place). -/
def wellFormed (p : Params) (o : Wire p.n) : Bool :=
  match o.decode with
  | some (.vote _ _ _) => true
  | some (.row _ _ body) => body.valid
  | some (.block s b raw support rows) =>
      b != .genesis && s == b.slot && decide (b.parent.slot < b.slot) &&
        raw.all (fun v => match v.decode? with
          | some (r, _, _) => r + 1 == b.slot
          | none => false) &&
        support.all (fun v => decide (v ∈ raw)) &&
        rows.all (fun a => a.valid && match a.decode? with
          | some (r, _, _) => decide (r ≤ p.round b.slot)
          | none => false)
  | none => false
```

- [x] **Step 3: Run it; it passes.** As in Task 3, Step 3.
- [x] **Step 4: Review gate G4 and CHECKPOINT.** Commit `FGSA model: handlers`.
  Execution notes (2026-09-29): `Model/Handlers.lean` is the code above verbatim. The four fixture roots are free (the FG test roots are 0, 1, 3, 5, 6), and `rF` (identity 3) is not in `stA.rowPool`. Every planned test value agreed with the build. Changes from the text above: (1) the `stR1` fixture had a structure-instance layout that Lean does not parse (a continuation line to the left of the first field); the fields are now on new lines, with the same values; (2) extra tests: a missing parent, a future slot, a wrong proposer slot, a vote outside the window, a wire that does not decode, an accepted block that passes its carried vote to the pool and stores its wire, and a carried row that the pool refuses but the FG block keeps (spec 540–541).

**G4 dispositions** (review of `6a7abab`: PASS; 0 blocking, 0 major, 3 minor). G4 is closed. The reviewer's mutation tests confirm that each acceptance condition is tested.

```text
┌─────┬──────────────────────────────────────────────────────────────────────────┐
│ G4  │ Disposition                                                              │
├─────┼──────────────────────────────────────────────────────────────────────────┤
│ 1   │ Task 10 `fg_on_block_accepts` has no `Inv0` hypothesis: `on_block`       │
│     │ accepts whenever `blockAccepted` passes (the four FG refusals fail by    │
│     │ `parentFG`, `fgBlock_notMem`, the F ⪯ B test and the slot test). Only    │
│     │ the base side needs the invariant.                                       │
│ 2   │ Smoke tests: the lower bound of the row window (now 16, round 2, w_F =   │
│     │ 1: round 0 refused, round 1 admitted) and a vote above Σ.s (label 4 at   │
│     │ slot 3 refused; label 3 admitted).                                       │
│ 3   │ `admitBlock` docstring: a base refusal after an FG acceptance would give │
│     │ a divergent state; `base_admitProposal_accepts` (Task 10) excludes it.   │
└─────┴──────────────────────────────────────────────────────────────────────────┘
```

---

### Task 5: Clock and the composite gate

**Files:**
- Create: `AvailableChainFGSA/Model/Clock.lean`
- Modify: `AvailableChainFGSA.lean`, `AvailableChainFGSA/Tests/Smoke.lean`

**Interfaces:**
- Consumes: Task 3; the fixture `stA` of Task 4 (audit N5: this is a real dependency); `SA.{confirmation, gate, release, prefixSupport, releaseThreshold, freezeTime, earlyTime, releaseTime, gateTime}`, `GridCO.{expire, freeze, earlyVotes, savedGenuine}`.
- Produces: `fastSet`, `gateStep`, `clockPre`, `clock`.

- [x] **Step 1: Write the failing tests.**

```lean
/-- An empty gate at d_2 = 14 (no votes): the result is saved as empty, the fast
set of label 2 is created empty, and S := F runs after the gate (spec 756–781). -/
def stG : State pT.n :=
  { stA with base := { stA.base with now := 14, stableRecord := .genesis } }
example : GridCO.savedGenuine (gateStep pT stG 2).base 2 = some none ∧
    fastWriteAt (gateStep pT stG 2) 2 = some [] ∧
    (gateStep pT stG 2).base.stableRecord = b1 := by decide
/-- Evaluate once: a second gate of label 2 writes nothing new (spec 756). -/
example : (gateStep pT (gateStep pT stG 2) 2).fastWrite = (gateStep pT stG 2).fastWrite := by decide
/-- The clock at 14 runs the gate of slot 2 and keeps the FG part (spec 718–720). -/
example : fastWriteAt (clock pT stA 14) 2 = some [] ∧ (clock pT stA 14).fg.F = stA.fg.F := by decide
```

  Add these gate tests (audit N1). Compute each expected value by hand from the spec before the build and write it in the test docstring:
  - **Successful fast gate.** The blocks of `stA` have stamp 12, which is after `e_2 = 10`, so use a new fixture `stS`: admit `B1` and `B2` at now = 8 (stamps 8), then admit two label-2 HEAD votes for `eraseFG B2` at now = 9 (seats 0 and 1; stamps 9 < `e_2`), then run `gateStep` at now = 14. Expected: the saved result is `some (eraseFG B2)`; `fastWriteAt … 2 = some [b1, eraseFG B2]` (the non-genesis active prefixes with `p ≥ τ = 2`); a lease on each with deadline `d_2 + L = 14 + 7 = 21`.
  - **Vetoed gate.** `stS` with a hand-set lease on a block that conflicts with `eraseFG B2` (for example `b1'`, after `B1'` is admitted at now = 8). Expected: the saved result is `some (eraseFG B2)`; `fastWriteAt … 2 = some []`; no new lease; S := F after the gate.
  - **Fast renewal, deadline unchanged.** `stS` with a hand-set lease `(b1, 2, 100)`. Expected: after the gate `leaseOf … b1 = some 100` (the max keeps 100), and `b1 ∈ fastWriteAt … 2` (a renewal counts also when the deadline does not change; spec 457–461).
  - **Slow-only renewal.** `stS` with ONE label-2 vote for `eraseFG B2` (seat 0) and a hand-set saved result `genuine := [(1, some (eraseFG B2))]`. The confirmation is `eraseFG B2` (score 1, one late voter); `prefixSupport` of `b1` is 1 < τ = 2, but `slowEligible` holds (k = 2, the label-1 result covers `b1`). Expected: a lease on `b1` with deadline 21, and `fastWriteAt … 2 = some []`.
  If `decide` is too slow for a test, keep it as a `#eval` and say so in the report.
- [x] **Step 2: Write `Model/Clock.lean`.** Imports: `AvailableChainFGSA.Model.Store`.

```lean
/-- [spec 761–775, 457–461] The fast-write set of gate `s`, computed on the
active view before the gate: empty if the result is empty or vetoed; else the
non-genesis active prefixes of the result that pass the fast test `p(s,B) ≥ τ`.
A renewal counts also when the deadline does not change. -/
def fastSet (p : Params) (v : GridCO.State p.n) (s : Slot) : List Block :=
  match SA.confirmation p.toParams v s with
  | none => []
  | some h =>
      if v.obligations.any (fun row => !Block.compatible row.1 h) then [] else
        v.blocks.filter (fun b => b != .genesis && Block.preceq b h &&
          decide (SA.releaseThreshold p.toParams ≤ SA.prefixSupport p.toParams v s b))

/-- [spec 754–782; M7, DQ5] `update_confirmation`: if label `s` is not saved,
run the SA gate on the active view and record `fastWrite[s]`; then `S := F`
if `F ⋠ S`, also after an empty or vetoed gate. -/
def gateStep (p : Params) (st : State p.n) (s : Slot) : State p.n :=
  let st := if (GridCO.savedGenuine st.base s).isSome then st else
    { onView (fun v => SA.gate p.toParams v s) st with
      fastWrite := st.fastWrite ++ [(s, fastSet p (actView st) s)] }
  normalizeS st

/-- [spec 683–694, 709–752; M8] The tick before the gate: set the time and
expire leases; the freeze and early caches (on the active view; model-only,
DQ8); the release at `q_{s−1}` (on the active view). The step order and the
time tests are those of `GridCO.clock` (`GridCO/Model/Protocol.lean:485`). -/
def clockPre (p : Params) (st : State p.n) (t : Time) : State p.n :=
  let q := p.toParams
  let st := { st with base := GridCO.expire { st.base with now := t } t }
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 3 * p.Δ && t == SA.freezeTime q fSlot then
    onView (fun v => GridCO.freeze q.engine v fSlot) st else st
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 2 * p.Δ && t == SA.earlyTime q eSlot then
    onView (fun v =>
      { v with early := v.early ++ [(eSlot, GridCO.earlyVotes q.engine v eSlot)] }) st
    else st
  let qSlot := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
  if 0 ≤ t - 5 * p.Δ && t == SA.releaseTime q qSlot then
    onView (fun v => SA.release q v qSlot) st else st

/-- [spec 683–694, 709–752; M8] The tick: `clockPre`, then the composite gate at
`d_{s−1}`. The duties are not here (Q1). -/
def clock (p : Params) (st : State p.n) (t : Time) : State p.n :=
  let st := clockPre p st t
  let dSlot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  if 0 ≤ t - 6 * p.Δ && t == SA.gateTime p.toParams dSlot then gateStep p st dSlot else st
```

- [x] **Step 3: Run it; it passes.** As in Task 3, Step 3.
- [x] **Step 4: Review gate G5 and CHECKPOINT.** Commit `FGSA model: clock and composite gate`.
  Execution notes (2026-09-29): `Model/Clock.lean` is the code above; the early-step line is wrapped for the 100-column linter (no other change). The four gate tests are in `Tests/Smoke.lean` with the fixtures `stS` (B1, B2 at now 8; two label-2 votes for B2 at now 9; now 14), `stV` (also B1' at now 8; hand-set lease on b1'), `stN` (hand-set lease `(b1, 2, 100)`) and `stW` (one vote; hand-set label-1 result b2), and the helpers `atTime` and `hv2`. Each docstring gives the hand computation (L = 7, τ = 2, d_2 = 14). Every value agreed with the build: successful gate → result b2, `fastWrite[2] = [b1, b2]`, leases with deadline 21, S = b2; vetoed gate → result b2 saved, `fastWrite[2] = ∅`, only the hand-set lease, S = F = genesis; renewal → deadline 100 kept, b1 in `fastWrite[2]`; slow-only → lease on b1 with deadline 21, `fastWrite[2] = ∅`. In the vetoed test F is genesis, so `S := F` has no visible effect there; the empty gate `stG` tests `S := F` with F = B1. Extra G5 coverage: expiry at the deadline (t = 20 keeps, t = 21 removes; no gate at those ticks), release at q_2 = 13 (the conflicting lease goes, the compatible one stays), and the freeze and early cache steps at 11 and 10. All tests use `decide`; none needed `#eval`.

**G5 dispositions** (review of `9929ac3` and `f1bb8a4`: PASS WITH FIXES; 0 blocking, 0 major, 4 minor). No model rule differs from the spec; the G2 script fixes are verified. G5 is closed.

```text
┌─────┬──────────────────────────────────────────────────────────────────────────┐
│ G5  │ Disposition                                                              │
├─────┼──────────────────────────────────────────────────────────────────────────┤
│ 1   │ New test `g'`: after a successful gate of label 2, leases and S are      │
│     │ cleared by hand; a second gate of label 2 writes neither (it fails       │
│     │ without the evaluate-once guard). The empty-gate test cannot show this.  │
│ 2   │ `stQ` docstring: hand-set, not reachable (its lease names `b1'`, which   │
│     │ is not in the store).                                                    │
│ 3   │ Freeze/early test docstring: the ticks set `stS` back from 14 to 11 and  │
│     │ 10, and at t = 10 = d_1 the clock also runs the gate of label 1.         │
│ 4   │ Expiry test docstring: at t = 21 = q_4 the release step also runs, with  │
│     │ no effect.                                                               │
│ R1  │ Risk R1 extended: plain `decide` can fail on a TRUE statement (max       │
│     │ recursion); use `decide +kernel` there.                                  │
└─────┴──────────────────────────────────────────────────────────────────────────┘
```

---

### Task 6: Frame reads and duties; Astra model check (G6)

**Files:**
- Create: `AvailableChainFGSA/Model/Frame.lean`
- Modify: `AvailableChainFGSA.lean`, `AvailableChainFGSA/Tests/Smoke.lean`

**Interfaces:**
- Consumes: Tasks 4–5; `SimplexFG.{storeControls, storeFrame, Controls.Z, Controls.lo, hOf, HeadFields, createRow, Record}`, `GridCO.{ghost, goldfishScore, voterCount, votesAt, stampBlock, stampVote, resolvedBefore, headTarget?, headLabel?, blockKnown}`.
- Produces: `controls`, `fullTree`, `erasedList`, `liveRoot`, `eligible`, `headInTree`, `proposalsAt`, `voterBlocks`, `headVotes`, `headSupport`, `headVote`, `getHead`, `proposerVotes`, `proposerSupport`, `chainWireRows`, `blockWireRows`, `proposalRows`, `propose`, `fgHead`, `fgBlockOf`, `deepest`, `fgSource`, `fgInputs`, `attest`.

- [x] **Step 1: Write the failing tests.**

```lean
/-- The FG action of round 1 at a_1 = 14, after the empty gate of slot 2:
fastWrite[2] is empty, so C_fg is none and the height pair is empty; there is
no fallback to S, the root, a slow lease or an older set (spec 669–677). -/
def stC0 : State pT.n := clock pT stA 14
example : fastWriteAt stC0 2 = some [] ∧ (fgInputs pT stC0).1 = none ∧
    (attest pT stC0 Record.initial 0).1.height_pair = .empty := by decide
/-- With a live fast write on B2 (set by hand), C_fg = B2 (the deepest member
of fastWrite[2] in the full filtered tree with a lease after a_1). -/
def stC1 : State pT.n :=
  { stC0 with
      fastWrite := [(2, [eraseFG B2])]
      base := { stC0.base with obligations := [(eraseFG B2, 2, 21)] } }
example : (fgInputs pT stC1).1 = some B2 := by decide
/-- An expired lease does not count (spec 1329: `lease[B] > Σ.t`). -/
example : (fgInputs pT
      { stC1 with base := { stC1.base with obligations := [(eraseFG B2, 2, 14)] } }).1 =
    none := by decide
/-- Band eligibility (spec 1068): at v_4 = 17 with no votes, the HEAD walks from
Z = F = B1 (no lease). B2 is eligible because σ[B1].h = 2 < lo = 3; B3 is not
(σ[B2].h = 3, no majority, not current). -/
example : headVote pT { stA with base := { stA.base with now := 17 } } 4 = eraseFG B2 := by decide
/-- DQ13: `deepest` breaks a depth tie by the greater root (spec 260–262). -/
example : deepest ({.node .genesis 1 ⟨5⟩ [], .node .genesis 2 ⟨9⟩ []} : Finset (FGBlock (Fin 4)))
    = some (.node .genesis 2 ⟨9⟩ []) := by decide
```

  Also add (compute the expected values by hand before the build): (a) a HEAD whose frozen support names a head that left `act(Σ)` after the freeze: the vote is in `headVotes` but not in `headSupport` (Review Focus 7); (b) a slot-`s` proposal that carries slot-`(s−1)` votes and then leaves `act(Σ)` because F moves to a conflicting block: its carried votes stay in `headVotes p st s` (spec 190–193; audit N1: the frozen-support test alone does not test this); (c) `proposalRows` drops a pool row that is already on the chain of the parent, and keeps at most two rows per identity and round with the pool rows first (spec 1255–1274).
- [x] **Step 2: Write `Model/Frame.lean`.** Imports: `AvailableChainFGSA.Model.Handlers`, `AvailableChainFGSA.Model.Clock`.

```lean
/-- [spec 616–633] The live frame: the FG module's store controls. -/
def controls (p : Params) (st : State p.n) : Controls (Fin p.n) := storeControls p.E p.cfg st.fg
/-- [spec 1033–1037] `get_filtered_block_tree(Σ)`. -/
def fullTree (p : Params) (st : State p.n) : Finset (FGBlock (Fin p.n)) :=
  storeFrame p.E p.cfg st.fg st.fg.TF
/-- [spec 1025–1037; model representation of a block set as the erased base list]
The erasure of an FG block set, in the order of the base list. -/
def erasedList {n : Nat} (st : State n) (X : Finset (FGBlock (Fin n))) : List Block :=
  st.base.blocks.filter (fun b => decide (∃ B ∈ X, eraseFG B = b))

/-- [spec 648–655, 1086–1098] `live_root`: the deepest live lease target in the
full filtered tree (ties: the greater root), else the FG root Z. -/
def liveRoot (p : Params) (st : State p.n) : Block :=
  let tree := fullTree p st
  let targets := st.base.obligations.filterMap (fun row =>
    if st.base.now < row.2.2 && decide (∃ B ∈ tree, eraseFG B = row.1) then some row.1 else none)
  targets.foldl (fun best b =>
    if best.depth < b.depth || (best.depth == b.depth && best.root < b.root) then b else best)
    (eraseFG (controls p st).Z)

/-- [spec 1063–1072] `goldfish_eligible` with the band floor: the parent's state
height is below `lo`, or a strict majority, or the store's current slot. -/
def eligible (p : Params) (st : State p.n) (raw support : List (GridCO.Wire p.n)) (b : Block) :
    Bool :=
  decide (∃ P ∈ st.fg.TF, eraseFG P = b.parent ∧ hOf p.E p.cfg P < (controls p st).lo) ||
    decide (GridCO.voterCount raw < 2 * GridCO.goldfishScore st.base.blocks raw support b) ||
    b.slot == st.slot p

/-- [spec 1074–1107] `get_head_in_tree`: GHOST from the live root over `tree`. -/
def headInTree (p : Params) (st : State p.n) (tree : List Block)
    (raw support : List (GridCO.Wire p.n)) : Block :=
  GridCO.ghost (liveRoot p st) tree (GridCO.goldfishScore st.base.blocks raw support)
    (eligible p st raw support)

/-- [spec 1109–1114] `get_head`: the full filtered tree. -/
def getHead (p : Params) (st : State p.n) (raw support : List (GridCO.Wire p.n)) : Block :=
  headInTree p st (erasedList st (fullTree p st)) raw support

/-- [spec 190–193, 1288–1293; helper] The admitted slot-`s` proposals, with their
vote lists. These stay readable when the block leaves `act(Σ)` (spec 190–193). -/
def proposalsAt {n : Nat} (st : State n) (s : Slot) :
    List (List (HeadWire n) × List (HeadWire n)) :=
  st.proposals.filterMap (fun o => match o.decode with
    | some (.block _ b raw sup _) => if b.slot = s then some (raw, sup) else none
    | _ => none)

/-- [spec 598–606, 1219–1226] `voter_processed_block_tree(Σ, s)`: blocks of Σ.T
received before `z_{s−1}`, and every ancestor of an admitted slot-`s` proposal. -/
def voterBlocks (p : Params) (st : State p.n) (s : Slot) : Finset (FGBlock (Fin p.n)) :=
  st.fg.TF.filter (fun B =>
    decide (GridCO.stampBlock st.base (eraseFG B) < SA.freezeTime p.toParams (s - 1)) ||
    decide (∃ P ∈ st.fg.TF, P.slot = s ∧ FGBlock.Preceq B P))

/-- [spec 606–612, 1283–1294] The HEAD raw merge: pool votes of slot `s − 1`
received before `z_{s−1}`, and the slot-`(s−1)` votes of every admitted slot-`s`
proposal. -/
def headVotes (p : Params) (st : State p.n) (s : Slot) : List (GridCO.Wire p.n) :=
  let frozenArm := (GridCO.votesAt st.base (s - 1)).filter (fun o =>
    decide (GridCO.stampVote st.base o < SA.freezeTime p.toParams (s - 1)))
  let carried := ((proposalsAt st s).flatMap (fun row => row.1.map baseVote)).filter
    (fun o => GridCO.headLabel? o == some (s - 1))
  (frozenArm ++ carried).eraseDups

/-- [spec 423–430, 1286–1293] The HEAD support merge: pool votes resolved
before `z_{s−1}` against the CURRENT `act(Σ)`; the declared support of every
admitted slot-`s` proposal whose head is in Σ.T with a valid slot. -/
def headSupport (p : Params) (st : State p.n) (s : Slot) : List (GridCO.Wire p.n) :=
  let frozenArm := (GridCO.votesAt st.base (s - 1)).filter (fun o =>
    GridCO.resolvedBefore (actView st) o (SA.freezeTime p.toParams (s - 1)))
  let carried := ((proposalsAt st s).flatMap (fun row => row.2.map baseVote)).filter (fun o =>
    GridCO.headLabel? o == some (s - 1) &&
      match GridCO.headTarget? o with
      | some h => GridCO.blockKnown st.base h && decide (h.slot ≤ s - 1)
      | none => false)
  (frozenArm ++ carried).eraseDups

/-- [spec 1276–1302] `goldfish_vote` at `v_s`: genesis at slot 0; else the head
of the filtered voter view (live controls, M9) from the live root. Condition
(G6 O-m3): the spec sets `s ← Σ.s` (spec 1278), and `eligible` reads `Σ.s`, so
this agrees with the spec only when `s = st.slot p`; the caller (T7) must
guarantee it. -/
def headVote (p : Params) (st : State p.n) (s : Slot) : Block :=
  if s = 0 then .genesis else
    headInTree p st (erasedList st (storeFrame p.E p.cfg st.fg (voterBlocks p st s)))
      (headVotes p st s) (headSupport p st s)

/-- [spec 1240–1243] The proposer's votes: every slot-`(s−1)` pool vote; the
support: those that resolve now (active head, valid slot). -/
def proposerVotes {n : Nat} (st : State n) (s : Slot) : List (GridCO.Wire n) :=
  GridCO.votesAt st.base (s - 1)
/-- [spec 1240–1243] The proposer's support: the pool votes that resolve now
(head in `act(Σ)`, valid slot). -/
def proposerSupport {n : Nat} (st : State n) (s : Slot) : List (GridCO.Wire n) :=
  (proposerVotes st s).filter (fun o => match GridCO.headTarget? o with
    | some h => GridCO.blockKnown (actView st) h && decide (h.slot ≤ s - 1)
    | none => false)

/-- [spec 552–553, 1264–1265; helper] The signed rows of the stored blocks on the chain
of `H`. -/
def chainWireRows {n : Nat} (st : State n) (H : Block) : List (RowWire n) :=
  (st.proposals.filterMap (fun o => match o.decode with
    | some (.block _ b _ _ rows) => if Block.preceq b H then some rows else none
    | _ => none)).flatten
/-- [spec 550–551, 1261–1263; helper] The rows with a round in `I` of the stored blocks
of a slot in a round of `I`. -/
def blockWireRows (p : Params) (st : State p.n) (I : Nat → Bool) : List (RowWire p.n) :=
  (st.proposals.filterMap (fun o => match o.decode with
    | some (.block _ b _ _ rows) =>
        if I (p.round b.slot) then some (rows.filter (fun a => (a.round?.map I).getD false))
        else none
    | _ => none)).flatten

/-- [spec 544–556, 1255–1274] `proposal_attestations(Σ, H)`: pool rows and
stored-block rows of the window `I = [max 0 (r − w_F), r]`, without rows on the
chain of `H`; per identity and round, every pool row, then distinct block rows
until there are two. Rows are grouped by their decoded `(round, identity)`, as in
`admitRow` (G6 O-m6). -/
def proposalRows (p : Params) (st : State p.n) (H : Block) : List (RowWire p.n) :=
  let r := p.round (st.slot p)
  let inI : Nat → Bool := fun r' => decide (r ≤ r' + p.wF) && decide (r' ≤ r)
  let onChain := chainWireRows st H
  let A := st.rowPool.filter (fun a => (a.round?.map inI).getD false && !decide (a ∈ onChain))
  let A' := (blockWireRows p st inI).filter (fun a => !decide (a ∈ onChain) && !decide (a ∈ A))
  A'.foldl (fun acc a =>
    let key := fun (x : RowWire p.n) => x.decode?.map (fun y => (y.1, y.2.1))
    if decide (a ∈ acc) || 2 ≤ (acc.filter (fun x => key x == key a)).length then acc
    else acc ++ [a]) A

/-- [spec 1236–1253; DQ10] `propose_block` at `t_s`, `s > 0`. The root formula
is GridCO's; it is not a content code and it can collide (DQ10). Condition
(G6 O-m3): the spec sets `s ← Σ.s` (spec 1238), and `eligible` and
`proposalRows` read `Σ.s`, so this agrees with the spec only when
`s = st.slot p`; the caller (T7) must guarantee it. -/
def propose (p : Params) (st : State p.n) (s : Slot) : Option (Msg p.n) :=
  if s = 0 then none else
    let raw := proposerVotes st s
    let sup := proposerSupport st s
    let H := getHead p st raw sup
    some (.proposal (.node H s ⟨s * (H.root.value + 1)⟩) (raw.filterMap liftHead?)
      (sup.filterMap liftHead?) (proposalRows p st H))

/-- [spec 1318–1323] The finality head: `get_head` with the current-slot votes
and their active resolved subset. -/
def fgHead (p : Params) (st : State p.n) : Block :=
  let s := st.slot p
  let raw := GridCO.votesAt st.base s
  let sup := raw.filter (fun o => match GridCO.headTarget? o with
    | some h => GridCO.blockKnown (actView st) h && decide (h.slot ≤ s)
    | none => false)
  getHead p st raw sup

/-- [spec 1324–1326; helper] The stored FG block of an erased block (exact under CStoreInv:
Task 11, `fgBlockOf_spec`). -/
def fgBlockOf {n : Nat} (st : State n) (b : Block) : Option (FGBlock (Fin n)) :=
  pickPair st.fg.TF (fun B => decide (eraseFG B = b))
/-- [spec 260–262, 1327–1335; DQ13] The deepest member (depth of the erasure);
ties: the greater root. `deepest ∅ = none`. For a nonempty set, `none` only if
two distinct maximal candidates share both depth and root; a tie between
members that are not maximal does not cause `none`. For a nonempty subset of
Σ.T, the result is `some` (Task 11, `deepest_spec`). -/
def deepest {n : Nat} (X : Finset (FGBlock (Fin n))) : Option (FGBlock (Fin n)) :=
  pickPair X (fun B => decide (∀ C ∈ X, (eraseFG C).depth < (eraseFG B).depth ∨
    ((eraseFG C).depth = (eraseFG B).depth ∧ C.root.value ≤ B.root.value)))

/-- [spec 666–677, 1327–1335] `C_fg`: the deepest block of the full filtered
tree that is in `fastWrite[rR]` and has a lease deadline after now. The set is
the one of the scheduled gate `d_{rR}`; there is no older set and no fallback. -/
def fgSource (p : Params) (st : State p.n) : Option (FGBlock (Fin p.n)) :=
  let r := p.round (st.slot p)
  let fw := (fastWriteAt st (r * p.R)).getD []
  deepest ((fullTree p st).filter (fun B => decide (eraseFG B ∈ fw) &&
    match leaseOf st (eraseFG B) with
    | some d => decide (st.base.now < d)
    | none => false))

/-- [spec 1315–1338] `get_fg_vote`: the source and the head fields of the
finality head. The fallback fields are unreachable under CStoreInv (Task 11,
`fgHead_stored`, `fgBlockOf_spec`). -/
def fgInputs (p : Params) (st : State p.n) : Option (FGBlock (Fin p.n)) × HeadFields :=
  (fgSource p st, match fgBlockOf st (fgHead p st) with
    | some Hd => HeadFields.ofBlock p.E p.cfg Hd
    | none => ⟨0, genesisRoot, 0⟩)

/-- [spec 1304–1313, 1391–1399; DQ4, M13] `attest` without emission: the row
body and the new record (a projection of the client: no `σ.nj`, no
`Λ.timeouts`). The identity `i` is supplied by the caller (Q1). -/
def attest (p : Params) (st : State p.n) (Λ : Record) (i : Fin p.n) : RowBody × Record :=
  let x := fgInputs p st
  let y := createRow p.E p.cfg Λ i x.1 x.2
  (RowBody.ofRow y.1, y.2)
```

  The old findings (a) and (b) of revision 1 are now proof obligations of Task 11 (`deepest_spec`, `fgBlockOf_spec`, `fgHead_stored`). The smoke tests compare the row-body projection of `attest`, not a `Record` (a record holds functions).
- [x] **Step 3: Run it; it passes.** As in Task 3, Step 3.
  Execution notes (2026-09-29): `Model/Frame.lean` is the code above; four signature or body lines are wrapped for the 100-column linter (no other change). The `stC1` fixture and the expired-lease test are re-laid out (the same structure-instance layout problem as `stR1`; same values). Every planned value agreed with the build. Extra tests (a)–(c) are in `Tests/Smoke.lean` with the hand computation in each docstring: (a) `stH0`/`stH`: a label-2 vote for `b1'` (stamp 9 < z_2 = 11) is in both HEAD merges while F = genesis; after F moves to B1 it stays in `headVotes` and leaves `headSupport`; (b) `stX`: the slot-3 proposal `xB` on `b1'` leaves `act(Σ)`, and its carried vote (pool stamp 12 ≥ 11, so not in the frozen arm) stays in `headVotes` through the proposal arm; (c) `stP`: for H = b2 the rows of B1, B2 (on the chain) drop, the pool rows of B3 and `q 1`, `q 2` stay in pool order, and the block row `q 3` drops (identity 3 already has two pool rows). Fallback (R1): test (c) uses `decide +kernel`; plain `decide` and the `Bool` form reach the elaborator's recursion limit on the state `stP` (even for `yB ∈ stP.base.blocks`); `#eval` gave `true` for the three conjuncts (not committed). Extra G6 coverage: `liveRoot` (a live lease on b2; an expired lease; a lease outside the full filtered tree), `propose` at t_4 = 16 (block `node b2 4 ⟨24⟩`, rows of B3), `fgHead`/`fgInputs` at `stA` (b3; the head fields of B3), and `attest` with the source B2 (no finality pair; height pair `.vote 3 σ[B2].T_h.root false`). No duty reads `frozen`, `early`, `releaseSnapshots`, `goldfishRecord` or `base.proposals`, and none calls GridCO `act` or the voter views (grep).
- [x] **Step 4: Astra model check (review gate G6).** Before any STORE proof task (Tasks 7–12; Task 2 does not depend on the model), start a Codex astra job: compare `Model/*.lean` line by line with the spec lines in each docstring and with the tree-read inventory; check that no duty or output reads a model-only cache (Global Constraints); check M11 (no free `n` next to `p`) and J1 (no auth match outside the decoders); check (G3 minor 4) that no composite duty reuses GridCO `act`, `voterView`, `voterSupportView` or `voterTree` (`GridCO/Model/Protocol.lean:250–273`): they read `frozen`, whose saved resolved pools and frozen domain `reconcile` does not clear, so after an F advance they would bypass the read-time resolution test (spec 429–430: "a saved resolved flag cannot bypass this test"). Output `docs/audit/fgsa-model-check-report.md` (blocking, major, minor; verdict). Fix every blocking and major finding in the model and in this plan, with new or changed smoke tests. Re-run the build.
- [x] **Step 5: CHECKPOINT.** Commit `FGSA model: frame reads and duties`.
  Execution notes (2026-09-29): the checkpoint is `d5171fc`. G6 ran two reviews of it: the Astra model check r195 (`docs/audit/fgsa-model-check-report.md`: PASS WITH FIXES; 0 blocking, 0 major, 5 minor) and an Opus review (`docs/audit/fgsa-task6-opus-review.md`: PASS WITH FIXES; 0 blocking, 1 major, 6 minor). The G6 fold is one commit. It adds 15 tests in `Tests/Smoke.lean`, each with a hand computation in its docstring. For each new test, a scratch file (not committed) defines the plausible wrong rule and proves with `decide` or `decide +kernel` that the wrong rule gives a different value; `#eval` printed the wrong values. Six new tests use `decide +kernel` (R1). The model rule changes only in `proposalRows` (item 9). The plan's code blocks for `Objects.lean` and `Store.lean` keep older docstrings in a few places; the Lean files are authoritative for docstrings and anchors.

**G6 dispositions** (Astra N1–N5, Opus MAJOR 1 and MINOR 1–6; lead items 1–9). No model rule differs from the spec. G6 is closed when the lead accepts this fold.

```text
┌──────┬─────────────────┬───────────────────────────────────────────────────────────────┐
│ Item │ Findings        │ Disposition (negative control: wrong rule → wrong value)      │
├──────┼─────────────────┼───────────────────────────────────────────────────────────────┤
│ 1    │ Opus MAJOR 1;   │ Four HEAD tests. `stE`: a late B2 outside the slot-3 view,    │
│      │ Astra N1        │ head b1 (full filtered tree → b2). `atTime stS 13`: the       │
│      │                 │ merges make b2 the head (empty merges → b1). `stE3`: B2 enters│
│      │                 │ the view as an ancestor of the slot-3 proposal x3, head x3 (no│
│      │                 │ proposal arm → b1). `stK`: `Y` outside the view makes the     │
│      │                 │ live store contested (Z = genesis, lo = 3), head childA       │
│      │                 │ (controls from the view → X; full tree → Y).                  │
│ 2    │ Astra N2        │ `stXs`: nonempty carried support; the proposal `xB` and the   │
│      │                 │ head `b1'` are outside act(Σ) but in Σ.T (no carried arm →    │
│      │                 │ []). `stB`: the pool refuses `q 3`; the on-chain `q 1` leaves │
│      │                 │ its group, so the block arm includes `q 3` (block arm [] →    │
│      │                 │ `q 3` missing). At now 16 the off-chain round-0 row `r0z` of  │
│      │                 │ the stored block `zB` is outside the window (no pool window,  │
│      │                 │ or no row filter in the block arm → `r0z` included).          │
│ 3    │ Astra N3;       │ `stF3` (hand-set): older set fastWrite[0] = [b1], a slow-only │
│      │ Opus MINOR 1    │ lease on b2, fastWrite[2] = [b1'] with B1' in Σ.T but outside │
│      │                 │ the full filtered tree: C_fg = none (older set → B1; any live │
│      │                 │ lease → B2; Σ.T without the filter → B1'). `stF4`: two fast   │
│      │                 │ targets, C_fg = B2 (first member → B1). `liveRoot` on `stR2`  │
│      │                 │ with a lease on the stored `b1'`: b1 (Σ.T → b1'). `stEL`: the │
│      │                 │ live root b2 is outside the slot-3 view; the walk starts      │
│      │                 │ there: head b2 (live root from the view → b1).                │
│ 4    │ Astra N5;       │ `stK`: the finality head is Y; σ[Y] = (1, genesis, 0) differs │
│      │ Opus MINOR 2    │ from the live cache (J = B1a, h_j = 2) (cache fields →        │
│      │                 │ (2, B1a, 1)). No source, but the finality pair (1, genesis)   │
│      │                 │ and lock[1] (no pair without a source → none). The record of  │
│      │                 │ `attest` on `stC1` (target[3], no timeout, no lock) and on    │
│      │                 │ `stK` (lock[1]) (unchanged record → none).                    │
│ 5    │ Astra N4        │ Spec anchors on the helpers (`[spec …; helper]` or `[spec …;  │
│      │                 │ model representation …]`) in Objects, Store, Handlers and     │
│      │                 │ Frame. Step 4 quotation anchor corrected to spec 429–430.     │
│ 6    │ Opus MINOR 3    │ `headVote`, `propose` docstrings: they agree with the spec    │
│      │                 │ only when `s = st.slot p`. Added to the T7 inputs (Task 13,   │
│      │                 │ Step 5; Open questions) and to Known limits.                  │
│ 7    │ Opus MINOR 4    │ Known limits: `goldfishScore` needs support ⊆ raw (DQ14).     │
│ 8    │ Opus MINOR 5    │ Local `frozen` renamed `frozenArm` in `headVotes`,            │
│      │                 │ `headSupport`.                                                │
│ 9    │ Opus MINOR 6    │ Choice: group by decode. `proposalRows` counts rows per       │
│      │                 │ decoded `(round, identity)`, the key of `admitRow`. All       │
│      │                 │ earlier tests keep their values. Edge (lead, G6 check): a     │
│      │                 │ row that does not decode has the key `none`, so all such rows │
│      │                 │ would share one group. No candidate is such a row, on any     │
│      │                 │ store: the `round?` filter of `proposalRows` and              │
│      │                 │ `blockWireRows` drops every row that does not decode (G12 m2; │
│      │                 │ MetaInv is not needed). So the grouping equals that of        │
│      │                 │ `admitRow`; no model change and no new filter.                │
└──────┴─────────────────┴───────────────────────────────────────────────────────────────┘
```

---

### Task 7: Write sets, active-view laws and the tick SA bridge

**Files:**
- Create: `AvailableChainFGSA/Statements/Invariants.lean`, `AvailableChainFGSA/Proofs/Fields.lean`, `AvailableChainFGSA/Proofs/ActView.lean`
- Modify: `AvailableChainFGSA.lean`

**Interfaces:**
- Consumes: Tasks 2–6; GridCO lemmas (check each signature; apply each lease-dependent one with `@… GridCO.slowLeasePolicy`): `admitVote_blocks` (`Map.lean:443`), `admitVote_obligations` (`Map.lean:455`), `admitVote_stable` (`History.lean:60`), `admitProposal_now` (`Map.lean:498`), `admitProposal_obligations` (`Map.lean:517`), `process_stable` (`History.lean:68`), `gate_blocks` (`Map.lean:940`), `release_subset` (`Basic.lean:140`), `confirmation_mem` (`RecordSlots.lean:150`).
- Produces: `Reachable`, `NestOK`, `SACompat`, `FastOrigin`, `CStoreInv` (Statements); the field lemmas; `actView_onView`; the six `bp.activeView.v1` items; `clock_eq_saClock_offGate`, `clock_eq_saClock_gate`.

- [x] **Step 1: Write `Statements/Invariants.lean`.** Imports: `AvailableChainFGSA.Model.Frame`, `AvailableChainKitFG.Correspondence`.

```lean
/-- The states that the local steps reach from the initial state: ticks at any
times and deliveries of any wire objects, in any order. No engine, no run.
This is an OVER-approximation (audit M1, N3): it allows unchecked inputs
(`process` does not run `wellFormed`, DQ14) and repeated or backward clocks.
Every store fact of this plan holds on it. Exact spec simulation needs the
scheduled event order and checked inputs of T7; in particular no statement of
this plan claims that the GridCO release test equals the spec's release on an
arbitrary store (the equivocation set of `GridCO.releaseCount` reads all stored
label-r votes; the spec reads the votes stamped before `q_r`; the two agree at
the first scheduled release tick). -/
inductive Reachable (p : Params) : State p.n → Prop
  | init : Reachable p (initial p.n)
  | tick {st : State p.n} (t : Time) : Reachable p st → Reachable p (clock p st t)
  | deliver {st : State p.n} (o : Wire p.n) : Reachable p st → Reachable p (process p st o)

/-- [bp comp.outputNesting.v2; K2] `F ⪯ S` (erased). -/
def NestOK {n : Nat} (st : State n) : Prop :=
  Block.Preceq (eraseFG st.fg.F) st.base.stableRecord

/-- [bp bp.activeView.v1, bp.reconcile.v1] Every live lease target, saved
nonempty result and fastWrite member is compatible with F. -/
def SACompat {n : Nat} (st : State n) : Prop :=
  (∀ row ∈ st.base.obligations, Block.Compatible row.1 (eraseFG st.fg.F)) ∧
  (∀ r C, (r, some C) ∈ st.base.genuine → Block.Compatible C (eraseFG st.fg.F)) ∧
  (∀ row ∈ st.fastWrite, ∀ b ∈ row.2, Block.Compatible b (eraseFG st.fg.F))

/-- [bp bp.leaseOrigins.v1 (fastWrite clause), bp.reconcile.v1 §6.3; K1; Opus M3]
The local fast-write origin invariant, relative to a block `Fb` (the erased F):
each member `B` of `fastWrite[r]` is below the saved body `C` of label `r`, or
below `Fb`. It needs no run: a gate writes a fresh label whose members are
prefixes of the saved result; reconcile keeps it (Task 9); no other step writes
`fastWrite` or `genuine`. -/
def FastOrigin {n : Nat} (Fb : Block) (st : State n) : Prop :=
  ∀ row ∈ st.fastWrite, ∀ B ∈ row.2,
    (∃ C, GridCO.savedGenuine st.base row.1 = some (some C) ∧ Block.Preceq B C) ∨
      Block.Preceq B Fb

/-- [bp bp.store.v1; K4 core; K1] The composite store invariant. `fg`: the FG
module's invariant (K4). `rootInj`: Σ.T is root-injective (DQ2). `baseTree`: the
base list is Σ.T erased. `Smem`: S is stored. `fastOrigin`, `fastDom`: the
fast-write origins (M3). `genuineKeys`, `leaseKeys`: one saved result per label
and one lease row per target, at the SA level (audit M4; used by `fastWriteAt`,
`leaseOf`). -/
structure CStoreInv (p : Params) (st : State p.n) : Prop where
  fg : KitFG.StoreInv p.E p.cfg st.fg
  rootInj : ∀ X ∈ st.fg.TF, ∀ Y ∈ st.fg.TF, X.root = Y.root → X = Y
  baseTree : ∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ st.fg.TF, eraseFG B = b
  saCompat : SACompat st
  Smem : st.base.stableRecord ∈ st.base.blocks
  fastOrigin : FastOrigin (eraseFG st.fg.F) st
  fastDom : (st.fastWrite.map Prod.fst).Nodup ∧
    ∀ r ∈ st.fastWrite.map Prod.fst, (GridCO.savedGenuine st.base r).isSome
  genuineKeys : (st.base.genuine.map Prod.fst).Nodup
  leaseKeys : (st.base.obligations.map Prod.fst).Nodup ∧
    ∀ row ∈ st.base.obligations, row.2.1 = SA.releaseThreshold p.toParams
```

- [x] **Step 2: Write the field statements** in `Proofs/Fields.lean`. For each step, one lemma per field group: `admitHead_fg`, `admitHead_base_blocks`, `admitHead_base_stable`, `admitHead_fastWrite`, `admitHead_genuine`; `admitRow_eq` (only `rowPool` changes: `admitRow p st a = st ∨ admitRow p st a = { st with rowPool := st.rowPool ++ [a] }`); `admitBlock_refused` (`admitBlock … = st` when `parentFG` is `none` or `blockAccepted` is false); `onView_fg`, `onView_base_blocks`, `onView_proposals`, `onView_rowPool`, `onView_fastWrite`; `normalizeS_fg`, `normalizeS_fields` (only `stableRecord`); `reconcile_fg`; `gateStep_fg`, `gateStep_base_blocks`; `clockPre_fg`, `clockPre_genuine`, `clockPre_fastWrite`; `clock_fg : (clock p st t).fg = st.fg`, `clock_base_blocks : (clock p st t).base.blocks = st.base.blocks`, `clock_proposals`, `clock_rowPool`. Also the exact gate effects that K1 and K6 need (Opus m1; Astra: "a separate exact fastSet equation is needed for source origins"):

```lean
theorem freeze_blocks (q : GridCO.Params) (v : GridCO.State n) (r : Slot) :
    (GridCO.freeze q v r).blocks = v.blocks
theorem release_blocks (p : SA.Params) (v : GridCO.State n) (r : Slot) :
    (SA.release p v r).blocks = v.blocks
/-- The SA gate keeps `blocks`. Proof: `@GridCO.gate_blocks GridCO.slowLeasePolicy
p.engine n v r` (the default instance would elaborate the GRID gate). -/
theorem saGate_blocks (p : SA.Params) (v : GridCO.State n) (r : Slot) :
    (SA.gate p v r).blocks = v.blocks
/-- [bp bp.leaseOrigins.v1; K1, K6] A fresh gate saves the confirmation of the
view and adds exactly `fastSet` of the view; a saved label changes neither. -/
theorem gateStep_fresh (p : Params) (st : State p.n) (s : Slot)
    (hnew : GridCO.savedGenuine st.base s = none) :
    GridCO.savedGenuine (gateStep p st s).base s = some (SA.confirmation p.toParams (actView st) s) ∧
    (∀ r ≠ s, GridCO.savedGenuine (gateStep p st s).base r = GridCO.savedGenuine st.base r) ∧
    (gateStep p st s).fastWrite = st.fastWrite ++ [(s, fastSet p (actView st) s)]
theorem gateStep_saved (p : Params) (st : State p.n) (s : Slot)
    (hs : (GridCO.savedGenuine st.base s).isSome) : gateStep p st s = normalizeS st
/-- [helper] Every member of `fastSet` is a non-genesis prefix of the confirmation. -/
theorem fastSet_prefix (p : Params) (v : GridCO.State p.n) (s : Slot) {B : Block}
    (hB : B ∈ fastSet p v s) :
    ∃ h, SA.confirmation p.toParams v s = some h ∧ Block.Preceq B h ∧ B ∈ v.blocks ∧
      B ≠ .genesis
```

- [x] **Step 3: Write the active-view statements** in `Proofs/ActView.lean` (Opus J2: all six items of bp01 §5; Astra: expose closure, genesis/F membership and unchanged pools and stamps).

```lean
/-- [bp bp.activeView.v1] (item 1, first part) `actView` keeps only stored blocks. -/
theorem actView_blocks (st : State n) (b : Block) :
    b ∈ (actView st).blocks ↔ b ∈ st.base.blocks ∧ Block.Compatible b (eraseFG st.fg.F)
/-- [bp bp.activeView.v1] (item 1) A ⊆ T, and g, F ∈ A. -/
theorem actView_genesis_F (p : Params) (st : State p.n) (h : CStoreInv p st) :
    Block.genesis ∈ (actView st).blocks ∧ eraseFG st.fg.F ∈ (actView st).blocks
/-- [bp bp.activeView.v1] (item 2) A is ancestor-closed. -/
theorem actView_ancestor_closed (p : Params) (st : State p.n) (h : CStoreInv p st)
    {b c : Block} (hb : b ∈ (actView st).blocks) (hc : Block.Preceq c b) :
    c ∈ (actView st).blocks
/-- [bp bp.activeView.v1] (item 3) For fixed Σ.T, a later F gives a smaller view. -/
theorem actView_antitone (st : State n) {F' : FGBlock (Fin n)} (h : FGBlock.Preceq st.fg.F F') :
    ∀ b ∈ (actView { st with fg := { st.fg with F := F' } }).blocks, b ∈ (actView st).blocks
/-- [bp bp.activeView.v1] (item 4) Heads above F are active, and so is every
path vertex from F to them. -/
theorem actView_path (p : Params) (st : State p.n) (h : CStoreInv p st) {B K : Block}
    (hK : K ∈ st.base.blocks) (hFB : Block.Preceq (eraseFG st.fg.F) B) (hBK : Block.Preceq B K) :
    K ∈ (actView st).blocks ∧ B ∈ (actView st).blocks
/-- [bp bp.activeView.v1] (item 5; DQ9) Exclusion is stable under F advances. -/
theorem blockExcluded_stable (st : State n) {F' : FGBlock (Fin n)} (h : FGBlock.Preceq st.fg.F F')
    (b : Block) (hx : blockExcluded st b = true) :
    blockExcluded { st with fg := { st.fg with F := F' } } b = true
/-- [bp bp.activeView.v1] (item 5, second sentence; G7 m1) View restriction
changes only the block list: every other SA field is the field of the base. -/
theorem actView_eq (st : State n) :
    actView st = { st.base with blocks := st.base.blocks.filter (activeCompatible st) }
/-- [bp bp.activeView.v1] (item 5, second sentence) View restriction changes no
signed pool, no stamp, no lease, no saved result, no S and no time. `actView_eq`
gives every other field. -/
theorem actView_fields (st : State n) :
    (actView st).votes = st.base.votes ∧ (actView st).voteStamp = st.base.voteStamp ∧
    (actView st).blockStamp = st.base.blockStamp ∧ (actView st).proposals = st.base.proposals ∧
    (actView st).genuine = st.base.genuine ∧ (actView st).obligations = st.base.obligations ∧
    (actView st).stableRecord = st.base.stableRecord ∧ (actView st).now = st.base.now
/-- [bp bp.activeView.v1] (item 6; K11 base case) If `K ⪯ F`, the active release
count against `K` is zero, for every label. -/
theorem actView_releaseCount_zero (st : State n) (q : GridCO.Params) (r : Slot) {K : Block}
    (hK : Block.Preceq K (eraseFG st.fg.F)) : GridCO.releaseCount q (actView st) r K = 0
/-- [bp bp.activeView.v1] (item 6) If `K ⪯ F`, every active block is compatible
with `K`, so a lease on `K` cannot veto an active genuine result. -/
theorem actView_noVeto (st : State n) {K : Block} (hK : Block.Preceq K (eraseFG st.fg.F)) :
    ∀ b ∈ (actView st).blocks, Block.Compatible K b
/-- [M2] Running a block-preserving step on the view commutes with `actView`. -/
theorem actView_onView (f : GridCO.State n → GridCO.State n)
    (hf : ∀ v, (f v).blocks = v.blocks) (st : State n) :
    actView (onView f st) = f (actView st)
/-- [helper] A vote admission commutes with `actView` (SA's vote pool reads no block). -/
theorem actView_admitHead (p : Params) (st : State p.n) (s : Slot) (i : Fin p.n) (b : Block) :
    actView (admitHead p st s i b) =
      GridCO.admitVote p.toParams.engine (actView st) ⟨.seat s i, .head b⟩
```

  For item 6 with a genesis or view result: `GridCO.confirmation` returns a member of the view's list (`confirmation_mem`), so `actView_noVeto` covers the result. `resolvedBefore` on the view tests `blockKnown (actView st)`, so a counted head is active; with `K ⪯ F` an active head is comparable with `K` (`block_preceq_total_of_common` if the head is below F; transitivity if F is below the head).
- [x] **Step 4: Write the tick SA bridge** in `Proofs/ActView.lean` (comp D3: "SA writes are copied back"; the block-step bridge is in Task 10, J3).

```lean
/-- [comp D3; M7, M8] Off the gate times, the composite tick is the SA tick on
the active view with the cumulative block list restored. -/
theorem clock_eq_saClock_offGate (p : Params) (st : State p.n) (t : Time)
    (hg : ¬ (0 ≤ t - 6 * p.Δ ∧ t = SA.gateTime p.toParams ((t - 6 * p.Δ) / (4 * p.Δ)).toNat)) :
    clock p st t = { st with base := { SA.clock p.toParams (actView st) t with blocks := st.base.blocks } }
/-- [comp D3; M7, DQ5; Opus m1] At a gate time of an unsaved label, the composite
tick is `normalizeS` of the SA tick on the active view, with EXACTLY the fast set
of the view before the gate added. -/
theorem clock_eq_saClock_gate (p : Params) (st : State p.n) (t : Time) (s : Slot)
    (hs : s = ((t - 6 * p.Δ) / (4 * p.Δ)).toNat) (hg : 0 ≤ t - 6 * p.Δ)
    (ht : t = SA.gateTime p.toParams s)
    (hnew : GridCO.savedGenuine st.base s = none) :
    clock p st t = normalizeS { st with
      base := { SA.clock p.toParams (actView st) t with blocks := st.base.blocks },
      fastWrite := st.fastWrite ++ [(s, fastSet p (actView (clockPre p st t)) s)] }
```

  The time `t` is fixed by the gate, so the freeze and release branches do not run at the same tick; the early branch does (`d_s = e_{s+1}`), and it commutes. `hnew` on `st` is enough: `clockPre` does not write `genuine` (`clockPre_genuine`). If the exact equality needs more premises, state them and report each one. Do not add a fault, synchrony or FG-safety premise to this algebraic bridge (audit N3).
- [x] **Step 5: Prove them.** Field lemmas: `unfold` and `split` on the `if` and `match` branches (as `GridCO.gate_blocks`). `actView_onView`: the Opus 3-line proof (`show`, then rewrite the filtered list with `hf`). The antitone, stability and item-4/6 lemmas: `eraseFG_preceq`, `block_incompatible_of_preceq`, `block_compatible_of_preceq_compatible`, `block_preceq_total_of_common` (Task 2). Items 1–2: `baseTree`, `KitFG.StoreInv.{gen, Fmem, closed}`, `eraseFG_preceq`. `gateStep_fresh`: `recordGenuine` under `slowLeasePolicy` appends `(s, result)` once (`GridCO/Model/Protocol.lean:441–446`); prove the needed `savedGenuine` of an appended list locally if GridCO has no lemma. The bridges: unfold `clock`, `clockPre`, `SA.clock` (`GridCO.clock` with `slowLeasePolicy`), `onView`; use `actView_onView` at each step and the fact that `expire` and the early step do not read or write `blocks`.
- [x] **Step 6: Review gate G7 and CHECKPOINT.** Commit `FGSA store: write sets, active view, tick SA bridge`.
  Execution notes (2026-09-29): the checkpoint is the commit that adds this note; G7 passed (dispositions below). `Statements/Invariants.lean` is the code of Step 1 verbatim. Every statement of the Step 2–4 code blocks is in `Proofs/Fields.lean` or `Proofs/ActView.lean` with the same text (two statement lines are wrapped for the 100-column linter). Forms chosen where the plan names a lemma without a statement: `admitBlock_refused` takes `parentFG st b = none ∨ ∃ P, parentFG st b = some P ∧ blockAccepted p st s b P rows = false`; `normalizeS_fields` is the exact equation `normalizeS st = { st with base := { st.base with stableRecord := if F ⪯ S then S else F } }`; the `clockPre` lemmas come from one conjunction `clockPre_fields` (fg, blocks, proposals, rowPool, genuine, fastWrite). Extra lemmas: `admitHead_obligations`, `gateStep_proposals`, `gateStep_rowPool`; the helpers `savedGenuine_append` and `saGate_genuine` (for `gateStep_fresh`), `block_compatible_of_preceq`, `block_compatible_of_below` and `eraseFG_ancestor_mem` (for items 1–6), and `onView_onView` and `clockPre_eq` (the pre-gate tick is ONE `onView` step; for the bridges). The two bridges need no premise beyond the plan's (`hs`, `hg`, `ht`, `hnew` for the gate). Item 6 for a genesis or view result needs no separate lemma: `actView_noVeto` covers every active block. The genesis result of `confirmation_mem` is active only by `actView_genesis_F` (under `CStoreInv`), or it is compatible with every block by `block_genesis_preceq`; Task 11 uses one of the two before `actView_noVeto` (G7 m4). GridCO lemmas used: `admitVote_blocks`, `admitVote_stable`, `admitVote_obligations`, `gate_blocks`, all with `@… GridCO.slowLeasePolicy` (each has a `[LeasePolicy]` argument, N3); the others of the Interfaces list are for Tasks 8–10. Proof notes: `actView_admitHead` needs `split_ifs` with two conditions that are equal by definition but not by syntax (closed by `absurd`); `clockPre_eq` is an 8-way case split on the freeze, early and release tests, each closed by `rfl`; the bridges rewrite `SA.clock` with `show SA.clock … = _ from if_neg hc` (or `if_pos hc`). Validation: `lake build --wfail AvailableChainFGSA` and `bash scripts/check-fgsa.sh` pass (537 constants, 217 theorems; standard axioms only). The duty-slot condition `s = st.slot p` (G6 O-m3) is an input of composition task T7 (Task 13, Step 5), not of this task: no Task 7 statement reads a duty.

**G7 dispositions** (review of `2e684fa`: PASS; 0 blocking, 0 major, 4 minor; report `docs/audit/fgsa-task7-opus-review.md`). All four are applied in the minors fold commit. m1: new rfl equation `actView_eq` (the SA view is the base with the filtered block list), and the `actView_fields` docstring lists the fields that it names. m2: `fastSet_prefix` has the new conjunct `B ≠ .genesis` (a stronger statement; the two Task 11 call sites are updated). m3: new wrapper `clock_eq_saClock_gate'` with only `ht` and `hnew` (`hs` and `hg` follow from `Δ > 0`). m4: the clause on the genesis result of item 6 is added to the execution note above. The two notes for later gates: `base_admitProposal_accepts` needs only `Inv0` and holds over the over-approximate `Reachable` (G10); `J ∈ TF` is `J_mem` in `Proofs/StoreInv.lean` (Task 11; G11 checks it). G7 is closed.

---

### Task 8: Output nesting, store form (K2; composition T6)

**Files:**
- Create: `AvailableChainFGSA/Statements/Store.lean`, `AvailableChainFGSA/Proofs/Nesting.lean`
- Modify: `AvailableChainFGSA.lean`

**Interfaces:**
- Consumes: Task 7.
- Produces: `OutputNestingStored` (Statement); `outputNesting_v1`, `normalizeS_nest`, `reconcile_nest`, `gateStep_nest`, `process_nest`, `clock_nest`, `outputNesting_stored`.

**Blueprint:** `comp.outputNesting.v1` and `comp.outputNesting.v2` (bp00 §3.1; bp01 §7; DQ7). The proof needs NO other invariant: the gate and every F advance end with `normalizeS`, and every other completed step writes neither F nor S (inside `admitBlock`, the state before `reconcile` can have a moved F and the old S; G8 m3). The run lift is T7.

- [x] **Step 1: Write the statement** in `Statements/Store.lean` (imports `AvailableChainFGSA.Statements.Invariants`):

```lean
/-- [bp comp.outputNesting.v2; K2] At every reachable state, `F ⪯ S`, and both
available accessors return S; for every `a`, without synchrony, including
empty and vetoed gates (spec 563–568). -/
def OutputNestingStored (p : Params) : Prop :=
  ∀ st, Reachable p st → NestOK st ∧ confirmed st = st.base.stableRecord ∧ stable st = confirmed st
```

- [x] **Step 2: Write the lemma statements** in `Proofs/Nesting.lean`:

```lean
/-- [bp comp.outputNesting.v1] The accessor form: `F ⪯ (if F ⪯ S then S else F)`. -/
theorem outputNesting_v1 (F S : Block) : Block.Preceq F (if Block.preceq F S then S else F)
theorem normalizeS_nest {n : Nat} (st : State n) : NestOK (normalizeS st)
theorem reconcile_nest {n : Nat} (st : State n) : NestOK (reconcile st)
theorem gateStep_nest (p : Params) (st : State p.n) (s : Slot) : NestOK (gateStep p st s)
theorem process_nest (p : Params) (st : State p.n) (o : Wire p.n) (h : NestOK st) :
    NestOK (process p st o)
theorem clock_nest (p : Params) (st : State p.n) (t : Time) (h : NestOK st) :
    NestOK (clock p st t)
/-- [bp comp.outputNesting.v2; K2] -/
theorem outputNesting_stored (p : Params) : OutputNestingStored p
```

- [x] **Step 3: Prove them.** `process_nest`: a head vote or a row changes neither `fg` nor `stableRecord` (Task 7); a refused block changes nothing; an accepted block: `admitProposal` keeps `stableRecord` (`GridCO.process_stable`-style lemma, with `@… GridCO.slowLeasePolicy` if it is lease-dependent), then either F is unchanged (keep `h`) or `reconcile_nest`; the row fold keeps both. `clock_nest`: expiry, freeze, early and release keep `stableRecord` and `fg`; the gate ends with `normalizeS`. `outputNesting_stored`: induction on `Reachable`; `initial` has `F = S = genesis`.
- [x] **Step 4: Review gate G8 and CHECKPOINT.** Commit `FGSA store: output nesting (K2)`.
  Execution notes (2026-09-29): the checkpoint is the commit that adds this note; G8 passed (dispositions below). `Statements/Store.lean` and the seven statements in `Proofs/Nesting.lean` are the code above verbatim. `OutputNestingStored` holds with NO other invariant, as planned. Extra helpers: `admitRow_nest` and `foldl_admitRow_nest` (the row fold), `admitProposal_stable` (the SA block admission and its carried votes keep S; the GridCO proof of `process_stable` uses the private `fold_stable`, so this file proves the fold locally; `admitVote_stable` is applied with `@… GridCO.slowLeasePolicy`, N3), and `clockPre_stable` (the pre-gate tick keeps S). Validation: `lake build --wfail AvailableChainFGSA` and `bash scripts/check-fgsa.sh` pass (557 constants, 234 theorems; standard axioms only).

**G8 dispositions** (review of `10834ba`: PASS; 0 blocking, 0 major, 3 optional minor; report `docs/audit/fgsa-task8-opus-review.md`). All three are applied in the minors fold commit. m1: the `OutputNestingStored` docstring says that conjuncts 2 and 3 are definitional (`rfl`, DQ7). m2: new corollary `finalized_preceq_stable` (`Block.Preceq (eraseFG (finalized st)) (stable st)` on reachable states) in `Proofs/Nesting.lean`. m3: "completed" is added to the module docstring, to the `process_nest` docstring and to the Blueprint line above. G8 is closed.

---

### Task 9: Reconcile facts (K3; K1 helper and origin form)

**Files:**
- Create: `AvailableChainFGSA/Proofs/Reconcile.lean`
- Modify: `AvailableChainFGSA.lean`

**Interfaces:**
- Consumes: Tasks 2, 7.
- Produces: `reconcile_obligations`, `reconcile_genuine`, `reconcile_savedGenuine`, `reconcile_fastWrite`, `reconcile_stable`, `reconcile_frame` (K3), `storeControls_reconcile` (K3), `reconcile_idem`, `reconcile_saCompat`, `reconcile_harmless` (helper), `reconcile_fastOrigin` (K1 historical case), `reconcile_harmless_origin` (K1, blueprint form).

**Blueprint:** `bp.reconcile.v1` (bp00 §3.1; bp01 §6.2–6.3). Write `Fb st := eraseFG st.fg.F`. Correction of revision 1 (Opus M3): the fastWrite premise of K1 does NOT need write origins over a run. It is the local invariant `FastOrigin` (Task 7), which this task preserves over reconcile and Task 11 preserves over every step.

- [x] **Step 1: Write the statements.**

```lean
/-- [bp bp.reconcile.v1] (§6.2, exact effects) -/
theorem reconcile_obligations (st : State n) :
    (reconcile st).base.obligations = st.base.obligations.filter (fun row => activeCompatible st row.1)
/-- [bp bp.reconcile.v1] (§6.2, exact effects) -/
theorem reconcile_genuine (st : State n) :
    (reconcile st).base.genuine = st.base.genuine.map (fun row => (row.1, row.2.filter (activeCompatible st)))
/-- [bp bp.reconcile.v1] (§6.2, exact effects) A label stays evaluated; a result
is kept or emptied, never replaced. -/
theorem reconcile_savedGenuine (st : State n) (r : Slot) :
    GridCO.savedGenuine (reconcile st).base r =
      (GridCO.savedGenuine st.base r).map (fun c => c.filter (activeCompatible st))
/-- [bp bp.reconcile.v1] (§6.2, exact effects) -/
theorem reconcile_fastWrite (st : State n) :
    (reconcile st).fastWrite = st.fastWrite.map (fun row => (row.1, row.2.filter (activeCompatible st)))
/-- [bp bp.reconcile.v1] (§6.2, exact effects) -/
theorem reconcile_stable (st : State n) :
    (reconcile st).base.stableRecord =
      if Block.preceq (eraseFG st.fg.F) st.base.stableRecord then st.base.stableRecord
      else eraseFG st.fg.F
/-- [bp bp.reconcile.v1, bp.frame.v1; K3] Reconcile writes no frame input and no
other field: Σ.T, the FG caches, the stamps, both pools, the proposals, the
time, the frozen and early caches, the release snapshots and G. -/
theorem reconcile_frame (st : State n) :
    (reconcile st).fg = st.fg ∧ (reconcile st).proposals = st.proposals ∧
    (reconcile st).rowPool = st.rowPool ∧
    (reconcile st).base.blocks = st.base.blocks ∧
    (reconcile st).base.blockStamp = st.base.blockStamp ∧
    (reconcile st).base.votes = st.base.votes ∧
    (reconcile st).base.voteStamp = st.base.voteStamp ∧
    (reconcile st).base.proposals = st.base.proposals ∧
    (reconcile st).base.now = st.base.now ∧
    (reconcile st).base.frozen = st.base.frozen ∧
    (reconcile st).base.early = st.base.early ∧
    (reconcile st).base.releaseSnapshots = st.base.releaseSnapshots ∧
    (reconcile st).base.goldfishRecord = st.base.goldfishRecord
/-- [bp bp.frame.v1, bp.reconcile.v1; K3] Reconcile keeps the FG frame. -/
theorem storeControls_reconcile (p : Params) (st : State p.n) :
    storeControls p.E p.cfg (reconcile st).fg = storeControls p.E p.cfg st.fg
/-- [bp bp.reconcile.v1] (idempotence for fixed F) -/
theorem reconcile_idem (st : State n) : reconcile (reconcile st) = reconcile st
/-- [bp bp.reconcile.v1] After reconcile every SA target is compatible with F. -/
theorem reconcile_saCompat (st : State n) : SACompat (reconcile st)
/-- [helper; bp bp.reconcile.v1] Harmless reconcile, filter form: if F is
compatible with every live lease, saved nonempty result, fastWrite member and S,
then reconcile deletes nothing and only moves S forward. The fastWrite premise
is discharged by `reconcile_harmless_origin`; do not cite this lemma as K1. -/
theorem reconcile_harmless (st : State n) (hC : SACompat st)
    (hS : Block.Compatible st.base.stableRecord (eraseFG st.fg.F)) :
    reconcile st = { st with base := { st.base with
        stableRecord := if Block.preceq (eraseFG st.fg.F) st.base.stableRecord
          then st.base.stableRecord else eraseFG st.fg.F } } ∧
    Block.Preceq st.base.stableRecord (reconcile st).base.stableRecord
/-- [bp bp.reconcile.v1 §6.3; K1 historical case] If the origin invariant holds
for the old F₀ and F₀ ⪯ F, it holds for F after reconcile. An emptied body C
keeps only members B with B ⪯ F (C # F, B ⪯ C, B ∥ F force B ⪯ F). -/
theorem reconcile_fastOrigin (st : State n) (F₀ : Block) (hO : FastOrigin F₀ st)
    (hF : Block.Preceq F₀ (eraseFG st.fg.F)) :
    FastOrigin (eraseFG st.fg.F) (reconcile st)
/-- [bp bp.reconcile.v1; K1] Harmless reconcile, blueprint form. The state holds
the new F; `F₀` is the F before the move, with its origin invariant. If the new
F is compatible with every live lease, every saved nonempty result and S, then
reconcile deletes no target, no body and no fastWrite member, and only extends
S. There is NO fastWrite premise. -/
theorem reconcile_harmless_origin (st : State n) (F₀ : Block) (hO : FastOrigin F₀ st)
    (hF : Block.Preceq F₀ (eraseFG st.fg.F))
    (hL : ∀ row ∈ st.base.obligations, Block.Compatible row.1 (eraseFG st.fg.F))
    (hG : ∀ r C, (r, some C) ∈ st.base.genuine → Block.Compatible C (eraseFG st.fg.F))
    (hS : Block.Compatible st.base.stableRecord (eraseFG st.fg.F)) :
    reconcile st = { st with base := { st.base with
        stableRecord := if Block.preceq (eraseFG st.fg.F) st.base.stableRecord
          then st.base.stableRecord else eraseFG st.fg.F } } ∧
    Block.Preceq st.base.stableRecord (reconcile st).base.stableRecord
```

- [x] **Step 2: Prove them.** Exact effects: unfold `reconcile`, `normalizeS`; `split`. `reconcile_idem`: the filters are idempotent (`List.filter_filter`, `Option.filter` twice), and `normalizeS` of a nested state is the identity. `reconcile_harmless`: `List.filter_eq_self`, `List.map` with `Option.filter_eq_self`; for S, if `F ⋠ S` then compatibility gives `S ⪯ F`. `reconcile_fastOrigin`: `reconcile_fastWrite`, `reconcile_savedGenuine`; case "B ⪯ C, C kept": unchanged; case "B ⪯ C, C emptied": `block_preceq_total_of_common` is not needed: `F ⪯ B` would give `F ⪯ C`, a contradiction, so the kept `B ∥ F` gives `B ⪯ F`; case "B ⪯ F₀": `block_preceq_trans` with `hF`. `reconcile_harmless_origin`: build `SACompat st` from `hL`, `hG` and `hO` (a member below a body `C` with `C ∥ F` is compatible with F by `block_compatible_of_preceq_compatible`; a member below `F₀ ⪯ F` is below F), then apply `reconcile_harmless`. `savedGenuine … = some (some C)` gives `(r, some C) ∈ genuine` (`List.find?` membership).
- [x] **Step 3: Review gate G9 and CHECKPOINT.** Commit `FGSA store: reconcile facts (K3, K1)`.
  Execution notes (2026-09-29): the checkpoint is the commit that adds this note; G9 passed (dispositions below). `Proofs/Reconcile.lean` has the twelve statements above with the same text (five statement lines are wrapped for the 100-column linter). No statement needs a new premise. `reconcile_harmless_origin` has NO fastWrite premise, as planned: it builds the fastWrite part of `SACompat` from `hO`, `hG` and `hF`. Extra helpers: `reconcile_eq` (the exact effect as one record update; every exact-effect lemma and `reconcile_idem` rewrite with it), `preceq_normal` (`F ⪯ (if F ⪯ S then S else F)` in `Bool` form), `stable_preceq_normal` (S precedes the new S when S and F are compatible), and `mem_genuine_of_saved` (a saved nonempty result is a row of `genuine`). Validation: `lake build --wfail AvailableChainFGSA` and `bash scripts/check-fgsa.sh` pass (577 constants, 252 theorems; standard axioms only).

**G9 dispositions** (review of `a339fd8`: PASS WITH FIXES; 0 blocking, 0 major, 3 minor; report `docs/audit/fgsa-task9-opus-review.md`). m1: the tags `[bp bp.reconcile.v1] (§6.2, exact effects)` on `reconcile_genuine`, `reconcile_savedGenuine`, `reconcile_fastWrite`, `reconcile_stable`, and `[bp bp.frame.v1, bp.reconcile.v1; K3]` on `storeControls_reconcile`, in the code and in the block above (minors fold commit; no statement changes). m2: the K1 `hL` reading is a Task 13 Step 5 report line. m3: the `reconcile_harmless` check is a G13 item (Task 13 Step 6). G9 is closed.

---

### Task 10: Admission agreement, block-step SA bridge (J3), acceptance sufficiency (K8)

**Files:**
- Create: `AvailableChainFGSA/Proofs/Admission.lean`
- Modify: `AvailableChainFGSA/Statements/Invariants.lean` (add `Inv0`), `AvailableChainFGSA.lean`

**Interfaces:**
- Consumes: Tasks 2, 7, 9; `KitFG.{pickPair_eq_of_unique, on_block_of_accepted, update_finality_TF}`.
- Produces: `pickPair_some_spec`, `parentFG_spec`, `eraseFG_fgBlock`, `fgBlock_parent`, `fgBlock_slot`, `fgBlock_root`, `fgBlock_rows`, `fgBlock_notMem`, `toRow_forall₂`, `blockAccepted_of_wellFormed`, `rootTest_iff_blockTest`, `fg_on_block_accepts`, `base_admitProposal_accepts`, `admitBlock_accepted_eq`, `admitBlock_sufficient`, `actView_admitBlock_sameF`, `actView_admitBlock_movedF`.

The composite test decides; the FG and GridCO tests must then take their accepting branch. Otherwise the base list and Σ.T would drift apart (comp §4.3, "small lemma").

- [x] **Step 1: Write the statements.** Add to `Statements/Invariants.lean` the definition `Inv0 p st`, the conjunction `KitFG.StoreInv p.E p.cfg st.fg ∧ (∀ X ∈ TF, ∀ Y ∈ TF, X.root = Y.root → X = Y) ∧ (∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ TF, eraseFG B = b)` (the first three fields of `CStoreInv`).

```lean
/-- [helper] Selector soundness (audit: `pickPair_eq_of_unique` is only the
sufficient direction). -/
theorem pickPair_some_spec {α : Type} [DecidableEq α] (T : Finset α) (q : α → Bool) {a : α}
    (h : pickPair T q = some a) : a ∈ T ∧ q a = true
/-- [M3] Under root injectivity the parent lookup is exact. -/
theorem parentFG_spec {n : Nat} (st : State n)
    (hinj : ∀ X ∈ st.fg.TF, ∀ Y ∈ st.fg.TF, X.root = Y.root → X = Y)
    (b : Block) (P : FGBlock (Fin n)) :
    parentFG st b = some P ↔ P ∈ st.fg.TF ∧ eraseFG P = b.parent
/-- [bp bp.carrier.v1] (the flat form of `eraseFG (fg B) = erase B`, DQ1) -/
theorem eraseFG_fgBlock {n : Nat} {P : FGBlock (Fin n)} {b : Block} (hb : b ≠ .genesis)
    (hP : eraseFG P = b.parent) (rows : List (RowWire n)) : eraseFG (fgBlock P b rows) = b
theorem fgBlock_parent {n : Nat} (P : FGBlock (Fin n)) (b : Block) (rows : List (RowWire n)) :
    (fgBlock P b rows).parent = P
theorem fgBlock_slot {n : Nat} (P : FGBlock (Fin n)) (b : Block) (rows : List (RowWire n)) :
    (fgBlock P b rows).slot = b.slot
theorem fgBlock_root {n : Nat} (P : FGBlock (Fin n)) (b : Block) (rows : List (RowWire n)) :
    (fgBlock P b rows).root = b.root
theorem fgBlock_rows {n : Nat} (P : FGBlock (Fin n)) (b : Block) (rows : List (RowWire n)) :
    (fgBlock P b rows).rows = rows.filterMap RowWire.toRow?
/-- A block with a fresh root is not in Σ.T. -/
theorem fgBlock_notMem {n : Nat} (st : State n) (P : FGBlock (Fin n)) (b : Block)
    (rows : List (RowWire n)) (hfresh : ¬ ∃ Y ∈ st.fg.TF, Y.root = b.root) :
    fgBlock P b rows ∉ st.fg.TF
/-- [audit M2; DQ12] A row list whose rows all decode loses no occurrence: the
FG rows are the decoded rows, position by position. -/
theorem toRow_forall₂ {n : Nat} (rows : List (RowWire n))
    (h : ∀ a ∈ rows, (RowWire.decode? a).isSome) :
    List.Forall₂ (fun a x => a.toRow? = some x) rows (rows.filterMap RowWire.toRow?)
/-- [DQ9, DQ14; Opus m3] On a checked block wire, the acceptance test reduces to
the state tests: slot not in the future, fresh root, `F ⪯ B`. -/
theorem blockAccepted_of_wellFormed (p : Params) (st : State p.n) (s : Slot) (b : Block)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) (P : FGBlock (Fin p.n))
    (hwf : wellFormed p ⟨.proposer s, .proposal b raw support rows⟩ = true) :
    blockAccepted p st s b P rows =
      (decide (b.slot ≤ st.slot p) && !decide (∃ Y ∈ st.fg.TF, Y.root = b.root) &&
        FGBlock.preceq st.fg.F (fgBlock P b rows))
/-- [DQ2; Opus m4] Under a root premise on the base list and `b`, the root test
and the block test agree (the T7 form uses `RootInjective`). -/
theorem rootTest_iff_blockTest (p : Params) (st : State p.n) (h : Inv0 p st) (b : Block)
    (hinj : ∀ c ∈ st.base.blocks, c.root = b.root → c = b) :
    (∃ Y ∈ st.fg.TF, Y.root = b.root) ↔ b ∈ st.base.blocks
/-- [bp bp.frame.v1] The FG module accepts every block that the composite accepts. -/
theorem fg_on_block_accepts (p : Params) (st : State p.n) (s : Slot)
    (b : Block) (P : FGBlock (Fin p.n)) (rows : List (RowWire p.n))
    (hP : parentFG st b = some P) (hacc : blockAccepted p st s b P rows = true) :
    on_block p.E p.cfg st.fg (fgBlock P b rows) =
      update_finality p.E p.cfg { st.fg with TF := insert (fgBlock P b rows) st.fg.TF } (fgBlock P b rows)
/-- [comp §4.3] The SA block admission accepts every block that the composite
accepts: the block and its stamp are appended, the base wire is stored; `now`,
leases, saved results and S do not change. -/
theorem base_admitProposal_accepts (p : Params) (st : State p.n) (h : Inv0 p st) (s : Slot)
    (b : Block) (raw support : List (HeadWire p.n)) (P : FGBlock (Fin p.n)) (rows : List (RowWire p.n))
    (hP : parentFG st b = some P) (hacc : blockAccepted p st s b P rows = true) :
    let base' := GridCO.admitProposal p.toParams.engine st.base (baseProposal s b raw support) b (raw.map baseHead)
    base'.blocks = st.base.blocks ++ [b] ∧
      base'.blockStamp = st.base.blockStamp ++ [(b, st.base.now)] ∧
      base'.proposals = st.base.proposals ++ [baseProposal s b raw support] ∧
      base'.obligations = st.base.obligations ∧ base'.genuine = st.base.genuine ∧
      base'.stableRecord = st.base.stableRecord ∧ base'.now = st.base.now
/-- [audit M4; Opus m2] The exact accepted step: the FG step, the stored wire,
reconcile when F moves, and the row fold that changes only the row pool. -/
theorem admitBlock_accepted_eq (p : Params) (st : State p.n) (s : Slot)
    (b : Block) (raw support : List (HeadWire p.n)) (P : FGBlock (Fin p.n)) (rows : List (RowWire p.n))
    (hP : parentFG st b = some P) (hacc : blockAccepted p st s b P rows = true) :
    let st1 : State p.n := { st with
      base := GridCO.admitProposal p.toParams.engine st.base (baseProposal s b raw support) b (raw.map baseHead)
      fg := on_block p.E p.cfg st.fg (fgBlock P b rows)
      proposals := st.proposals ++ [⟨.proposer s, .proposal b raw support rows⟩] }
    let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
    ∃ pool, admitBlock p st s b raw support rows = { st2 with rowPool := pool } ∧
      st2.rowPool <+: pool
/-- [bp bp.receiptCoverage.v1 §10.1; K8; Opus m2] Acceptance sufficiency: a
checked, absent block with a stored parent, a slot that is not in the future, a
fresh root and `F ⪯ b` is admitted. -/
theorem admitBlock_sufficient (p : Params) (st : State p.n) (h : CStoreInv p st) (s : Slot)
    (b : Block) (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hwf : wellFormed p ⟨.proposer s, .proposal b raw support rows⟩ = true)
    (hpar : b.parent ∈ st.base.blocks) (hslot : b.slot ≤ st.slot p)
    (hfresh : ∀ c ∈ st.base.blocks, c.root ≠ b.root)
    (hF : Block.Preceq (eraseFG st.fg.F) b) :
    b ∈ (process p st ⟨.proposer s, .proposal b raw support rows⟩).base.blocks ∧
      ∃ P, parentFG st b = some P ∧
        fgBlock P b rows ∈ (process p st ⟨.proposer s, .proposal b raw support rows⟩).fg.TF
/-- [comp D3; Opus J3] A block delivery that does not move F is the SA block
admission on the active view (the carried rows change only the row pool). -/
theorem actView_admitBlock_sameF (p : Params) (st : State p.n) (h : CStoreInv p st) (s : Slot)
    (b : Block) (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) (P : FGBlock (Fin p.n))
    (hP : parentFG st b = some P) (hacc : blockAccepted p st s b P rows = true)
    (hF : (admitBlock p st s b raw support rows).fg.F = st.fg.F) :
    actView (admitBlock p st s b raw support rows) =
      GridCO.admitProposal p.toParams.engine (actView st) (baseProposal s b raw support) b
        (raw.map baseHead)
/-- [comp D3; Opus J3] When F moves to `F'`, the view is the SA admission on the
old view, with its blocks filtered by `F'` and reconcile's three writes
(`reconcile_obligations`, `reconcile_genuine`, `reconcile_stable`). -/
theorem actView_admitBlock_movedF (p : Params) (st : State p.n) (h : CStoreInv p st) (s : Slot)
    (b : Block) (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) (P : FGBlock (Fin p.n))
    (hP : parentFG st b = some P) (hacc : blockAccepted p st s b P rows = true)
    (hF : (admitBlock p st s b raw support rows).fg.F ≠ st.fg.F) :
    let A := GridCO.admitProposal p.toParams.engine (actView st) (baseProposal s b raw support) b
      (raw.map baseHead)
    let st' := admitBlock p st s b raw support rows
    let ok := fun c => Block.compatible c (eraseFG st'.fg.F)
    actView st' = { A with
      blocks := A.blocks.filter ok
      obligations := A.obligations.filter (fun row => ok row.1)
      genuine := A.genuine.map (fun row => (row.1, row.2.filter ok))
      stableRecord := if Block.preceq (eraseFG st'.fg.F) A.stableRecord then A.stableRecord
        else eraseFG st'.fg.F }
```

  The carried votes add vote stamps, not block stamps, so the `blockStamp` equation is exact.
- [x] **Step 2: Prove them.** `pickPair_some_spec`: unfold `pickPair`; `split`; `Finset.choose_spec`. `parentFG_spec`: forward by `pickPair_some_spec`; backward by `KitFG.pickPair_eq_of_unique`: two candidates `P, P'` have `eraseFG P = eraseFG P'`, so equal roots (`eraseFG_root`), so `P = P'`. `toRow_forall₂`: induction on `rows`. `blockAccepted_of_wellFormed`: unfold both; the syntactic conjuncts are equal. `fg_on_block_accepts`: `KitFG.on_block_of_accepted`; the four FG refusals fail: `fgBlock_notMem`; `P ∈ TF`; `F ⪯ B` is in `blockAccepted`; `fgBlock_slot`, `fgBlock_parent` and `eraseFG_slot` give the slot test. `base_admitProposal_accepts`: unfold `GridCO.admitProposal` and show that the refusal is false: the slot formula is the same (`p.toParams.engine.Δ = p.Δ` by `rfl`); `blockKnown st.base b.parent` from `baseTree` and `hP`; `b ∉ st.base.blocks` because a stored `c = b` has a stored FG block with the root of `b`; the proposer test from `s == b.slot`. Then `admitVote_blocks`, `admitVote_obligations`, `admitVote_stable` over the fold (GridCO `Map.lean`, `History.lean`; with the explicit lease instance where needed; if a needed fold lemma is `private`, prove the fold form locally). `admitBlock_sufficient`: `hpar` and `baseTree` give `P ∈ TF` with `eraseFG P = b.parent`, and `parentFG_spec` gives `parentFG st b = some P`; `hfresh` and `baseTree` give the fresh root; `hF`, `eraseFG F ≠ b` (F is stored, `b` is absent because its root is fresh), so `eraseFG F ⪯ b.parent = eraseFG P`, and `preceq_of_eraseFG_preceq` with `viewRootInj_of_rootInj` gives `F ⪯ P ⪯ fgBlock P b rows`; `blockAccepted_of_wellFormed` does the rest. `actView_admitBlock_sameF`: `F ⪯ fgBlock P b rows` and `fgBlock P b rows ≠ F` (fresh root) give `F ⪯ P`, so the parent is active; `b` is active; `b` is not in the view list; so `GridCO.admitProposal` accepts on the view too, and filter commutes with `++ [b]`; the vote fold reads no block (`actView_fields`); the row fold changes only `rowPool`. `actView_admitBlock_movedF`: the same, then `reconcile`'s exact effects (Task 9) and `actView_fields`.
- [x] **Step 3: Review gate G10 and CHECKPOINT.** Commit `FGSA store: admission agreement, block-step bridge, sufficiency`.
  Execution notes (2026-09-29): the checkpoint is the commit that adds this note; G10 passed (dispositions below). `Inv0` is in `Statements/Invariants.lean` as planned. `Proofs/Admission.lean` has the 17 statements above with the same text (some lines are wrapped for the 100-column linter), with ONE change: `admitBlock_accepted_eq` has no `Inv0` premise (the proof uses only `hP` and `hacc`; an unused premise fails the linter). The bridges `actView_admitBlock_sameF` and `actView_admitBlock_movedF` need no premise beyond the plan's. `actView_admitBlock_movedF` also uses `KitFG.on_block_F_mono` (F moves only forward, so the new filter is inside the old one); the plan's proof note did not name it. Extra helpers: `blockAccepted_facts`, `accepted_base_facts`, `accepted_F_facts` (an accepted block has `F ⪯ P`, so its parent and itself are active), `admitVote_withBlocks` and `foldVotes_withBlocks` (the carried-vote fold reads no block), `foldVotes_fields`, `admitProposal_of_accept` (the accepting branch of `GridCO.admitProposal`), `admitProposal_base_view` (the base and the view admissions are the same fold with two block lists), `activeCompatible_eq`, `foldl_admitRow_eq` and `foldl_admitRow_view` (the row fold appends to the pool only). Other KitFG lemmas used: `preceq_parent_of_preceq_node`, `preceq_node_of_preceq`, `preceq_refl`. Validation: `lake build --wfail AvailableChainFGSA` and `bash scripts/check-fgsa.sh` pass (640 constants, 307 theorems; standard axioms only).

**G10 dispositions** (review of `3840172`: PASS; 0 blocking, 0 major, 4 minor; report `docs/audit/fgsa-task10-opus-review.md`). The only change to `Statements/Invariants.lean` in Task 10 is the new `Inv0`. m1: the `admitBlock_accepted_eq` block above has no `Inv0` premise, as the code; the Task 11 call note says so. m2: the `admitBlock_sufficient` docstring cites DQ2, and the new corollary `admitBlock_sufficient_absent` takes `b ∉ st.base.blocks` and the root premise of `rootTest_iff_blockTest` in place of `hfresh`. m3: new projection `CStoreInv.toInv0` (`Proofs/Admission.lean`), used at the six earlier sites in Tasks 10–12. m4: `[helper]` docstrings on `fgBlock_parent`, `fgBlock_slot`, `fgBlock_root`, `fgBlock_rows`, and `[helper; DQ2]` on `fgBlock_notMem`. G10 is closed.

---

### Task 11: The composite store invariant (K4 core), F monotone, K1 at a step, selector facts

**Files:**
- Create: `AvailableChainFGSA/Proofs/StoreInv.lean`
- Modify: `AvailableChainFGSA/Statements/Store.lean` (add two statements), `AvailableChainFGSA.lean`

**Interfaces:**
- Consumes: Tasks 8–10; `KitFG.{storeInv_init, storeInv_on_block, on_block_F_mono, update_finality_h_max, update_finality_pair, storeControls_eq_fjControls}`; `GridCO.confirmation_mem`, `GridCO.gate_target_origin` (`GenuineHistory.lean:32`), `GridCO.ghostWalk_mem` (`RecordSlots.lean:131`), `GridCO.RootInjectiveBelow` (`Roots.lean:17`), all with `@… GridCO.slowLeasePolicy` where they are lease-dependent.
- Produces: `StoreInvariant`, `FMonotone` (Statements); `cstoreInv_init`, `cstoreInv_process`, `cstoreInv_clock`, `storeInvariant`, `viewRootInj_TF`, `storeControls_eq`, `fg_step_cases`, `process_F_mono`, `clock_F_eq`, `fMonotone`, `process_hmax_mono`, `process_pair_mono`, `saCompat_gateStep`, `fastOrigin_gateStep`, `actView_eq_image`, `admitBlock_reconcile_harmless` (K1 at a block step), `fgBlockOf_spec`, `deepest_spec`, `fgHead_stored`, `rootInjectiveBelow_base`, `leaseOf_eq_deadlineOf` (G3 minor 3).

**Blueprint:** `bp.store.v1` (K4 core) and `bp.frame.v1` (bp00 §3.1; bp01 §4); `bp.reconcile.v1` (K1). Q3 is answered: the FG part IS a `SimplexFG.Store` value, so the K4 core is "the FG part changes only by `on_block`, and `StoreInv` holds". The metadata part of K4 is Task 12.

- [x] **Step 1: Add the statements** to `Statements/Store.lean`:

```lean
/-- [bp bp.store.v1; K4 core] Every reachable state satisfies the composite invariant. -/
def StoreInvariant (p : Params) : Prop := ∀ st, Reachable p st → CStoreInv p st
/-- [bp bp.store.v1] Local F moves only to a descendant, at every step. -/
def FMonotone (p : Params) : Prop :=
  ∀ st : State p.n, (∀ o, FGBlock.Preceq st.fg.F (process p st o).fg.F) ∧
    (∀ t, (clock p st t).fg.F = st.fg.F)
```

- [x] **Step 2: Write the lemma statements** in `Proofs/StoreInv.lean`:

```lean
theorem cstoreInv_init (p : Params) : CStoreInv p (initial p.n)
theorem cstoreInv_process (p : Params) (st : State p.n) (h : CStoreInv p st) (o : Wire p.n) :
    CStoreInv p (process p st o)
theorem cstoreInv_clock (p : Params) (st : State p.n) (h : CStoreInv p st) (t : Time) :
    CStoreInv p (clock p st t)
/-- [bp bp.store.v1; K4 core] -/
theorem storeInvariant (p : Params) : StoreInvariant p
/-- [bp bp.carrier.v1; K5 local + DQ2] Σ.T satisfies `ViewRootInj` with no hypothesis. -/
theorem viewRootInj_TF (p : Params) (st : State p.n) (h : CStoreInv p st) : ViewRootInj st.fg.TF
/-- [bp bp.frame.v1; K4] The live frame is the FJ_FRAME of Σ.T. -/
theorem storeControls_eq (p : Params) (st : State p.n) (h : CStoreInv p st) :
    controls p st = fjControls p.E p.cfg st.fg.F st.fg.TF
/-- [bp bp.frame.v1] The FG projection stutters or takes one FG `on_block` step. -/
theorem fg_step_cases (p : Params) (st : State p.n) (o : Wire p.n) :
    (process p st o).fg = st.fg ∨ ∃ B, (process p st o).fg = on_block p.E p.cfg st.fg B
/-- [bp bp.store.v1; K4] -/
theorem fMonotone (p : Params) : FMonotone p
theorem process_hmax_mono (p : Params) (st : State p.n) (o : Wire p.n) :
    st.fg.h_max ≤ (process p st o).fg.h_max
theorem process_pair_mono (p : Params) (st : State p.n) (o : Wire p.n) :
    lexKey (st.fg.h_j, st.fg.J) ≤ lexKey ((process p st o).fg.h_j, (process p st o).fg.J)
/-- [bp bp.leaseOrigins.v1] A fresh gate keeps the fast-write origins. -/
theorem fastOrigin_gateStep (p : Params) (st : State p.n) (h : CStoreInv p st) (s : Slot) :
    FastOrigin (eraseFG st.fg.F) (gateStep p st s)
/-- [bp bp.activeView.v1] The erased active view is the image of the FG active view. -/
theorem actView_eq_image (p : Params) (st : State p.n) (h : CStoreInv p st) (b : Block) :
    b ∈ (actView st).blocks ↔ ∃ B ∈ activeView st.fg, eraseFG B = b
/-- [bp bp.reconcile.v1; K1] K1 at a block step, blueprint form: at an accepted
block that moves F, if the new F is compatible with every live lease (every row
of `obligations`, due leases included; G9 m2), every saved nonempty result and S
of the state before the step, then reconcile
deletes no lease, no body and no fastWrite member, and only extends S. No
fastWrite premise: `FastOrigin` comes from `CStoreInv`. -/
theorem admitBlock_reconcile_harmless (p : Params) (st : State p.n) (h : CStoreInv p st)
    (s : Slot) (b : Block) (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (P : FGBlock (Fin p.n)) (hP : parentFG st b = some P) (hacc : blockAccepted p st s b P rows = true)
    (hL : ∀ row ∈ st.base.obligations,
      Block.Compatible row.1 (eraseFG (admitBlock p st s b raw support rows).fg.F))
    (hG : ∀ r C, (r, some C) ∈ st.base.genuine →
      Block.Compatible C (eraseFG (admitBlock p st s b raw support rows).fg.F))
    (hS : Block.Compatible st.base.stableRecord (eraseFG (admitBlock p st s b raw support rows).fg.F)) :
    (admitBlock p st s b raw support rows).base.obligations = st.base.obligations ∧
    (admitBlock p st s b raw support rows).base.genuine = st.base.genuine ∧
    (admitBlock p st s b raw support rows).fastWrite = st.fastWrite ∧
    Block.Preceq st.base.stableRecord (admitBlock p st s b raw support rows).base.stableRecord
/-- [DQ13; audit N2] The stored FG block of an erased block is exact. -/
theorem fgBlockOf_spec (p : Params) (st : State p.n) (h : CStoreInv p st) (b : Block)
    (B : FGBlock (Fin p.n)) : fgBlockOf st b = some B ↔ B ∈ st.fg.TF ∧ eraseFG B = b
/-- [DQ13; audit N2] A nonempty subset of Σ.T has a deepest member (tie: the
greater root). -/
theorem deepest_spec (p : Params) (st : State p.n) (h : CStoreInv p st)
    (X : Finset (FGBlock (Fin p.n))) (hX : X ⊆ st.fg.TF) (hne : X.Nonempty) :
    ∃ B, deepest X = some B ∧ B ∈ X ∧ ∀ C ∈ X, (eraseFG C).depth < (eraseFG B).depth ∨
      ((eraseFG C).depth = (eraseFG B).depth ∧ C.root.value ≤ B.root.value)
/-- [DQ13; audit N2] The finality head is stored; so the fallback head fields
of `fgInputs` are unreachable. -/
theorem fgHead_stored (p : Params) (st : State p.n) (h : CStoreInv p st) :
    fgHead p st ∈ st.base.blocks
/-- [DQ2; Opus m4] The base list satisfies GridCO's local root premise. -/
theorem rootInjectiveBelow_base (p : Params) (st : State p.n) (h : CStoreInv p st) :
    GridCO.RootInjectiveBelow st.base.blocks
/-- [helper; G3 minor 3] The composite lease read is SA's lease read at its one
level. -/
theorem leaseOf_eq_deadlineOf (p : Params) (st : State p.n) (h : CStoreInv p st) (b : Block) :
    leaseOf st b = GridCO.deadlineOf st.base b (SA.releaseThreshold p.toParams)
```

- [x] **Step 3: Prove them.**
  - `cstoreInv_init`: `KitFG.storeInv_init`; the base list is `[genesis]`; `SACompat`, `FastOrigin`, `fastDom`, `genuineKeys` and `leaseKeys` hold on empty lists; `S = genesis`.
  - `cstoreInv_process`, head vote and row: no invariant field changes (Task 7). Refused block: the state is the same. Accepted block: `fg`: `KitFG.storeInv_on_block` with `ViewRootInj (insert B TF)` from `viewRootInj_of_rootInj` (root freshness from `blockAccepted`; parent closure from `P ∈ TF`); `rootInj`: the new root is fresh; `baseTree`: `base_admitProposal_accepts`, `update_finality_TF`, `eraseFG_fgBlock`; `SACompat`: if F is unchanged, leases, results and fastWrite are unchanged (`base_admitProposal_accepts`); if F moved, `reconcile_saCompat`; `FastOrigin`: if F is unchanged, unchanged; if F moved, `reconcile_fastOrigin` with `F₀ := eraseFG st.fg.F` and `on_block_F_mono` + `eraseFG_preceq`; `fastDom`, `genuineKeys`, `leaseKeys`: reconcile keeps the label and target lists (`reconcile_*`), and the base admission does not write them; `reconcile_frame` keeps the other fields; `Smem`: S is unchanged or `eraseFG F` with `F ∈ TF` (`StoreInv.Fmem`). The row fold keeps every field.
  - `cstoreInv_clock`: `fg` and the base list do not change. `SACompat` after the gate: a new lease target `B` satisfies `B ⪯ C` with `C = confirmation (actView st) s` (`gate_target_origin`), and `C` is genesis or active (`confirmation_mem`), so `block_compatible_of_preceq_compatible` applies; the saved result is `C`; the fastWrite set is a filter of the active list; release and expiry only delete rows (`release_subset`). `FastOrigin`: `fastOrigin_gateStep` (`gateStep_fresh` and `fastSet_prefix`: the members are prefixes of the saved `C`; the other labels keep their bodies because `fastDom` says their labels were saved before). `fastDom`: the new label is fresh (`hnew`) and is saved by the same step. `genuineKeys`: `recordGenuine` appends only an unsaved label. `leaseKeys`: `writeObligation` removes the old row of the same target and level, then appends one; under `slowLeasePolicy` the only level is `releaseThreshold` (G3 minor 3: this one constant level of `writeObligation` is the source of `leaseKeys`). `leaseOf_eq_deadlineOf`: both reads are `find?` on `obligations`; by `leaseKeys` every row has the level `releaseThreshold`, so the two predicates select the same first row. `Smem`: `advance S C` is `S` or `C`, and `C` is stored; `normalizeS` writes `eraseFG F`.
  - `fg_step_cases`, `fMonotone`: `KitFG.on_block_F_mono`, `reconcile_frame`, `clock_fg`.
  - `process_hmax_mono`, `process_pair_mono`: `update_finality_h_max`, `update_finality_pair` with `on_block_of_refused`/`on_block_of_accepted`; these give equations; use order lemmas for the monotonicity.
  - `actView_eq_image`: `baseTree` and `compatible_iff_eraseFG` with `viewRootInj_TF`.
  - `admitBlock_reconcile_harmless`: `admitBlock_accepted_eq` (no `Inv0` premise; G10 m1); `reconcile_harmless_origin` on `st1` with `F₀ := eraseFG st.fg.F`, `hO` from `h.fastOrigin` (it reads only `fastWrite` and `genuine`, which `st1` shares with `st`), and `hF` from `on_block_F_mono`.
  - `fgBlockOf_spec`: as `parentFG_spec`. `deepest_spec`: the order (depth, root value) is total on `X` and antisymmetric because `rootInj` makes roots distinct in `X`; so the maximum is unique and `KitFG.pickPair_eq_of_unique` applies. `fgHead_stored`: `GridCO.ghost` returns its anchor or a member of its tree (`ghostWalk_mem`); the tree `erasedList st (fullTree p st)` is a sublist of `base.blocks`; the anchor `liveRoot` is `eraseFG Z` (Z is F or J, both in TF: `StoreInv.Fmem`, `StoreInv.pair`) or a lease target in the tree. `rootInjectiveBelow_base`: `baseTree`, `KitFG.ancestor_closed_of_parent_closed`, `rootInj` and `preceq_of_eraseFG_preceq`.
- [x] **Step 4: Review gate G11 and CHECKPOINT.** Commit `FGSA store: composite invariant (K4 core), F monotone, K1`.
  Execution notes (2026-09-29): the checkpoint is the commit that adds this note; G11 passed with fixes (dispositions below). The two statements and the 18 lemma statements above are in `Statements/Store.lean` and `Proofs/StoreInv.lean` with the same text (some lines are wrapped for the 100-column linter). No statement needs a new premise. `saCompat_gateStep` (named in Produces, not in the code block) is `SACompat (gateStep p st s)` under `CStoreInv p st`. Proof structure: `cstoreInv_of_sublist` (the invariant reads only `fg`, the block list, the leases, the saved results, S and `fastWrite`; the leases may shrink) covers votes, rows, refused blocks and the pre-gate tick (`clockPre_obligations_sublist`); `cstoreInv_accepted_pre` gives the fields of the pre-reconcile state of an accepted block, and `cstoreInv_admitBlock` splits on a moved F (reconcile facts of Task 9); `cstoreInv_gateFresh` proves the fresh gate before `S := F`, and `cstoreInv_normalizeS` the last step. `leaseKeys` after a gate uses GridCO's `gate_eq_writeKeys` with the new helpers `writeObligation_keys`, `writeKeys_keys`, `saGateWriteKeys_level` and `saGate_cases` (`admissionLevels` under `slowLeasePolicy` gives only `releaseThreshold`). Other extra helpers: `J_mem` and `Z_mem` (the FG root is stored; from `lexMax_spec`/`lexMax_of_none` and `derive_anchors_preceq`), `savedGenuine_congr`, `fastOrigin_congr`, `ne_of_saved`, `notMem_keys_of_unsaved`, `compat_of_confirmation`, `foldl_select_mem` (for `liveRoot`), `find?_congr_mem`. GridCO lemmas used, all with `@… GridCO.slowLeasePolicy`: `gate_target_origin`, `confirmation_mem`, `gate_eq_writeKeys`; `ghostWalk_mem` (corrected by G11 M1: it HAS a lease argument, and the fix applies it as `@GridCO.ghostWalk_mem GridCO.slowLeasePolicy`); `RootInjectiveBelow` has no lease argument. Further helpers: `cstoreInv_clockPre` (the tick before the gate) and `cstoreInv_gateStep` (the gate) (G11 m4). `process_F_mono` and `clock_F_eq` are the two conjuncts of `fMonotone` as corollaries (added by G11 m1). `rootInjectiveBelow_base` needs only `baseTree`, closure (`eraseFG_ancestor_mem`) and `rootInj`, not `preceq_of_eraseFG_preceq`. Validation: `lake build --wfail AvailableChainFGSA` and `bash scripts/check-fgsa.sh` pass (708 constants, 370 theorems; standard axioms only).

**G11 dispositions** (review of `5e62302`: PASS WITH FIXES; 0 blocking, 1 major, 5 minor; report `docs/audit/fgsa-task11-opus-review.md`). M1: `fgHead_stored` applied `GridCO.ghostWalk_mem` at the default `gridLeasePolicy`; the statement does not read the instance (the reviewer checked it by `rfl`), so the result was correct, but the form is forbidden. Fix: `@GridCO.ghostWalk_mem GridCO.slowLeasePolicy`; the rule text (Global Constraints, `LeasePolicy` item) and the execution note above are corrected. Guard: `scripts/CheckFGSALease.lean` scans the types and values of every compiled FGSA constant; every argument at a `[GridCO.LeasePolicy]` position must be `GridCO.slowLeasePolicy` (a default instance, a bound variable, a partial or an unapplied use fails). `check-fgsa.sh` runs it, then compiles a scratch module with `GridCO.gate` at the default instance and requires the check to reject it (exit 1, named use). Before the M1 fix the scan reported exactly `fgHead_stored`. m1: `process_F_mono` and `clock_F_eq` are added as corollaries of `fMonotone`. m2: `J_mem` is tagged `[bp bp.store.v1; K4]`, and the Task 13 report cites it for "F, J ∈ T". m3: `fMonotone` has the docstring `[bp bp.store.v1; K4]`, also in the block above. m4: the execution note lists `cstoreInv_clockPre` and `cstoreInv_gateStep`. m5: the K1 docstring says that `hL` covers every row of `obligations`, due leases included (code and block above); the G9 m2 line is in the Task 13 Step 5 report bullets. G11 is closed.

---

### Task 12: The metadata invariant (K4 metadata) and the cross-node carrier (K5)

**Files:**
- Create: `AvailableChainFGSA/Proofs/Metadata.lean`, `AvailableChainFGSA/Proofs/CrossNode.lean`
- Modify: `AvailableChainFGSA/Statements/Invariants.lean` (add `MetaInv`, `ContentAgree`), `AvailableChainFGSA/Statements/Store.lean` (add `MetadataInvariant`), `AvailableChainFGSA.lean`

**Interfaces:**
- Consumes: Tasks 10–11.
- Produces: `MetaInv`, `ContentAgree`, `MetadataInvariant` (Statements); `process_cumulative`, `clock_cumulative`, `metaInv_init`, `metaInv_process`, `metaInv_clock`, `metadataInvariant`, `stored_wire_of_block`, `fg_eq_of_eraseFG_eq_across`, `preceq_iff_across`, `compatible_iff_across`, `rootInjectiveOn_across` (r188 N4); `contentAgree_self` (G12 m1).

**Blueprint:** `bp.store.v1` ("old states/stamps are unchanged"), `bp.frame.v1` ("the cumulative metadata reads in §2.4 remain"), `bp.carrier.v1` (premise "Base full-content root injectivity"). Audit M4 (metadata) and M2 (cross-node content). Run-level receipt times, causal signatures and emission origins stay in T7.

- [x] **Step 1: Write the statements.** In `Statements/Invariants.lean`:

```lean
/-- [bp bp.store.v1, bp.frame.v1; K4 metadata; audit M4] The local metadata
invariant. `wireTree`: every stored wire is a decoded proposal whose FG block is
in Σ.T, with the SAME ordered rows (`filterMap toRow?`), and whose rows all
decode. `treeWire`: every non-genesis block of Σ.T has exactly one stored wire.
`stampKeys`: the block stamps are keyed by the base list, once each.
`pool*`: the row pool holds decoded rows, no duplicate, at most two per
identity and round (used by `proposalRows`). `noGenesisWire`: no stored wire
carries genesis (G12 m1; with `treeWire` it gives `contentAgree_self`). The
grouping key of `proposalRows` is never `none` on any store, because its
`round?` filter (`Model/Frame.lean`, `proposalRows` and `blockWireRows`) drops
every row that does not decode (G6 item 9; G12 m2). -/
structure MetaInv (p : Params) (st : State p.n) : Prop where
  wireTree : ∀ o ∈ st.proposals, ∃ s b raw sup rows,
    o = ⟨.proposer s, .proposal b raw sup rows⟩ ∧ (∀ a ∈ rows, (RowWire.decode? a).isSome) ∧
    ∃ B ∈ st.fg.TF, eraseFG B = b ∧ B.rows = rows.filterMap RowWire.toRow?
  treeWire : ∀ B ∈ st.fg.TF, B ≠ .genesis →
    ∃! o, o ∈ st.proposals ∧ Wire.block? o = some (eraseFG B)
  proposalsNodup : st.proposals.Nodup
  stampKeys : st.base.blockStamp.map Prod.fst = st.base.blocks
  blocksNodup : st.base.blocks.Nodup
  poolDecodes : ∀ a ∈ st.rowPool, (RowWire.decode? a).isSome
  poolNodup : st.rowPool.Nodup
  poolCap : ∀ r i, (st.rowPool.filter (fun a =>
    a.decode?.map (fun x => (x.1, x.2.1)) == some (r, i))).length ≤ 2
  noGenesisWire : ∀ o ∈ st.proposals, Wire.block? o ≠ some .genesis

/-- [bp bp.carrier.v1; K5 cross-node; DQ3(b), which REVERSES comp D4; audit M2;
narrowed at G12] The content premise on two stores: stored proposal wires whose
blocks have equal roots have the same erased block (with its parent chain) and
the same ordered signed rows (with their rounds). The carried votes and the
support list are free: no cross-node proof reads them. T7 derives it for every
pair of honest stores of a run from the run premise `ContentRootInjective` and
the run fact that every stored wire is a payload that the node processed. -/
def ContentAgree {n : Nat} (st st' : State n) : Prop :=
  ∀ s b raw sup rows, (⟨.proposer s, .proposal b raw sup rows⟩ : Wire n) ∈ st.proposals →
  ∀ s' b' raw' sup' rows',
    (⟨.proposer s', .proposal b' raw' sup' rows'⟩ : Wire n) ∈ st'.proposals →
    b.root = b'.root → b = b' ∧ rows = rows'
```

  In `Statements/Store.lean`:

```lean
/-- [bp bp.store.v1; K4 metadata] -/
def MetadataInvariant (p : Params) : Prop := ∀ st, Reachable p st → MetaInv p st
```

  In `Proofs/Metadata.lean`:

```lean
/-- [bp bp.store.v1] A delivery only appends: Σ.T and the base list grow; old
block stamps, vote stamps, stored wires and pool rows stay, in order. -/
theorem process_cumulative (p : Params) (st : State p.n) (o : Wire p.n) :
    st.fg.TF ⊆ (process p st o).fg.TF ∧
    st.base.blocks <+: (process p st o).base.blocks ∧
    st.base.blockStamp <+: (process p st o).base.blockStamp ∧
    st.base.voteStamp <+: (process p st o).base.voteStamp ∧
    st.proposals <+: (process p st o).proposals ∧
    st.rowPool <+: (process p st o).rowPool
/-- [bp bp.store.v1] A tick changes no tree, stamp, wire or pool. -/
theorem clock_cumulative (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).fg.TF = st.fg.TF ∧ (clock p st t).base.blocks = st.base.blocks ∧
    (clock p st t).base.blockStamp = st.base.blockStamp ∧
    (clock p st t).base.voteStamp = st.base.voteStamp ∧
    (clock p st t).proposals = st.proposals ∧ (clock p st t).rowPool = st.rowPool
theorem metaInv_init (p : Params) : MetaInv p (initial p.n)
theorem metaInv_process (p : Params) (st : State p.n) (h : CStoreInv p st) (m : MetaInv p st)
    (o : Wire p.n) : MetaInv p (process p st o)
theorem metaInv_clock (p : Params) (st : State p.n) (m : MetaInv p st) (t : Time) :
    MetaInv p (clock p st t)
/-- [bp bp.store.v1; K4 metadata] -/
theorem metadataInvariant (p : Params) : MetadataInvariant p
/-- [helper] The one stored wire of a stored non-genesis FG block, with its rows. -/
theorem stored_wire_of_block (p : Params) (st : State p.n) (h : CStoreInv p st) (m : MetaInv p st)
    {B : FGBlock (Fin p.n)} (hB : B ∈ st.fg.TF) (hg : B ≠ .genesis) :
    ∃ s raw sup rows, ⟨.proposer s, .proposal (eraseFG B) raw sup rows⟩ ∈ st.proposals ∧
      B.rows = rows.filterMap RowWire.toRow?
```

  In `Proofs/CrossNode.lean`:

```lean
/-- [bp bp.carrier.v1; K5 cross-node, under ContentAgree] Cross-store
reconstruction: stored FG blocks at two stores with the same erasure are equal. -/
theorem fg_eq_of_eraseFG_eq_across (p : Params) (st st' : State p.n)
    (h : CStoreInv p st) (h' : CStoreInv p st') (m : MetaInv p st) (m' : MetaInv p st')
    (hc : ContentAgree st st') {X Y : FGBlock (Fin p.n)} (hX : X ∈ st.fg.TF) (hY : Y ∈ st'.fg.TF)
    (he : eraseFG X = eraseFG Y) : X = Y
/-- [bp bp.carrier.v1; K5 cross-node] Erasure preserves and reflects ancestry
across two stores. -/
theorem preceq_iff_across (p : Params) (st st' : State p.n)
    (h : CStoreInv p st) (h' : CStoreInv p st') (m : MetaInv p st) (m' : MetaInv p st')
    (hc : ContentAgree st st') {X Y : FGBlock (Fin p.n)} (hX : X ∈ st.fg.TF) (hY : Y ∈ st'.fg.TF) :
    FGBlock.Preceq X Y ↔ Block.Preceq (eraseFG X) (eraseFG Y)
theorem compatible_iff_across (p : Params) (st st' : State p.n)
    (h : CStoreInv p st) (h' : CStoreInv p st') (m : MetaInv p st) (m' : MetaInv p st')
    (hc : ContentAgree st st') {X Y : FGBlock (Fin p.n)} (hX : X ∈ st.fg.TF) (hY : Y ∈ st'.fg.TF) :
    FGBlock.compatible X Y = Block.compatible (eraseFG X) (eraseFG Y)
/-- [bp bp.carrier.v1; K5 cross-node; r188 N4] The `KitFG.accountable` premise
for two chains at two stores (bp01 §2.2 step 6). -/
theorem rootInjectiveOn_across (p : Params) (st st' : State p.n)
    (h : CStoreInv p st) (h' : CStoreInv p st') (m : MetaInv p st) (m' : MetaInv p st')
    (hc : ContentAgree st st') {B₁ B₂ : FGBlock (Fin p.n)} (h₁ : B₁ ∈ st.fg.TF)
    (h₂ : B₂ ∈ st'.fg.TF) : KitFG.RootInjectiveOn B₁ B₂
```

- [x] **Step 2: Prove them.** `process_cumulative`: the three step kinds (Task 7 field lemmas, `admitBlock_accepted_eq`, `reconcile_frame`); `insert` for Σ.T. `metaInv_process`: an accepted block adds one wire and one FG block (`admitBlock_accepted_eq`, `fg_on_block_accepts`), with rows `filterMap toRow?` (`fgBlock_rows`) that all decode (`blockAccepted`); `treeWire` uniqueness from `blocksNodup` and `rootInj` (a second wire for the same erased block would need a second acceptance, which the fresh-root test refuses); `stampKeys` from `base_admitProposal_accepts`; the pool fields from `admitRow_eq` and the `admitRow` guard. `fg_eq_of_eraseFG_eq_across`: induction on `X` (strong induction on the depth). Genesis: `eraseFG_eq_genesis`. Node: the parents have equal erasures (`eraseFG_parent`), are stored (`StoreInv.closed`), so they are equal by induction; `stored_wire_of_block` at both stores and `hc` (equal roots by `eraseFG_root`) give equal payloads, so equal row lists, so `X.rows = Y.rows`; slot and root come from the erasure. `preceq_iff_across`: forward by `eraseFG_preceq`; backward: the ancestor `Y'` of `Y` at the depth of `X` has `eraseFG Y' = eraseFG X` and is stored at `st'` (closure), so `Y' = X`. `rootInjectiveOn_across`: ancestor closure puts each compared ancestor in the store of its tip. Two ancestors in one store: local root injectivity (`viewRootInj_TF`). Ancestors in different stores: genesis by local injectivity; otherwise their stored wires (`stored_wire_of_block`) and equal roots give equal payloads (`hc`), then `fg_eq_of_eraseFG_eq_across`. No stronger content premise is needed.
- [x] **Step 3: Review gate G12 and CHECKPOINT.** Commit `FGSA store: metadata invariant and cross-node carrier`.
  Execution notes (2026-09-29): the checkpoint is the commit that adds this note; G12 passed with fixes (dispositions below). `MetaInv`, `ContentAgree` and `MetadataInvariant` are in the Statements files with the same text. The 11 produced lemmas are in `Proofs/Metadata.lean` and `Proofs/CrossNode.lean` with the same text (some lines are wrapped for the 100-column linter). No statement needs a new premise. Proof structure: `metaInv_process` splits on the step kind; a vote keeps the base list and the block stamps (`admitVote_stamps`); a row uses `metaInv_admitRow`; an accepted block uses `accepted_st2` (the facts of the pre-fold state: one new wire, `insert (fgBlock P b rows)`, one new block and stamp, the pool unchanged), `metaInv_accepted` for that state, and `metaInv_foldl_admitRow` for the row fold. Difference from Step 2: the `treeWire` uniqueness and `proposalsNodup` use the fresh erased block `b ∉ st.base.blocks` (`accepted_base_facts`) with `wireTree` + `baseTree` (`wire_block_mem`: the block of every stored wire is in the base list), not `blocksNodup` + `rootInj`; `blocksNodup` is kept by the same fact. `stored_wire_of_block` uses `treeWire`, `wireTree` and `rootInj` (the wire's FG block has the same root). `fg_eq_of_eraseFG_eq_across` is a structural induction on `X` (no depth measure). `preceq_iff_across` backward uses the new helper `eraseFG_ancestor_preceq` (`eraseFG_ancestor_mem` that also returns `C ⪯ Y`). `rootInjectiveOn_across` uses the new helper `fg_eq_of_root_eq_across` (genesis by local root injectivity, else `stored_wire_of_block` + `hc` + `fg_eq_of_eraseFG_eq_across`) for the two cross-store cases, and `rootInj` for the two same-store cases; `compatible_iff_across` uses `contentAgree_symm`. Other extra helpers: `admitVote_stamps`, `foldVotes_stamps`, `writeKeys_stamps`, `saGate_stamps`, `gateStep_stamps`, `clockPre_stamps`, `admitProposal_prefix`, `block?_proposal`, `accepted_rows_decode` (DQ12). Validation: `lake build --wfail AvailableChainFGSA` and `bash scripts/check-fgsa.sh` pass (775 constants, 422 theorems; standard axioms only).

**G12 dispositions** (review of `5c0230e`: PASS WITH FIXES; 0 blocking, 1 major, 3 minor; report `docs/audit/fgsa-task12-opus-review.md`). M1 (coordinator decision, option (a)): `ContentAgree` is narrowed to "equal roots → the same erased block and the same rows"; the raw-vote and support parts are dropped (DQ3(b) note: "narrowed at G12"). The premise is weaker, so the four cross-node theorems are stronger; their statements are unchanged, and the proofs read the two conjuncts directly (the reviewer's `Weak.lean` showed the same). The Task 13 report gets the premise-scope line, and the T7 inputs get the run lemma "every stored wire is a payload that the node processed". m1: new `MetaInv` field `noGenesisWire`, proved by the same induction with no new premise (`blockAccepted` refuses genesis; `hg` in `metaInv_accepted`), and new `contentAgree_self` (`Proofs/CrossNode.lean`): one store agrees with itself under `CStoreInv` and `MetaInv`. m2: the `MetaInv` docstring, the DQ12 line and the G6 item 9 row now name the `round?` filter of `proposalRows` and `blockWireRows` as the reason that no candidate has the key `none`, on every store. m3 (G11 M1 at `5c0230e`): fixed in `2ca677a`. G12 is closed.

---

### Task 13: Axiom audit, full build, map, handoff

**Files:**
- Create: `AvailableChainFGSA/Tests/Axioms.lean`
- Modify: `AvailableChainFGSA.lean`, `lakefile.toml` (`defaultTargets`), `docs/MAP.md` (one new section)

- [x] **Step 1: `Tests/Axioms.lean`.** One `#print axioms` line for each public theorem of Tasks 2 and 7–12 (as `AvailableChainSA/Tests/Axioms.lean`). Each must print only `propext`, `Classical.choice`, `Quot.sound`, or no axiom.
- [x] **Step 2: Axiom scan.** ONE `--expect` flag, then all names (audit M6; the parser sets `expected := args.drop 1`):
  `lake env lean --run scripts/CheckFGSAAxioms.lean --expect outputNesting_stored storeInvariant fMonotone metadataInvariant reconcile_harmless_origin admitBlock_reconcile_harmless reconcile_frame viewRootInj_of_rootInj preceq_of_eraseFG_preceq fg_eq_of_eraseFG_eq_across rootInjectiveOn_across clock_eq_saClock_gate actView_admitBlock_sameF admitBlock_sufficient actView_releaseCount_zero`. Expected: exit 0.
- [x] **Step 3: Full build.** Add `"AvailableChainFGSA"` to `defaultTargets`. Run `pgrep -fl lean`; wait for a free slot. Run `lake build --wfail` (the full project target). Expected: PASS for every library. Then `bash scripts/check-fgsa.sh`. Expected: exit 0.
- [x] **Step 4: Map.** Add a section "FG-SA composite model (store)" at the end of `docs/MAP.md`: one row per file, with its role and the K ids. Plan 1a also edits `docs/MAP.md`; add only the new section, so that a merge has no overlap.
- [x] **Step 5: Report to the coordinator** (no `log.md` or `state.md` in this worktree unless the coordinator asks). The report has:
  - a table that separates completed local facts from the remaining run lifts: K id / blueprint id → Lean names → extra hypotheses. At least: K1 → `reconcile_harmless_origin`, `admitBlock_reconcile_harmless` (no fastWrite premise; `reconcile_harmless` is a helper); K2 → `outputNesting_stored` (run lift: T7); K3 → `reconcile_frame`, `storeControls_reconcile`; K4 → `storeInvariant` (core), `metadataInvariant` (metadata); K5 → local: `viewRootInj_TF`, `compatible_iff_eraseFG`; cross-node: `fg_eq_of_eraseFG_eq_across`, `preceq_iff_across`, `compatible_iff_across`, `rootInjectiveOn_across` (the two-chain `KitFG.accountable` premise) with the premise `ContentAgree` (DQ3(b), reverses comp D4; run form `ContentRootInjective` in T7); K8 input → `admitBlock_sufficient`; activeView → the six items; SA bridges → `clock_eq_saClock_*` (`hnew`), `actView_admitBlock_*`;
  - every difference found against the spec, the blueprint and comp §4, and every smoke-test value that differed from the hand computation;
  - the answers used for DQ1–DQ14 and each audit finding that is still open;
  - the validation commands and their results (build, check script, axiom scan);
  - the inputs for composition task T7: the duty-slot condition `s = st.slot p` of `headVote` and `propose` (G6 O-m3); the Q1 boundary table (with the v1 object dependency, J1), `blockExcluded_stable`, `wellFormed` and `blockAccepted_of_wellFormed`, "processed by root" (DQ9), `attest`, the content premise (DQ3) and the DQ10 root limit, the Λ placement (DQ4), and the one-tick-per-time premise that `clock_eq_saClock_gate` needs (DQ5);
  - the K4 clause "F, J ∈ T" of `bp.store.v1` (G11 m2): `storeInvariant` (`Fmem`) with `J_mem`; the other `bp.store.v1` clauses: "T is cumulative" and "old states/stamps are unchanged" by `process_cumulative`, `clock_cumulative` and `MetaInv` (Task 12), and the tick part of "pair and H monotone" by `clock_fg`;
  - the content premise (G12 M1): "`ContentAgree` is a run premise (DQ3(b), narrowed at G12 to the erased block and the rows). It is false on honest-fork runs under the present root formula (DQ10/I9) and on runs with faulty content equivocation; the cross-node lemmas (`fg_eq_of_eraseFG_eq_across`, `preceq_iff_across`, `compatible_iff_across`, `rootInjectiveOn_across`) are vacuous for such store pairs. One store with itself needs no premise (`contentAgree_self`)." And the T7 input: deriving `ContentAgree` needs the run lemma "every stored wire is a payload that the node processed";
  - the K1 reading (G9 m2): "K1 `hL`: live = present in `Σ.lease` (`obligations`), including due leases that the next tick expires (spec 447–448, 736–741)". So theorem (b) and K7 in T7 must show compatibility for due leases as well;
  - the inputs for composition task T1 (registry): `comp.outputNesting.v2`, `bp.store.v1`, `bp.reconcile.v1`, `bp.carrier.v1`, `bp.activeView.v1` with the Lean names.
- [x] **Step 6: Review gate G13 (final) and CHECKPOINT.** Commit `FGSA store: axiom audit, full build, map`.
  G13 check item (G9 m3): no file cites `reconcile_harmless` (the filter form, with a fastWrite premise) as K1; the K table keeps it in the helper column.
  Execution notes (2026-09-29): the checkpoint is the commit that adds this note; G13 (full audit, Astra plus Opus) passed with fixes (dispositions below). Step 1: `Tests/Axioms.lean` has 206 `#print axioms` lines, one for each theorem of `Proofs/BlockAncestry`, `Carrier` (Task 2) and `Fields`, `ActView`, `Nesting`, `Reconcile`, `Admission`, `StoreInv`, `Metadata`, `CrossNode` (Tasks 7–12), generated from the `theorem` lines; the root imports it. Printed sets: 123 × {propext, Classical.choice, Quot.sound}, 53 × {propext, Quot.sound}, 22 × {propext}, 8 × none. Step 2: the `--expect` scan with the 15 names exits 0 (784 constants, 431 theorems). Step 3: `"AvailableChainFGSA"` is in `defaultTargets`; `lake build --wfail` (full project target) passes (3600 jobs); `bash scripts/check-fgsa.sh` exits 0 (with the lease-instance check of G11 and its negative control). Step 4: `docs/MAP.md` has the new last section "FG-SA composite model (store)" (one row per file, role, K ids; append only). Step 5: the report went to the coordinator by message; with the G13 corrections it is `docs/FGSA-STORE-REPORT.md`. The G13 check item holds: `reconcile_harmless` appears only at its definition, in the origin form's proof, and in `Tests/Axioms.lean`; the MAP row calls it a helper.

**G13 dispositions** (final audit of `8e8b61e`: Astra r199 `docs/audit/fgsa-final-audit-astra.md`, READY WITH FIXES, 0 blocking, 2 major, 3 minor; Opus `docs/audit/fgsa-final-audit-opus.md`, READY WITH FIXES, 0 blocking, 0 major, 5 minor, with an independent build of all FGSA modules and an axiom walk of 13,926 constants). No finding changes a theorem, a statement or a model rule. (1) Lease scan (Astra M1 = Opus m2): `scripts/CheckFGSALease.lean` skips only generated equation lemmas (`eq_<k>`, `eq_def`) of a definition declared outside the scanned modules, and inspects that definition; every other FGSA-module declaration must have no policy parameter; parameter types are reduced by `whnf` (aliases of `LeasePolicy` are caught); every reached imported `AvailableChain.*` definition is inspected (a bound policy is accepted there only as a generic pass-through; a closed policy must be `slowLeasePolicy`); the script states what is trusted (imported theorem proofs; definitions outside `AvailableChain`). Controls: the direct default call, the Astra alias wrapper, a generic wrapper with an alias policy type (Opus), and an imported wrapper that fixes the default; all rejected. (2) Imports (Astra M2, Opus m1): `check-fgsa.sh` parses import headers after comment removal (the existing tokenizer), applies the direct allowlist with its directory rules (KitFG only in `Statements/` and `Proofs/`, GridCO proofs only in `Proofs/`, internal layers Model < Statements < Proofs, root and Tests any FGSA module), and checks the root imports on the parsed header; `CheckFGSAAxioms.lean` requires every `AvailableChainFGSA/**/*.lean` module in `env.header.moduleNames` and rejects Framework, Registry, SAPC and Witnesses modules in the compiled closure (`AvailableChainStatements` stays allowed). Controls: an unlisted library, two wrong-layer imports, a forbidden import after a comment and a line break, an orphan module with a `sorry` behind a commented root import (root check and compiled coverage check), and SAPC in the closure; all rejected. (3) Astra N1: both Lean check scripts are required; a missing one exits 2. (4) Opus m3: `contentAgree_self` needs `CStoreInv` and `MetaInv` (no content premise); `ContentAgree` is the store-pair premise, the run premise is `ContentRootInjective` (report, `docs/MAP.md`). (5) Opus m4: new `Tests/RootCollision.lean` (the Opus witness; "DQ10/I9 limit, not a defect of the model"): two honest blocks with root 4; `CStoreInv` and `MetaInv` hold; `ContentAgree` and the conclusion of `rootInjectiveOn_across` fail; a node that holds one block refuses the other (DQ2). T7 input line added. (6) Opus m5: the Q1/Q5 grep reads comment-free text and also matches `Run`, `Env`, `Interface`, `Claims`. (7) Astra N2: the report says "no new undeclared rule difference at the stated protocol boundary", lists the release-cutoff difference (r195 D2) and adds the release event order to the T7 inputs; `storeControls_eq` needs `CStoreInv` in the K3 row; the report has a scope paragraph. Astra N3: new `stL` tests in `Tests/Smoke.lean`: an active stored target (`X` in `stK`, F = genesis) outside the full filtered tree; the live root is Z = genesis and C_fg = none, and a scratch check of the wrong rule (the active tree in place of `fullTree`) gives `eraseFG X` and `some X`. New files outside the Global Constraints list: `scripts/CheckFGSALease.lean` (G11), `Tests/RootCollision.lean`, `docs/FGSA-STORE-REPORT.md` (coordinator request). Validation: `lake build --wfail` (full project, 3601 jobs) passes; `bash scripts/check-fgsa.sh` exits 0 with every negative control rejected; the `--expect` scan exits 0 (805 constants, 442 theorems). G13 is closed. The merge into main is a separate step that the coordinator starts after plan 1b.

**G13 fold verification dispositions** (Opus verification of `8f61f06`: CLOSED WITH FIXES, 0 blocking, 0 major, 2 minor; report `docs/audit/fgsa-final-audit-fold-verify.md`). Neither minor was a present defect; no theorem, statement or model rule changes. MINOR-1 (lease check, imported definitions): `scripts/CheckFGSALease.lean` now accepts, in an inspected imported definition, only the definition's own policy parameters (the policy-typed leading binders of its type and value, opened as free variables); a variable bound by an inner `let` or `fun` fails. The namespace test uses the name without its `private` prefix. Policy types are classified by `whnf` with all transparency (an `@[irreducible]` alias is caught). A reachability backstop: in the closure of the scanned constants (types and values, all namespaces, private names; imported theorem proofs excluded), no constant may mention `gridLeasePolicy`, and only the value of `slowLeasePolicy` may mention `LeasePolicy.mk`. The header states that theorem proofs are scanned too (kept on purpose). On the clean tree the check finds the same 34 (owner, callee) policy-use pairs as before; the argument count falls from 116 to 76 because opened binders make repeated subterms equal, so the scan visits them once. MINOR-2 (import allowlist): `scripts/CheckFGSAAxioms.lean` checks the allowlist and layer rules again on the compiled direct imports (`env.header.moduleData[i].imports`; `Init` allowed; a module directly under the root or in another directory may import nothing else), and its coverage rule accepts the extension in any case. In `check-fgsa.sh` the header parser fails closed (`UNPARSED IMPORT HEADER` if the token `import` or `prelude` remains, which covers a `«»` module name and a `prelude` line), and every source enumeration is `find -L … -iname '*.lean'`. New controls (the auditor's files in `scripts/fgsa-controls/`): the four header and file-name bypasses (text allowlist, Q1/Q5 grep, compiled allowlist over a copy of the FGSA build), an orphan `.LEAN` module (root check and coverage), the imported let, beta, private, irreducible-alias and non-`AvailableChain` wrappers, and a `LeasePolicy.mk` wrapper outside `AvailableChain` (backstop); all rejected. Validation: `bash scripts/check-fgsa.sh` exits 0 (805 constants, 442 theorems, 5503 modules, direct imports of 21 FGSA modules; lease: 788 constants, 17 equation lemmas skipped, 335 imported definitions, 76 lease arguments, 4203 constants reached); every negative control is rejected; the `--expect` scan with the 15 names exits 0, and with a missing name exits 2.

## Review gates

```text
┌─────────┬─────────────────────┬─────────────────────────────────────────────────────┐
│ Gate    │ When                │ Who and what                                        │
├─────────┼─────────────────────┼─────────────────────────────────────────────────────┤
│ G0      │ before Task 1       │ Two plan audits (Astra r185, Opus): both REVISE;    │
│         │                     │ applied in revision 2. Second audit (Astra r188):   │
│         │                     │ PASS WITH MINORS (= ADOPT WITH FIXES), no blocking  │
│         │                     │ or major finding; N1–N6 applied in revision 2.1.    │
│         │                     │ CLOSED. Reports in docs/audit/.                     │
│ G1–G5   │ end of Tasks 1–5    │ independent review (a fresh reviewer agent that did │
│         │                     │ not write the code): each definition against its    │
│         │                     │ spec lines; each test value by hand; the Global     │
│         │                     │ Constraints (M11, J1). Findings go to the task      │
│         │                     │ report.                                             │
│ G6      │ end of Task 6       │ Astra model check of Model/*.lean against the spec  │
│         │                     │ and the tree-read inventory (Task 6, Step 4), plus  │
│         │                     │ the independent review. Before the store proof      │
│         │                     │ tasks 7–12 (Task 2 is independent of the model).    │
│ G7–G12  │ end of Tasks 7–12   │ independent review: each statement against its      │
│         │                     │ blueprint statement (bp00 §3.1); no weakened        │
│         │                     │ statement; no new hypothesis without a report line; │
│         │                     │ the explicit lease instance; axioms of the new      │
│         │                     │ theorems.                                           │
│ G13     │ end of Task 13      │ final independent review of the whole library and   │
│         │                     │ the report; the coordinator decides on the merge.   │
└─────────┴─────────────────────┴─────────────────────────────────────────────────────┘
```

A reviewer blocks the CHECKPOINT on: a model rule that differs from the spec without a report line; a statement weaker than its blueprint statement without a report line; a `sorry`, `admit`, project axiom or native evaluation; a direct import outside the allowed list or a forbidden library in the import closure; a Q1/Q5 dependency other than the declared v1 object types; a lease-dependent GridCO lemma without `@… GridCO.slowLeasePolicy`; a free `n` next to `p : Params`.

## Out of scope

- The run layer (composition T7): the `ProtocolSpec` instance, the hooks binding, `ClockLaws`, stamps, receipts, paths, carried-row signatures, the run form of K8, and the run form of nesting.
- The engine choice (Q1) and the deliverable form (Q5): the Λ placement, the own-row processing, `pendingRow`, the `LinkedFG` premise, `FGSAClaims`. A v2 decode adapter (J1).
- The run premise `ContentRootInjective` and its derivation of `ContentAgree` for honest stores (DQ3); the registry entries (composition T1).
- K6–K11 and theorems (b), (c), (c′), (d) (composition T8–T16).
- The lease parts of `bp.leaseOrigins.v1` (a successful gate origin of each live target, one-chain live targets, ancestor deadlines). They are local facts (a `Reachable` induction suffices, as for `FastOrigin`), but no task of T3–T6 needs them; composition T10/T12 states them.
- A change of the honest root formula (DQ10 alternative); it is a cross-library user decision.
- The leak ledger. The model is ready for it as a derived function (Global Constraints).

## Known limits

- (G6 O-m4) `GridCO.goldfishScore` counts a supporter only if its seat is in the raw list (`seats n raw`); the spec score (spec 1039–1048) counts every clean seat of the support list. The two agree when support ⊆ raw. This holds by construction for the frozen arm, the proposer and the FG action. For the carried arm it needs `B.support ⊆ B.votes`, which `wellFormed` checks but `process` does not run (DQ14). So the HEAD score equals the spec score only when T7 binds the input check. Inherited from GridCO; no model change.
- (G6 O-m3) `headVote` and `propose` take the slot `s` but read `Σ.s` through `eligible` and `proposalRows`; they agree with the spec only when `s = st.slot p` (a T7 caller obligation).

## Risks

```text
┌─────┬──────────────────────────────────────┬──────────────────────────────────────┐
│ ID  │ Risk                                 │ Mitigation                           │
├─────┼──────────────────────────────────────┼──────────────────────────────────────┤
│ R1  │ decide is slow on composite states   │ Bool-valued tests; decide +kernel;   │
│     │ (Finset, derive, GridCO lists); it   │ smaller fixtures; report fallbacks.  │
│     │ can fail on a TRUE statement (max    │ Use decide +kernel where plain       │
│     │ recursion depth: seen on stV and     │ decide fails (a robustness risk,     │
│     │ stP, G5)                             │ not a soundness risk)                │
│ R2  │ A GridCO lemma is lease-dependent    │ apply it with @… GridCO.slowLease-   │
│     │ (the DEFAULT instance silently gives │ Policy (Global Constraints); if it   │
│     │ the GRID gate) or is private         │ is private, prove a local form       │
│ R3  │ Plan 1b changes GridCO/SA hooks (E4  │ this plan uses only GridCO/SA state  │
│     │ excludes)                            │ functions, not their ProtocolSpec;   │
│     │                                      │ rebuild after a rebase               │
│ R4  │ Merge overlap with plan 1a in        │ append-only edits; one new MAP       │
│     │ lakefile.toml and docs/MAP.md        │ section; resolve at merge            │
│ R5  │ The FG module test fixtures (B1, B2, │ if they change, copy them into       │
│     │ B3, B1', stF) change                 │ Tests/Smoke.lean                     │
│ R6  │ A new frozen spec version before     │ diff against 2e884811; report each   │
│     │ execution                            │ modeled line (Sources, note 1)       │
│ R7  │ The exact SA bridge equality needs   │ state each extra premise; the bridge │
│     │ more premises than planned           │ is a reuse tool, not a spec claim    │
│ R8  │ The Mac lean slots are shared        │ pgrep before each build; module      │
│     │                                      │ targets during steps                 │
│ R9  │ Root premises are vacuous on runs    │ declared (DQ10); inherited from      │
│     │ with arithmetic-root collisions      │ GridCO/SA; alternative is a user     │
│     │                                      │ decision                             │
│ R10 │ Engine v2 needs a re-typing of the   │ all auth reads in the decoders (J1); │
│     │ object layer                         │ a v2 decode adapter keeps Store,     │
│     │                                      │ Statements and Proofs; a native      │
│     │                                      │ re-typing also touches the wire      │
│     │                                      │ constructors of the handlers, the    │
│     │                                      │ .auth test of proposalRows and the   │
│     │                                      │ v1 SA base (r188 N5; scope in T7)    │
│ R11 │ The cross-node proof needs a MetaInv │ state the extra field in the task    │
│     │ field that this plan does not list   │ report; do not weaken ContentAgree's │
│     │                                      │ conclusion                           │
└─────┴──────────────────────────────────────┴──────────────────────────────────────┘
```

## Open questions (summary)

- Q1 (engine) and Q5 (deliverable) stay open. This plan has no binding to them; its objects are v1-typed (J1).
- DQ1–DQ14 above, each with a recommended answer. The plan follows the recommendations. The second G0 audit (r188) accepted them. The user can still change them.
- User decision (DQ10, DQ3): keep the arithmetic honest root and the content premise (this plan), or move to content-coded roots with an admission check across GridCO/SA/FG-SA (comp D4 as written).
- For composition T7: the duty-slot condition `s = st.slot p` for `headVote` and `propose` (G6 O-m3); the one-tick-per-public-time premise (DQ5, `clock_eq_saClock_gate`), the content premise `ContentRootInjective` (DQ3), checked inputs at every handler call (DQ14), and "processed by root" (DQ9).

## Disposition of audit findings

A = Astra r185 (`docs/audit/fgsa-model-store-plan-audit-report.md`). O = Opus (`docs/audit/fgsa-model-store-plan-opus-review.md`). Every finding is applied unless the row says "rejected" or "partly".

```text
┌────────────┬──────────────────────────────────────────┬──────────────────────────────┐
│ Finding    │ Change                                   │ Section                      │
├────────────┼──────────────────────────────────────────┼──────────────────────────────┤
│ A B1 = O B1│ Every p-dependent API on State p.n, Wire │ Global Constraints (M11);    │
│ (blocking) │ p.n, Fin p.n; no casts; fixtures State 4 │ Design M11; Tasks 3–12 code; │
│            │ = State pT.n (compiled)                  │ Review status                │
│ A M1       │ One row check RowWire.valid for both     │ Design M12; DQ12, DQ14;      │
│            │ forms; wellFormed complete; tests of the │ Task 1 Objects; Task 4       │
│            │ same row in both forms; Reachable is an  │ wellFormed and tests; Task 7 │
│            │ over-approximation, T7 checks inputs     │ Reachable doc                │
│ A M2 +     │ Named premise ContentAgree (store pair)  │ DQ1, DQ3; Q1 boundary; Task  │
│ O M2       │ and ContentRootInjective (run, T7);      │ 12 (ContentAgree, cross-node │
│            │ DQ3(b) REVERSES comp D4 (stated); K5     │ lemmas); Task 10             │
│            │ cross-node stated with it; row-position  │ toRow_forall₂; Task 2 label  │
│            │ lemma; Task 2 labeled "K5 local"         │ "local"; Task 13 report      │
│ A M3 +     │ Local invariant FastOrigin (Opus shape)  │ Task 7 (FastOrigin,          │
│ O M3       │ + fastDom in CStoreInv; preserved by     │ CStoreInv); Task 9           │
│            │ gate (fastOrigin_gateStep) and reconcile │ (reconcile_fastOrigin,       │
│            │ (reconcile_fastOrigin); K1 in blueprint  │ reconcile_harmless_origin);  │
│            │ form with no fastWrite premise; the      │ Task 11 (admitBlock_         │
│            │ "needs a run" text removed               │ reconcile_harmless)          │
│ A M4 +     │ MetaInv (wire ↔ FG block rows, one wire  │ Task 12 (MetaInv,            │
│ O M4       │ per block, stamp keys, pool shape);      │ process_cumulative); Task 10 │
│            │ cumulative-step lemmas; exact insertion  │ (admitBlock_accepted_eq,     │
│            │ of stamp and wires; lease and label key  │ base_admitProposal_accepts); │
│            │ uniqueness in CStoreInv                  │ Task 7 (CStoreInv keys)      │
│ A M5 /     │ Opus route: no DIRECT import of the five │ Global Constraints (Imports);│
│ O M5       │ libraries; the transitive Statements     │ Task 1 check-fgsa.sh         │
│            │ dependency through GridCO proofs is      │                              │
│            │ disclosed and allowed (plan 1a does not  │                              │
│            │ change Statements, 1a plan line 65);     │                              │
│            │ closure check against Framework,         │                              │
│            │ Registry, SAPC, Witnesses; grep of all   │                              │
│            │ five names. Astra's local-proof route    │                              │
│            │ rejected: it copies GridCO lemmas for no │                              │
│            │ soundness gain                           │                              │
│ A M6       │ One --expect with all names; copy also   │ Task 2 Step 4–5; Task 13     │
│            │ the importModules array; tests of a      │ Step 2                       │
│            │ present and a missing name (verified     │                              │
│            │ against scripts/CheckFGAxioms.lean)      │                              │
│ O J1       │ Q1 row and boundary: v1-typed objects;   │ Scope (Q1); Q1 boundary;     │
│            │ all auth matching in HeadWire.decode?,   │ Design M4; Task 1 Objects;   │
│            │ RowWire.decode?, Wire.decode             │ Task 4 handlers; R10         │
│ O J2       │ bp.activeView.v1 items 1, 2, 4, 6 added  │ Task 7 Step 3                │
│            │ (and the unchanged pools/stamps, Astra)  │                              │
│ O J3       │ Block-step SA bridge: actView_admitBlock │ Task 10; Design M2 (limit)   │
│            │ _sameF / _movedF; the GridCO-invariant   │                              │
│            │ limit on the view recorded               │                              │
│ A N1       │ Conflicting slot-3 block with a label-2  │ Task 4 tests; Task 5 gate    │
│            │ vote and a fresh row (separate calls     │ tests; Task 6 test (b)       │
│            │ admit them first); duplicate block;      │                              │
│            │ future-round row; stR1 renamed a         │                              │
│            │ handler-integration fixture; vetoed      │                              │
│            │ gate, unchanged-deadline fast renewal,   │                              │
│            │ slow-only renewal, proposal that leaves  │                              │
│            │ act(Σ) but stays in the HEAD merge       │                              │
│ A N2 +     │ deepest uses the spec tie rule (greater  │ DQ13; Task 6 deepest; Task   │
│ O m8       │ root); deepest_spec, fgBlockOf_spec,     │ 11                           │
│            │ fgHead_stored replace the old findings   │                              │
│ A N3       │ Reachable documented as arbitrary-clock  │ Task 7 Reachable doc and     │
│            │ over-approximation; no unconditional     │ bridge note                  │
│            │ release-helper equality; only a fresh-   │                              │
│            │ label premise on the gate bridge         │                              │
│ A N4       │ bp00 re-pinned (03afa5ae), diff from     │ Sources (note 4); Task 0     │
│            │ 6057f9b5 checked, ids exist; report file │                              │
│            │ name fixed; eraseFG_fgBlock cited in     │                              │
│            │ Task 10                                  │                              │
│ A N5       │ G6 "before store proof tasks"; Task 5    │ Task list; Review gates;     │
│            │ depends on Task 4; one writer for shared │ Global Constraints (Shared   │
│            │ files; sizes raised; no second identical │ files, Builds)               │
│            │ checkpoint build                         │                              │
│ O m1       │ clock_eq_saClock_gate states fw exactly: │ Task 5 clockPre; Task 7      │
│            │ fastSet of the view of clockPre; also    │ Steps 2, 4                   │
│            │ gateStep_fresh, fastSet_prefix           │                              │
│ O m2       │ Statements of admitBlock_accepted_eq,    │ Task 10                      │
│            │ fgBlock_*; acceptance sufficiency        │                              │
│            │ admitBlock_sufficient for K8             │                              │
│ O m3       │ PARTLY: the parent-slot and row-round    │ DQ9, DQ14; Task 4            │
│            │ tests are COPIED into wellFormed, not    │ wellFormed; Task 10          │
│            │ moved out of blockAccepted (a move would │ blockAccepted_of_wellFormed  │
│            │ make store invariants depend on checked  │                              │
│            │ inputs over the unchecked Reachable);    │                              │
│            │ blockAccepted_of_wellFormed gives the    │                              │
│            │ wanted refusal classes; "processed by    │                              │
│            │ root" for T7                             │                              │
│ O m4       │ DQ2 rationale: never fires for ANY       │ DQ2; Task 10; Task 11        │
│            │ processed block under RootInjective;     │                              │
│            │ rootTest_iff_blockTest;                  │                              │
│            │ rootInjectiveBelow_base                  │                              │
│ O m5       │ DQ5 text: SA.gate writes genuine once;   │ DQ5; Design M7               │
│            │ the composite guard adds the other       │                              │
│            │ skips; hnew from ScheduleWellFormed;     │                              │
│            │ v2 restore caveat                        │                              │
│ O m6       │ frozen, early, releaseSnapshots (and G,  │ Global Constraints (Model-   │
│            │ base.proposals) declared model-only      │ only caches); DQ8; Task 3    │
│            │ caches                                   │ State doc                    │
│ O m7 +     │ DQ10 collisions (honest fork and         │ DQ10; Review status; R9;     │
│ A M2 (DQ10)│ adversarial) stated with the consequence │ Open questions; propose doc  │
│            │ (vacuity); existing theorems checked;    │                              │
│            │ no claim of fresh honest roots           │                              │
│ O LeasePol.│ Explicit @… GridCO.slowLeasePolicy rule  │ Global Constraints; Task 7   │
│ trap (§1,  │ for every lease-dependent GridCO lemma;  │ saGate_blocks; R2; Review    │
│ Q4)        │ reviewer check                           │ Focus 11                     │
│ A: pickPair│ pickPair_some_spec (selector soundness)  │ Task 10                      │
│ sufficient │                                          │                              │
│ only       │                                          │                              │
│ A: σ.nj,   │ Declared as inherited reductions; attest │ Design M13; Task 6 attest    │
│ Λ.timeouts │ is a projection                          │ doc                          │
│ A: script  │ Header rule exception for the axiom      │ Global Constraints           │
│ header     │ script                                   │                              │
│ A: FG pin  │ Pins.lean:99–100 usable for unchanged    │ Sources, note 2              │
│ bridge     │ FG code, with the version note           │                              │
│ A/O DQ7    │ Comp T6 complete only after the T7 run   │ DQ7; Scope                   │
│            │ lift                                     │                              │
│ A/O DQ4    │ Record/emission order and own-row admit  │ DQ4                          │
│            │ stay T7 obligations; agrees with v2 E5   │                              │
│ O sizes    │ Estimate raised to 4.3–5.6k              │ Task list                    │
└────────────┴──────────────────────────────────────────┴──────────────────────────────┘
```

Rejected or partly applied: Astra M5's first route (prove the GridCO lemmas locally) is rejected in favor of the Opus direct-import rule, which both reports accept as sound; the transitive dependency is disclosed and checked. Opus m3 is applied partly (copy, not move), for the reason in the table and in DQ14.

## Disposition of the re-audit findings

R = Astra r188 (`docs/audit/fgsa-model-store-plan-reaudit-report.md`), on revision 2 (`5801ce6`). Verdict PASS WITH MINORS; all six minors are applied in revision 2.1.

```text
┌──────────┬──────────────────────────────────────────┬──────────────────────────────┐
│ Finding  │ Change                                   │ Section                      │
├──────────┼──────────────────────────────────────────┼──────────────────────────────┤
│ R N1     │ bp00 source is the verified archive copy │ Sources (table, note 4);     │
│          │ 00-outline-03afa5ae.md; the drift of the │ Task 0 Steps 1 and 5; Review │
│          │ current file (5a89d168) recorded; report │ status; Review gates (G0);   │
│          │ path fixed; PASS WITH MINORS mapped to   │ DQ11                         │
│          │ ADOPT WITH FIXES; G0 closed              │                              │
│ R N2     │ fastSet and fastSet_prefix take          │ Task 5 fastSet; Task 7       │
│          │ GridCO.State p.n (M11 holds with no      │ fastSet_prefix               │
│          │ exception)                               │                              │
│ R N3     │ Lease rule by the actual declaration,    │ Global Constraints           │
│          │ not by the section variable; examples of │ (LeasePolicy instances)      │
│          │ both kinds                               │                              │
│ R N4     │ rootInjectiveOn_across added (statement, │ Task 2 docstring; Task 12;   │
│          │ proof route); in the K5 handoff table    │ Task 13 Steps 2 and 5        │
│          │ and the axiom scan                       │                              │
│ R N5     │ v2: only the adapter route keeps the     │ Scope (Q1); Q1 boundary;     │
│          │ internal API; native re-typing scope is  │ Task 1 Wire.decode doc; R10  │
│          │ a T7 decision                            │                              │
│ R N6     │ deepest: the empty set and the tie of    │ DQ13; Task 6 deepest doc     │
│          │ maximal candidates documented            │                              │
└──────────┴──────────────────────────────────────────┴──────────────────────────────┘
```
