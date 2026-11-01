# I9 report: derived block roots

_2026-09-29. Plan: `docs/plans/2026-09-29-i9-derived-roots.md` (r4). Branch
`i9-derived-roots` from `a5aaf3c`, in the worktree
`~/worktrees/available-chain-i9`. Ledger:
`.superpowers/sdd/2026-09-29-i9-derived-roots/progress.md` (not in Git).
Design: `docs/FRAMEWORK-DESIGN.md` §12 I9 and §2 E4._

This report is the Task 11 Step 4 record. It is in the branch before the
merge, so that the links to it from `FRAMEWORK-DESIGN.md` §12 I9 and from
the plan's named-exception note are not dangling (docs review, factual
error 2). It gives the tasks and commits, the checks, the lock break with
its names, every statement change (old and new text), every fixture whose
intent changed, and the decisions that the controller took without the
user.

## 1. Summary

### The problem

Before I9, `Block.node` carried a supplied `root : BlockId`. Honest proposers
computed it with the formula `s * (parent.root + 1)` (Grid CO, SA, SA-PC, L*
and FG-SA `propose`). This formula collides on forks: slot 4 on genesis and
slot 2 on the slot-1 block both get root 4. Every regime has the premise
`RootInjective` (`AvailableChainStatements/Generic/Conditions.lean`), so an
adversary could leave every regime, and the certificates gave no guarantee
against a forged collision (`FRAMEWORK-DESIGN.md` §12 I9).

### The user decisions of 2026-09-29

`FRAMEWORK-DESIGN.md` §12 I9 records two user decisions. The plan implements
them as D1, D2 and D8.

- D1. The root is a function of the content (`root(B) := H(content)`, with
  `H` injective). A block does not carry its own root. It carries its
  parent's root.
- D2. The parent-root check is the store dependency lookup
  (`depsPresent`/`blockKnown`) only. An unknown parent root is a temporary
  missing dependency. So `excludes` gets no clause, SA-PC keeps its `rfl`,
  and wire validity has no root check. Wire forwarding rules wait for a P2P
  spec discussion.
- D8. I9 comes before Phase 2 and plan 1c.

The user also decided that this change is a contract and lock break, with its
own plan and a full audit after plan 1b.

### What I9 changed

- Model. `Block.node (parent : Block) (slot : Slot) (body : Nat)` replaces
  `Block.node parent slot (root : BlockId)`. `Block.root` computes the root:
  `nodeRoot pr s x := ⟨epair pr.value (epair s x) + 1⟩`
  (`AvailableChainModel/Objects/Blocks.lean`). `epair` is a length-delimited
  pairing with a total log-step `bitLen` (`AvailableChainModel/Objects/Codec.lean`).
- Injectivity. `Block.root_injective` holds on the whole `Block` type. So
  `RootInjective` is a theorem for every run: `rootInjective_all`
  (`AvailableChainKit/Roots.lean`). The FG forms are `FGBlock.root_injective`,
  `rootInjectiveOn_all` and `viewRootInj_all`. Grid CO has
  `rootInjectiveBelow_all`; FG-SA has `rootInj_all`.
- Lookup. `parent_mem_iff_root` and `parent_mem_and_iff_root` show that "the
  store holds the carried parent" is equivalent to "the store holds a block
  with the parent's root". Each protocol proves its lookup form and a no-op
  fact for a missing parent.
- Honest body. Honest proposers use body `0` (D5); the FG-SA proposer uses
  `packBody 0 rows`. The old root formula is removed.
- FG. `FGBlock.node (parent) (slot) (body : Nat) (rows)`, with
  `FGBlock.root (.node p s x rs) = nodeRoot p.root s (encFGBody x rs)` under
  the class `RowCodec V` (D10). `encFGBody` starts with the domain tag
  `fgBodyTag = 1`.
- FG-SA. The base body packs the application value and the ordered signed
  rows (`packBody`). `rowsOk` checks this packing in `wellFormed` and in
  `blockAccepted` (D9). With it, `ContentAgree` is a theorem (`contentAgree`,
  `contentAgree_reachable`).

### What I9 did not change

- No `Msg`, `Wire`, `Payload` or `Interface` type. Payloads carry resolved
  blocks (D3). This is a resolved-block model, not a root-only wire.
- No root or parent-root conjunct in any `wellFormed` or handler. No clause in
  any `excludes`. `blockKnown` keeps its definition. FG-SA's `rowsOk` is a
  content check, not a root check.
- The regime root fields (`rootInjective`), `CStoreInv.rootInj`, the `Inv0`
  conjunct and the `hroot`-type lemma premises stay (D6). The universal
  lemmas fill them. Their removal is a later plan.
- The contract statements `gridContract_from_engine`,
  `saContract_from_engine`, `sapcContract_from_engine`,
  `sapcStrong_from_engine`, plan 1b's `holds*` rows, the WindowMargin and hook
  facts, and every `AvailableChainFramework` declaration keep their text.

### Audits and reviews

- Plan r1: Astra `docs/audit/i9-plan-audit-report.md`, REVISE 3/5/2;
  fgsa-impl `docs/audit/i9-plan-fgsa-review.md`, ADOPT WITH FIXES 0/3/3.
- Plan r2: DC-simplify with fgsa-impl (`docs/audit/i9-plan-claude-review.md`),
  ADOPT WITH FIXES 0/1/6, all applied in r3.
- Plan r3: Astra `docs/audit/i9-plan-recheck-report.md`, REVISE 1/1/1.
- Plan r4: Astra `docs/audit/i9-plan-recheck2-report.md`, ADOPT 0/0/0. The
  branch starts at this commit (`a5aaf3c`).
- Branch, Tasks 0–8 (`a5aaf3c..e42bb37`): Astra, prompt
  `docs/audit/i9-branch-audit-0-8.md`, report
  `docs/audit/i9-branch-audit-0-8-report.md`, READY WITH FIXES 0/1/0. The
  one major finding (I9-A01) is resolved by a named exception (§5.10; §7,
  decision 4).
- Final branch review (`f0f656e...9b5892b`): Astra
  `docs/audit/i9-branch-final-report.md`, MERGE WITH FIXES 0/1/2. F1
  (major): `fg_ba` and `fg_bb` were deleted outside the statement rule;
  they are restored with their old text (§5.9). F2 (minor): the
  carried-vote check of the FG-SA duplicate smoke test `wDup` was vacuous;
  the test now carries a fresh label-2 vote that direct delivery admits
  (§6.1). F3 (minor): the `CONTRACT.md` D9 sentence, fixed in `7790316`
  (docs review, factual error 1). F1 and F2 are fixed in a separate Lean
  commit.
- Docs review of the branch documents (§9): Needs fixes (3 factual, 5 stale,
  3 inconsistencies, 9 minor); fixed in the final docs commit before the
  merge.

## 2. Tasks and commits

The branch commits, in order. Reviews: `Critical/Important/Minor`.

```text
┌─────────────┬───────────────┬────────────────────────────────────────────────┬──────────────────────────────┐
│ Task        │ Commit        │ Subject                                        │ Review                       │
├─────────────┼───────────────┼────────────────────────────────────────────────┼──────────────────────────────┤
│ 0 Codec     │ 031edab       │ Model: length-delimited codec                  │ APPROVED 0/0/5; m1 to Task   │
│             │               │                                                │ 9, m2 by the controller,     │
│             │               │                                                │ m3–m5 in e7aa163             │
├─────────────┼───────────────┼────────────────────────────────────────────────┼──────────────────────────────┤
│ 1 Block     │ e7aa163       │ Model: codec review minors                     │ APPROVED 0/0/3; all three in │
│             │ d4a3c00       │ Model: derived block roots; universal root     │ 782b6fb                      │
│             │               │ injectivity                                    │                              │
├─────────────┼───────────────┼────────────────────────────────────────────────┼──────────────────────────────┤
│ 2 Kit       │ 782b6fb       │ Model, Kit: Task 1 review minors               │ APPROVED 0/0/0               │
│             │ a7c8261       │ Kit, EngineV2, Framework: derived roots        │                              │
├─────────────┼───────────────┼────────────────────────────────────────────────┼──────────────────────────────┤
│ 3 Grid CO,  │ 6736f31       │ GridCO, SA: derived roots                      │ APPROVED 0/0/2; both in      │
│ SA          │               │                                                │ f821a9f                      │
├─────────────┼───────────────┼────────────────────────────────────────────────┼──────────────────────────────┤
│ 4 SA-PC     │ f821a9f       │ GridCO: Task 3 review minors                   │ APPROVED 0/0/3; all three in │
│             │ 1c319ca       │ SAPC: derived roots                            │ 98bd9a7                      │
├─────────────┼───────────────┼────────────────────────────────────────────────┼──────────────────────────────┤
│ 5 L*        │ 98bd9a7       │ SAPC: Task 4 review minors                     │ APPROVED 0/0/1 (report       │
│             │ 3b0a0b5       │ LStar: derived roots                           │ wording; parked)             │
├─────────────┼───────────────┼────────────────────────────────────────────────┼──────────────────────────────┤
│ 6           │ cd0bf37       │ Witnesses, Registry: derived roots             │ APPROVED 0/0/1 (unused       │
│ Witnesses,  │               │                                                │ lemmas; parked)              │
│ Registry    │               │                                                │                              │
├─────────────┼───────────────┼────────────────────────────────────────────────┼──────────────────────────────┤
│ 7 SimplexFG │ 521c34e       │ SimplexFG: FG blocks with a body; derived      │ APPROVED 0/0/3; m1, m2 in    │
│             │               │ roots                                          │ 4885a83                      │
│             │ 4885a83       │ SimplexFG: domain tag in encFGBody; review     │                              │
│             │               │ minors                                         │                              │
├─────────────┼───────────────┼────────────────────────────────────────────────┼──────────────────────────────┤
│ 8 KitFG     │ e42bb37       │ KitFG: derived roots                           │ APPROVED 0/0/2 (m1 parked;   │
│             │               │                                                │ m2 to §8)                    │
├─────────────┼───────────────┼────────────────────────────────────────────────┼──────────────────────────────┤
│ 9 FG-SA     │ 8298916       │ FGSA: signed content in block identity;        │ APPROVED 0/0/4; m1–m4 in     │
│             │               │ ContentAgree proved                            │ 731b4c5                      │
│             │ 731b4c5       │ FGSA: Task 9 review minors                     │                              │
├─────────────┼───────────────┼────────────────────────────────────────────────┼──────────────────────────────┤
│ 10          │ fc16b0a       │ docs: I9 derived roots (on i9-docs)            │ Astra pre-final audit READY  │
│ Documents   │               │                                                │ WITH FIXES 0/1/0; docs       │
│             │ 6ebbb26       │ I9 plan: named exception for deleted private   │ review: Needs fixes 3/5/3/9  │
│             │               │ root-proof helpers (on i9-docs)                │ (§9)                         │
│             │ aa36906       │ audit: Astra pre-final audit of I9 Tasks 0–8   │                              │
│             │               │ (on i9-docs)                                   │                              │
│             │ 4bdb7fa       │ Merge i9-docs                                  │                              │
│             │ b89ed5a       │ docs: I9 Task 9 facts; post-I9 FG-SA store     │                              │
│             │               │ notes                                          │                              │
├─────────────┼───────────────┼────────────────────────────────────────────────┼──────────────────────────────┤
│ 11 Build,   │ f756404       │ Merge main into i9-derived-roots before the    │ Task 11 checks: §3; docs     │
│ lock, merge │               │ lock step                                      │ review fixes: §9; Astra      │
│             │ 9b5892b       │ I9: lock break (91 names); full checks         │ final review MERGE WITH      │
│             │ 7790316       │ docs: I9 docs review fixes; I9-REPORT          │ FIXES 0/1/2 (§1)             │
│             │ (§10)         │ merge into main                                │                              │
└─────────────┴───────────────┴────────────────────────────────────────────────┴──────────────────────────────┘
```

Branch `i9-docs` started at `e42bb37` in a separate worktree (§7,
decision 9). `4bdb7fa` merged it after Task 9. `f756404` merged main into the
branch before the lock step, as Task 11 Step 2 requires. Main commits between
`a5aaf3c` and `f0f656e` are docs and plan commits of other sessions; they are
not I9 work.

## 3. Checks

Each task ran the `--wfail` build of the libraries that it owned or that an
earlier task owned. Downstream libraries were allowed to fail until their task
(plan "Build states"). Each task report also shows a grep with no `sorry`,
`admit`, `native_decide` or new axiom in the changed files.

```text
┌──────┬────────────────────────────┬──────────────────────────────────────────────────────────────┐
│ Task │ Build (`lake build         │ Other checks and axioms                                      │
│      │ --wfail`)                  │                                                              │
├──────┼────────────────────────────┼──────────────────────────────────────────────────────────────┤
│ 0    │ AvailableChainModel: 611   │ Laws: only propext, Classical.choice, Quot.sound. Spike: B3  │
│      │ jobs                       │ roots 4,433 bits (generic G02) and 21,373 bits (FG-SA        │
│      │                            │ packed); B4 20,956 and 166,846 bits. 14 `decide +kernel`     │
│      │                            │ checks (K1–K14): 4.25–4.29 s wall each against the 4.30 s    │
│      │                            │ import baseline (K0), peak RSS ≤ 1.39 GB (baseline 1.30 GB). │
│      │                            │ Stop rule not triggered.                                     │
├──────┼────────────────────────────┼──────────────────────────────────────────────────────────────┤
│ 1    │ Model, Statements,         │ `Block.root_injective`, `parent_mem_iff_root`,               │
│      │ Kit.Roots: 653 jobs; Kit:  │ `parent_mem_and_iff_root`, `rootInjective_all`: standard     │
│      │ 894 jobs                   │ axioms. EngineV2 failed at `Sketch.lean:95,104` (Task 2      │
│      │                            │ scope).                                                      │
├──────┼────────────────────────────┼──────────────────────────────────────────────────────────────┤
│ 2    │ Model, Kit, EngineV2,      │ `CatalogLock --check`: exit 1, 91 CHANGED, 0 REMOVED, exact  │
│      │ Framework: 923 jobs        │ match with `i9-lock-expected.tsv`. No `--write`.             │
├──────┼────────────────────────────┼──────────────────────────────────────────────────────────────┤
│ 3    │ GridCO, SA: 985 jobs       │ SA `Tests/Axioms.lean` (it also covers Grid CO): 76 → 81     │
│      │                            │ lines; 79 standard, 1 `[propext]`, 1 none. No `decide        │
│      │                            │ +kernel`.                                                    │
├──────┼────────────────────────────┼──────────────────────────────────────────────────────────────┤
│ 4    │ GridCO, SA, SAPC: 1124     │ SAPC `Tests/Axioms.lean`: 916 → 920 lines, allowed axioms    │
│      │ jobs                       │ only. Smoke: 18 checks true (`smokePass`). No `decide        │
│      │                            │ +kernel`.                                                    │
├──────┼────────────────────────────┼──────────────────────────────────────────────────────────────┤
│ 5    │ LStar, SAPC: 1117 jobs     │ SAPC `Tests/Axioms.lean`: 920 → 921 lines                    │
│      │ (SAPC alone after 98bd9a7: │ (`y_root_lt_x_root`). L* has no `Tests/Axioms.lean`; a       │
│      │ 1109 jobs)                 │ scratch check shows allowed axioms for the new L* lemmas. No │
│      │                            │ `decide +kernel`.                                            │
├──────┼────────────────────────────┼──────────────────────────────────────────────────────────────┤
│ 6    │ Witnesses: 3320 jobs;      │ `scripts/Registry.lean --check`: exit 0 before and after the │
│      │ Registry, Witnesses: 3559  │ regeneration; `REGISTRY.md`, `MATRIX.md` byte-identical.     │
│      │ jobs                       │ Three self-tests: exit 0. `CheckFrameworkAxioms`: 771        │
│      │                            │ constants. No `decide +kernel`.                              │
├──────┼────────────────────────────┼──────────────────────────────────────────────────────────────┤
│ 7    │ SimplexFG: 718 jobs        │ 14 `decide +kernel` switches; about 4.3 s wall and 0.84–0.89 │
│      │                            │ GB peak RSS per module. B3 root: 2,871 bits, 3,297 bits      │
│      │                            │ after `fgBodyTag`. New theorems: standard axioms.            │
├──────┼────────────────────────────┼──────────────────────────────────────────────────────────────┤
│ 8    │ KitFG: 3321 jobs           │ `scripts/check-fg.sh`: exit 0. `CheckFGAxioms`: 1209         │
│      │                            │ constants, 582 theorems. `FGPinIds --check-names`: 72 names. │
│      │                            │ `check-fg-pins.sh`: 14 sources, 13 pin ids, 8 active         │
│      │                            │ references, 9 not-formalized ids. `TwoChanges.lean`: 8.0 s,  │
│      │                            │ 1.96 GB.                                                     │
├──────┼────────────────────────────┼──────────────────────────────────────────────────────────────┤
│ 9    │ FGSA: 3381 jobs; after     │ `scripts/check-fgsa.sh`: exit 0; axioms 892 constants, 494   │
│      │ 731b4c5: 3382 jobs         │ theorems, 21 modules; lease 874 constants, 76 lease          │
│      │                            │ arguments; 10 negative controls refused. After 731b4c5: 893, │
│      │                            │ 495, 22; lease 875, 76. `Tests/Axioms.lean`: 206 → 222 → 223 │
│      │                            │ lines, none removed. Real `stA` checks: 4.33–4.39 s, ≤ 973   │
│      │                            │ MB; `Smoke.lean` 18.93 s, 1.17 GB; `RootCollision.lean` 8.04 │
│      │                            │ s, 1.88 GB. `--expect` scans: exit 0.                        │
├──────┼────────────────────────────┼──────────────────────────────────────────────────────────────┤
│ 10   │ none (docs only)           │ Eight controller slots: six filled in b89ed5a; two filled in │
│      │                            │ 9b5892b (Task 11: `CONTRACT.md`, `GRIDCO-STATUS.md`).        │
├──────┼────────────────────────────┼──────────────────────────────────────────────────────────────┤
│ 11   │ all 14 default targets:    │ The full checks of Task 11 Steps 1–2 (next table).           │
│      │ 3,629 jobs                 │                                                              │
└──────┴────────────────────────────┴──────────────────────────────────────────────────────────────┘
```

Task 11 Steps 1 and 2 ran on `f756404` (main merged in) and committed
`9b5892b`. Before each build or script run, no Lean process was active.

```text
┌────────────────────────────────────────┬──────────┬──────────────────────────────────────────────────────────┐
│ Command                                │ Exit     │ Result                                                   │
├────────────────────────────────────────┼──────────┼──────────────────────────────────────────────────────────┤
│ lake build --wfail (all 14 default     │ 0        │ 3,629 jobs, 0 warnings.                                  │
│ targets)                               │          │                                                          │
├────────────────────────────────────────┼──────────┼──────────────────────────────────────────────────────────┤
│ lake env lean --run                    │ 0        │ 771 constants checked.                                   │
│ scripts/CheckFrameworkAxioms.lean      │          │                                                          │
├────────────────────────────────────────┼──────────┼──────────────────────────────────────────────────────────┤
│ bash scripts/check-fg.sh               │ 0        │ 1209 constants (582 theorems) in the axiom check; 72     │
│                                        │          │ pinned names; 14 sources, 13 pin ids.                    │
├────────────────────────────────────────┼──────────┼──────────────────────────────────────────────────────────┤
│ bash scripts/check-fgsa.sh             │ 0        │ build 3,382 jobs; axioms 893 constants, 495 theorems;    │
│                                        │          │ lease 875 constants; 10 negative controls refused.       │
├────────────────────────────────────────┼──────────┼──────────────────────────────────────────────────────────┤
│ scripts/Registry.lean --check          │ 0        │ No output: `REGISTRY.md` and `MATRIX.md` are current.    │
├────────────────────────────────────────┼──────────┼──────────────────────────────────────────────────────────┤
│ Registry --selftest (3 self-tests)     │ 0        │ Each output is equal to its `.expected` file (the        │
│                                        │          │ `sorry` warning of `Unsound.lean` is intended).          │
├────────────────────────────────────────┼──────────┼──────────────────────────────────────────────────────────┤
│ grep sorry, admit, native_decide,      │ —        │ 0 hits for `sorry`, `native_decide` and `^axiom`. With   │
│ ^axiom over the 60 changed Lean files  │          │ `grep -w`, 4 hits of the word "admit", all docstring     │
│ (not scripts/registry-selftest/)       │          │ prose (FGSA Tests/Smoke:225, GridCO Tests/Smoke:104,     │
│                                        │          │ SimplexFG Client:228, 232); no tactic.                   │
├────────────────────────────────────────┼──────────┼──────────────────────────────────────────────────────────┤
│ Import coverage (transitive import     │ —        │ 304 of 307 modules reached. The 3 SA-PC `Pending/*`      │
│ walk from each library root)           │          │ modules are in no default target (as before I9;          │
│                                        │          │ `MAP.md`). The controller compiled all three on this     │
│                                        │          │ tree with no error.                                      │
├────────────────────────────────────────┼──────────┼──────────────────────────────────────────────────────────┤
│ CatalogLock --check, --write, --check  │ 1, 0, 0  │ The lock break: §4.                                      │
└────────────────────────────────────────┴──────────┴──────────────────────────────────────────────────────────┘
```

Limit: the full build did no new work. All 3,629 jobs were up to date from
the task builds, because `f756404` changed docs only. `--wfail` applies to
the replayed logs, and Lake traces are content hashes, so the result is
valid for this tree. It is not a clean rebuild.

## 4. The lock break

The type of `Block`'s third constructor argument changed from `root : BlockId`
to `body : Nat`. Every lock line whose dependency closure goes through
`AvailableChain.Block` changes its hash. `docs/catalog.lock` has 250 lines:
91 lines change and 159 lines stay. No declaration in `AvailableChainFramework`
changes its source text or its type; the lines change only because their
closure changes.

Astra computed the 91 names with the lock dependency algorithm on the compiled
tree (plan Finding 5, audit A08). r203's `lock-impact.tsv` also marked ten
scalar `_le_trans` theorems; they do not reach `Block`, so they are not in the
set. The expected set is `docs/plans/i9-lock-expected.tsv`.

The 91 names, grouped by module. The prefix `AvailableChain.Framework.` is
left out.

```text
┌─────────────────────────────┬────────────────────────────────────────────────────────────────────┐
│ Module (count)              │ Names (in a Catalog row, each name has the prefix `Catalog.`)      │
├─────────────────────────────┼────────────────────────────────────────────────────────────────────┤
│ Instance.lean (13)          │ Instance, Instance.P, Instance.hooks, Instance.iface, Instance.mk, │
│                             │ Instance.n, Instance.Δ, Instance.Δ_pos, V1Ctx, V1Ctx.E, V1Ctx.mk,  │
│                             │ V1Ctx.rho, ClaimDomain.v1                                          │
├─────────────────────────────┼────────────────────────────────────────────────────────────────────┤
│ Facets/Strong.lean (7)      │ StrongInstance, StrongInstance.mk, StrongInstance.sface,           │
│                             │ StrongInstance.strong, StrongInstance.toInstance,                  │
│                             │ ClaimDomain.strong, DomainMap.strongV1                             │
├─────────────────────────────┼────────────────────────────────────────────────────────────────────┤
│ DomainMap.lean (2)          │ ClaimDomain.ofV1, DomainMap.ofV1                                   │
├─────────────────────────────┼────────────────────────────────────────────────────────────────────┤
│ Catalog/Core.lean (10)      │ Catalog.Candidate, core, includedConfirmed,                        │
│                             │ includedConfirmed_trigger_late, not_candidate_of_family,           │
│                             │ prefixOrder, safeConfirmed, safeOf, safeStable, sleepy             │
├─────────────────────────────┼────────────────────────────────────────────────────────────────────┤
│ Catalog/Meaning.lean (8)    │ Catalog.includedConfirmed_holds_iff,                               │
│                             │ includedConfirmed_inhabited_iff, prefixOrder_holds_iff,            │
│                             │ prefixOrder_inhabited_iff, safeConfirmed_holds_iff,                │
│                             │ safeConfirmed_inhabited_iff, safeStable_holds_iff,                 │
│                             │ safeStable_inhabited_iff                                           │
├─────────────────────────────┼────────────────────────────────────────────────────────────────────┤
│ Catalog/Mono.lean (8)       │ Catalog.fastOutageRegime_mono, includedFrom_mono,                  │
│                             │ outageRegime_mono, recoveredAt_mono, recoveryRegime_mono,          │
│                             │ recurrence_mono, safeFrom_mono, stableSleepyRegime_mono            │
├─────────────────────────────┼────────────────────────────────────────────────────────────────────┤
│ Catalog/Profiles.lean (10)  │ Catalog.ac43, ac43_iff, ac43_valid_cross, fastOutageRegime_iff,    │
│                             │ outageRegime_iff, recoveredAt_iff, recoveryRegime_iff,             │
│                             │ stableSleepyRegime_iff, strong1, strong1_iff                       │
├─────────────────────────────┼────────────────────────────────────────────────────────────────────┤
│ Catalog/Relations.lean (1)  │ Catalog.core_holdsAt_of_ac43                                       │
├─────────────────────────────┼────────────────────────────────────────────────────────────────────┤
│ Catalog/Standard.lean (18)  │ Catalog.includedStable, includedStable_transport,                  │
│                             │ includedStable_trigger_late, includedStableFast,                   │
│                             │ includedStableFast_transport, includedStableFast_trigger_late,     │
│                             │ persistOutage, persistOutage_no_witness_at_zero_budget,            │
│                             │ persistOutage_transport, persistOutage_trigger_late,               │
│                             │ persistOutageFast, persistOutageFast_no_witness_at_zero_budget,    │
│                             │ persistOutageFast_transport, persistOutageFast_trigger_late,       │
│                             │ persistTrigger, recovered, recovered_transport,                    │
│                             │ recovered_trigger_late                                             │
├─────────────────────────────┼────────────────────────────────────────────────────────────────────┤
│ Catalog/Strong.lean (14)    │ Catalog.strongIncluded, strongIncluded_transport,                  │
│                             │ strongIncluded_trigger_late, strongIncludedTrigger, strongPersist, │
│                             │ strongPersist_transport, strongPersist_trigger_late,               │
│                             │ strongRecoveredIncluded, strongRecoveredIncluded_transport,        │
│                             │ strongRecoveredIncluded_trigger_late, strongRecoveredSafe,         │
│                             │ strongRecoveredSafe_transport, strongSafe, strongSafe_transport    │
└─────────────────────────────┴────────────────────────────────────────────────────────────────────┘
```

Counts: 13 + 7 + 2 + 10 + 8 + 8 + 10 + 1 + 18 + 14 = 91.

```text
┌────────────────────────────────────┬────────────────────────────────────────────────────────────────────┐
│ Step                               │ Result                                                             │
├────────────────────────────────────┼────────────────────────────────────────────────────────────────────┤
│ Task 2: CatalogLock --check        │ exit 1; exactly the 91 CHANGED names; 0 REMOVED                    │
│                                    │ (`claude-files/i9/lock-task2.out`). No `--write`.                  │
├────────────────────────────────────┼────────────────────────────────────────────────────────────────────┤
│ Task 11: CatalogLock --check       │ exit 1; 91 CHANGED, 0 ADDED, 0 REMOVED; set equal to the tsv (0    │
│                                    │ extra, 0 missing). The 91 new hashes are equal to those of Task 2. │
├────────────────────────────────────┼────────────────────────────────────────────────────────────────────┤
│ Task 11: git diff main --          │ empty; no binder repairs were necessary.                           │
│ AvailableChainFramework/           │                                                                    │
├────────────────────────────────────┼────────────────────────────────────────────────────────────────────┤
│ Task 11: CatalogLock --write       │ exit 0; 250 lines, 91 changed. Old lock blob 6a4d148…; new lock    │
│ --allow-changes                    │ blob ea01491…                                                      │
├────────────────────────────────────┼────────────────────────────────────────────────────────────────────┤
│ Task 11: CatalogLock --check after │ exit 0, no output.                                                 │
│ the write                          │                                                                    │
├────────────────────────────────────┼────────────────────────────────────────────────────────────────────┤
│ Lock commit                        │ 9b5892b "I9: lock break (91 names); full checks".                  │
│                                    │ `FRAMEWORK-DESIGN.md` §8 lock change log has the entry             │
│                                    │ "2026-09-29, I9 Task 11".                                          │
└────────────────────────────────────┴────────────────────────────────────────────────────────────────────┘
```

Changed definitions in the closures. A scratch script, with the `ownHash`
and `deps` rules of `CatalogLock.lean`, printed the own hash of every
constant in the union of the closures of the 91 names, on this tree and on
main (`f0f656e`). The union has 1,048 constants on main and 1,061 on I9.

- Own hash changed (16), all in `AvailableChainModel.Objects.Blocks`: the
  constructor `Block.node`, `Block.root`, and the generated helpers of
  `Block` (`rec`, `casesOn`, `below`, `brecOn.go`, the `preceq`, `slot`
  and `DecidableEq` matchers and proofs).
- New in the closures (20): `Block.root._f`, `nodeRoot`; the codec
  (`epair`, `lpair`, `bitLen`, `bitLenDouble`, `bitLenSearch` and their
  helpers); `BlockId.value` (an old projection that did not change); the
  core `ShiftRight` and `HShiftRight` instances (Init, not project code).
- Gone from the closures (7): the `BlockId` recursors and
  `instDecidableEqBlockId` with its helpers, because the derived
  `DecidableEq Block` no longer compares a stored `BlockId`.

No constant of `AvailableChainStatements` or `AvailableChainFramework`
changed its own hash. So the only changed or new project definitions that
the CHANGED lines reach are `Block`, `Block.root`, `nodeRoot` and the codec
(plan Task 11 Step 2 stop rule).

## 5. Statement changes

The plan's rule (Global Constraints, "Statements"): a statement may change
only by (a) a replacement of the old root field, the old root formula or a
numeric root value; (b) an added `[RowCodec V]` binder (D10); (c) a change in
the named exception table. The table has one added row: the deletion of
private helpers that served only a removed root proof (I9-A01, §5.10).

Astra's branch audit of Tasks 0–8 found 18 kept theorems with a direct
statement-text change and seven deleted theorems, and 141 KitFG theorems that
gain `[RowCodec V]` (132 of them class (b) only). Task 9 adds the FG-SA
changes below. Astra's final review (F1) found two deletions outside (a),
(b) and (c): `fg_ba` and `fg_bb` (§5.9). They are restored with their old
text. No other change falls outside (a), (b) and (c).

Declarations with a `def`, `structure` or `inductive` body are included where
their signature or body changed as part of the plan.

### 5.1 Model (`AvailableChainModel`)

```text
┌────────────────────────────────────┬──────────────────────────────────┬────────────────────────────────────┐
│ Declaration (class)                │ Old text                         │ New text                           │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ Block.node (Objects/Blocks.lean)   │ | node (parent : Block) (slot :  │ | node (parent : Block) (slot :    │
│ Class (a)                          │ Slot) (root : BlockId)           │ Slot) (body : Nat)                 │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ Block.root                         │ | .genesis => genesisRoot        │ | .genesis => genesisRoot          │
│ Class (a)                          │ | .node _ _ r => r               │ | .node p s x => nodeRoot p.root s │
│                                    │                                  │ x                                  │
└────────────────────────────────────┴──────────────────────────────────┴────────────────────────────────────┘
```

New: `nodeRoot`, `Block.body`, `Block.root_ne_genesis_of_node`,
`Block.root_injective`, `parent_mem_iff_root`, `parent_mem_and_iff_root`, and
the codec module `Objects/Codec.lean` (`bitLen`, `tz`, `lpair`, `epair`,
`efst`, `esnd`, `encList`, `encOption`, `encBool` and their laws).

### 5.2 Statements, Kit, EngineV2, Framework

No statement text changed.

- `AvailableChainStatements/Generic/Conditions.lean`: the docstring of
  `RootInjective` only. Old: "Collision resistance of block roots, idealized
  as injectivity on genesis and the ancestors of all blocks named by this run.
  …". New: "Injectivity of block roots on genesis and the ancestors of all
  blocks named by this run. … this condition is a theorem for every run:
  `rootInjective_all` in `AvailableChainKit/Roots.lean` proves it."
- `AvailableChainKit`: new `rootInjective_all` (`Roots.lean`). In
  `Core.lean`, `block_preceq_trans` renames a case binder `r` to `x`; the
  statement is byte-identical. `healthyPrefix_rootInjective` keeps its text
  and proof.
- `AvailableChainEngineV2/Sketch.lean`: the two toy folds at `:95` and `:104`
  pass the body `k` instead of the root literal `⟨k + 1⟩`. These are toy
  definitions with no theorem statement.
- `AvailableChainFramework`: no change.

### 5.3 Grid CO and SA

```text
┌────────────────────────────────────┬──────────────────────────────────┬────────────────────────────────────┐
│ Declaration (class)                │ Old text                         │ New text                           │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ GridCO.honest_proposal_views       │ 0 < s ∧ B = .node parent s ⟨s *  │ 0 < s ∧ B = .node parent s 0 ∧     │
│ (Proofs/Proposals.lean:65)         │ (parent.root.value + 1)⟩ ∧       │                                    │
│ Class (c)                          │                                  │                                    │
└────────────────────────────────────┴──────────────────────────────────┴────────────────────────────────────┘
```

`Proposals.lean:223` is a proof term inside `honest_proposal_exists`; that
statement does not change. The model definition `propose`
(`Model/Protocol.lean:292`) changes its body from the old root formula to
`Block.node parent s 0` (class (a), D5). New: `blockKnown_parent_slot_iff_root`,
`admitProposal_missingParent` (`Proofs/Handling.lean`),
`rootInjectiveBelow_all` (`Proofs/Roots.lean`). SA: no statement change.

### 5.4 SA-PC

```text
┌────────────────────────────────────┬──────────────────────────────────┬────────────────────────────────────┐
│ Declaration (class)                │ Old text                         │ New text                           │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ SAPC.honest_proposal_views         │ 0 < s ∧ b = .node parent s ⟨s *  │ 0 < s ∧ b = .node parent s 0 ∧     │
│ (Proofs/Proposals.lean:55)         │ (parent.root.value + 1)⟩ ∧       │                                    │
│ Class (c)                          │                                  │                                    │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ delivered_blocks, emitted_blocks,  │ private helper theorems of the   │ deleted; `rootInjective` in        │
│ named_block, roots (private        │ old `roots` field proof          │ `sleepy` is                        │
│ theorems in SAPC/Tests/            │                                  │ `Framework.Kit.rootInjective_all   │
│ CleanInvariantCounterexample.lean) │                                  │ env _ run`                         │
│ Class (c), I9-A01 row              │                                  │                                    │
└────────────────────────────────────┴──────────────────────────────────┴────────────────────────────────────┘
```

`Proposals.lean:106` is a proof term inside `honest_proposal_exists`. The
model definition `propose` (`Model/Choice.lean:87`) uses body `0`. New:
`blockKnown_parent_slot_iff_root`, `proposalEnters_missingParent`,
`admitProposal_missingParent` (`Proofs/BaseViews.lean`),
`process_pc_missingPaths` (`Proofs/CertificateValidity.lean`),
`y_root_lt_x_root` (`Tests/CleanInvariantCounterexample.lean`).

### 5.5 L*

No statement change. `propose` (`Model/Protocol.lean:258`) uses body `0`. The
stored-block exclusion facts (`excludes_stable`, `excludes_proposal_iff` and
the others of r203-followups item 1) build with no proof edit. New:
`blockKnown_parent_slot_iff_root`, `admitProposal_missingParent`
(`Proofs/Hooks.lean`).

### 5.6 Witnesses and Registry

```text
┌────────────────────────────────────┬──────────────────────────────────┬────────────────────────────────────┐
│ Declaration (class)                │ Old text                         │ New text                           │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ Regimes.recoveryProposalEmitted    │ HonestProposalAt fullEnv         │ HonestProposalAt fullEnv interface │
│ (Witnesses/Regimes.lean)           │ interface witnessRun 2 (.node    │ witnessRun 2 (.node .genesis 2 0)  │
│ Class (a)                          │ .genesis 2 ⟨1⟩)                  │                                    │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ Sanity.emitted_proposed, private   │ private helper of the old        │ deleted; `exampleRootInjective` is │
│ (Witnesses/Sanity.lean)            │ `exampleRootInjective` proof     │ proved by `Block.root_injective`   │
│ Class (c), I9-A01 row              │                                  │                                    │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ Counter.chain_root                 │ theorem chain_root (m : Nat) :   │ removed (false after I9); replaced │
│ (Registry/CounterRun.lean:287)     │ (chain m).root = ⟨m⟩             │ by `theorem chain_depth : ∀ m :    │
│ Class (a)                          │                                  │ Nat, (chain m).depth = m` and      │
│                                    │                                  │ `theorem chain_injective {i j :    │
│                                    │                                  │ Nat} (h : chain i = chain j) : i = │
│                                    │                                  │ j`                                 │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ Counter.preceq_node                │ (s : Slot) (r : BlockId) (h :    │ (s : Slot) (x : Nat) (h :          │
│ (Registry/CounterRun.lean)         │ Block.Preceq B p) : Block.Preceq │ Block.Preceq B p) : Block.Preceq B │
│ Class (a)                          │ B (.node p s r)                  │ (.node p s x)                      │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ NoInput.clockBlock_root            │ theorem clockBlock_root (m :     │ removed (false after I9); replaced │
│ (Registry/Gaps/NoInput.lean:191)   │ Nat) : (clockBlock m).root = ⟨m⟩ │ by `theorem clockBlock_depth : ∀ m │
│ Class (a)                          │                                  │ : Nat, (clockBlock m).depth = m`   │
│                                    │                                  │ and `theorem clockBlock_injective  │
│                                    │                                  │ {i j : Nat} (h : clockBlock i =    │
│                                    │                                  │ clockBlock j) : i = j`             │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ NoInput.preceq_node                │ (s : Slot) (r : BlockId) …       │ (s : Slot) (x : Nat) … (.node p s  │
│ (Registry/Gaps/NoInput.lean)       │ (.node p s r)                    │ x)                                 │
│ Class (a)                          │                                  │                                    │
└────────────────────────────────────┴──────────────────────────────────┴────────────────────────────────────┘
```

These keep their text; only the proof changes: `exampleRootInjective`,
`Witnesses.Regimes.rootInjective` (by `Block.root_injective`),
`counter_rootInjective`, `clock_rootInjective` (by `rootInjective_all`).
`REGISTRY.md` and `MATRIX.md` did not change.

### 5.7 SimplexFG

SimplexFG had no `theorem` at the Task 7 base. The changes are in the
constructor, in definition signatures and in examples.

```text
┌────────────────────────────────────┬──────────────────────────────────┬────────────────────────────────────┐
│ Declaration (class)                │ Old text                         │ New text                           │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ FGBlock.node (Objects.lean)        │ | node (parent : FGBlock V)      │ | node (parent : FGBlock V) (slot  │
│ Class (a)                          │ (slot : Slot) (root : BlockId)   │ : Slot) (body : Nat) (rows : List  │
│                                    │ (rows : List (Row V))            │ (Row V))                           │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ FGBlock.root                       │ | .node _ _ r _ => r             │ under `[RowCodec V]`: | .node p s  │
│ Class (a), (b)                     │                                  │ x rs => nodeRoot p.root s          │
│                                    │                                  │ (encFGBody x rs)                   │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ process_row, transition, derive    │ no `[RowCodec V]`                │ gain `[RowCodec V]` through the    │
│ (ChainState); hOf, frontier,       │                                  │ section `variable`; body text      │
│ ViewRootInj, lexKey, lexMax,       │                                  │ unchanged                          │
│ fjControls, filteredFrom, fjFrame  │                                  │                                    │
│ (Frame); acceptViable,             │                                  │                                    │
│ update_finality, on_block,         │                                  │                                    │
│ storeControls, storeFrame (Store); │                                  │                                    │
│ createRow, clientRun (Client)      │                                  │                                    │
│ Class (b)                          │                                  │                                    │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ HeadFields.ofBlock (Client)        │ {V : Type} [DecidableEq V]       │ the explicit binder list gains     │
│ Class (b)                          │ [Fintype V] (E : Electorate V) … │ `[RowCodec V]`                     │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ Collision example                  │ (fjFrame E4 cfg1 .genesis        │ (…).j = 2 ∧ (…).J = B1c; with      │
│ (Frame.lean:176–200 at the base)   │ {.genesis, B1a, B1c, childA,     │ `B1a.root ≠ B1c.root` from         │
│ Class (c)                          │ childC}).j = 0 ∧ (…).J =         │ `FGBlock.root_injective`           │
│                                    │ .genesis                         │                                    │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ ChainState inline block example    │ root `⟨1⟩`                       │ body `0`                           │
│ Class (a)                          │                                  │                                    │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ Client `clientRun` examples        │ `⟨1⟩`, `⟨2⟩`, head fields `⟨2,   │ `B1.root`, `clientB1alt.root`,     │
│ Class (a)                          │ ⟨1⟩, 0⟩`                         │ `⟨2, B1.root, 0⟩`                  │
└────────────────────────────────────┴──────────────────────────────────┴────────────────────────────────────┘
```

New: `RowCodec`, the `Fin n` instance, `encHeightPair`, `encFinalityPair`,
`encRow`, `fgBodyTag`, `encFGBody` and their injectivity lemmas
(`encFGBody_inj`), `FGBlock.body`, `FGBlock.root_ne_genesis_of_node`,
`FGBlock.root_injective`.

### 5.8 KitFG

Class (a): 11 theorems. The binder of the node's third argument changes from
`r : BlockId` to `x : Nat`, and `.node p s r rs` becomes `.node p s x rs` in
the statement. The binder keeps its position and its kind (explicit or
implicit). Example (Certificates):

```text
old: theorem preceq_node_of_preceq {A p : FGBlock V} (s : Slot) (r : BlockId) (rs : List (Row V))
         (h : FGBlock.Preceq A p) : FGBlock.Preceq A (.node p s r rs)
new: theorem preceq_node_of_preceq {A p : FGBlock V} (s : Slot) (x : Nat) (rs : List (Row V))
         (h : FGBlock.Preceq A p) : FGBlock.Preceq A (.node p s x rs)
```

```text
┌──────────────────────────────────────────────┬──────────────────────────────┬──────────┐
│ Theorem                                      │ Binder change                │ Also (b) │
├──────────────────────────────────────────────┼──────────────────────────────┼──────────┤
│ Certificates.preceq_node_of_preceq           │ (r : BlockId) → (x : Nat)    │ no       │
│ Certificates.preceq_parent_node              │ (r : BlockId) → (x : Nat)    │ no       │
│ Certificates.preceq_parent_of_preceq_node    │ {r : BlockId} → {x : Nat}    │ no       │
│ Certificates.onChain_parent                  │ (r : BlockId) → (x : Nat)    │ no       │
│ Certificates.derive_node                     │ (r : BlockId) → (x : Nat)    │ yes      │
│ Certificates.derive_node_height_entry_cases  │ (r : BlockId) → (x : Nat)    │ yes      │
│ Certificates.derive_node_height_cases        │ (r : BlockId) → (x : Nat)    │ yes      │
│ Certificates.node_entry_eq_of_height_eq      │ (r : BlockId) → (x : Nat)    │ yes      │
│ Certificates.folded_witnesses                │ (r : BlockId) → (x : Nat)    │ yes      │
│ Certificates.crossing_matching_quorum        │ (r : BlockId) → (x : Nat)    │ yes      │
│ CrossingNoFinal.crossing_maturity            │ (r : BlockId) → (x : Nat)    │ yes      │
└──────────────────────────────────────────────┴──────────────────────────────┴──────────┘
```

Class (b) with an explicit binder: `RootInjectiveOn` (def) and
`RootInjectiveOn.symm` gain `[RowCodec V]` before their other binders;
`chainOrder_foldRows` gains `[RowCodec V]` as its first binder.

Class (b) only, through section `variable` lines: every other KitFG
declaration that reads `derive`, `process_row`, `foldRows`, roots or the
frame. Old text: no `[RowCodec V]`; new text: `[RowCodec V]` is an instance
argument; no other text changes. The list has the 132 theorems of Astra's
audit (from the compiled types) and the definitions, structures and fields of
the Task 8 report §2:

- Accountable: `accountable`, `accountable_oriented`, `finalLock`,
  `finalLock_e1`, `justification_certificate_rows`, `uniqueJust_chains`.
- CausalCap: `causalCap`, `causalCap_notRoot`.
- Certificates: `foldRows` (def), `RowWitnesses` (structure) and its fields
  `target_sub`, `target`, `progress`, `finalize`; `F_eq_J_of_heights`,
  `J_is_entry`, `chainOrder_derive`, `derive_F_preceq_J`, `derive_L`, `derive_anchors_preceq`,
  `derive_witnesses`, `entry_eq_of_preceq`, `entry_eq_on_plateau`,
  `entry_first`, `entry_height`, `entry_idem`, `entry_parent_height`,
  `entry_preceq`, `entry_same_height`, `finality_certificate`,
  `finalized_below_height`, `finalized_zero_is_genesis`, `foldRows_fields`,
  `foldRows_s`, `foldl_process_row_fields`, `foldl_process_row_s`, `h_mono`,
  `height_crossing`, `heights_ordered`, `justification_certificate`,
  `justified_below_height`, `justified_zero_is_genesis`, `one_le_h`,
  `process_row_fields`, `process_row_finalize`, `process_row_progress`,
  `process_row_target`, `witnesses_advance`, `witnesses_congr`,
  `witnesses_empty`, `witnesses_fold`, `witnesses_foldRows`,
  `witnesses_height_events`, `witnesses_mono`, `witnesses_process`.
- ClientSafety: `clientRun_covers`, `clientRun_noSlash`, `createRow_eq`,
  `createRow_noSelfSlash`, `recordInv_createRow`.
- Correspondence: `StoreInv` (structure) and its fields `closed`, `gen`,
  `Fmem`, `hmax`, `pair`, `FJ`, `Fcar`; `exists_frontier`,
  `filteredFrom_Z_mem`, `filteredFrom_reachesLo`, `filteredFrom_viable_child`,
  `fjControls_J_preceq_of_rootIsJ`, `fjFrame_D`, `fjFrame_D_nonempty`,
  `fjFrame_Z_mem_D`, `fjFrame_lo`, `frameViable_eq_accept_cut`,
  `frameViable_eq_accept_of_noContest`, `frameViable_subset_accept`,
  `frontier_insert`, `frontier_mono`, `fst_le_of_lexKey_le`, `hOf_eq`,
  `le_frontier`, `lexKey_fallback_le`, `lexMax_eq_of_greatest`,
  `lexMax_insert`, `lexMax_mono`, `lexMax_of_advance`, `lexMax_of_candidate`,
  `lexMax_of_none`, `lexMax_spec`, `mem_filteredFrom`, `on_block_F_mono`,
  `on_block_TF_subset`, `on_block_of_accepted`, `on_block_of_refused`,
  `pair_eq_of_lexKey_eq`, `storeControls_eq_fjControls`,
  `storeFrame_feasible`, `storeFrame_full`, `storeInv_accept`,
  `storeInv_init`, `storeInv_on_block`, `update_finality_F_cases`,
  `update_finality_F_mono`, `update_finality_TF`, `update_finality_h_max`,
  `update_finality_pair`, `viewRootInj_mono`.
- CrossingNoFinal: `crossingNeedsTimeout`, `crossingNoFinal`,
  `crossingNoFinal_QC`, `crossing_other_entry`.
- InBandLock: `finalityPair_carrier_above`, `inBandLock`.
- Provenance: `provenance_entry`, `provenance_finality`,
  `provenance_finalityQC`, `provenance_finalityRow`.
- TwoChanges: `EC`, `EJ`, `nFrame`, `phaseOf` (defs); `Fmove_atFrontier`,
  `Fmove_atTop`, `Fmove_below`, `Fmove_filtered`, `effFrame_of_bits`,
  `evidence_mono`, `filteredFrom_congr`, `filteredFrom_move`,
  `fjControls_contest`, `gap_of_ne`, `lexMax_carrier_of_top`,
  `lexMax_fst_lt`, `lexMax_top_of_carrier`, `nFrame_eq`,
  `nFrame_eq_phaseFrame`, `one_le_frontier`, `phaseOf_eq`, `rootIsJ_iff`,
  `top_J_extends`, `top_contest`, `top_contested`, `top_uncontested`,
  `twoChanges`, `twoChanges_count`, `twoChanges_nested`.

The six theorems of the exception table (`RootInjectiveOn.symm`,
`uniqueJust_chains`, `finalLock`, `accountable`, `causalCap`,
`causalCap_notRoot`) are in this list. No premise was added or removed: every
theorem that takes `hroot : RootInjectiveOn …` or `hinj : ViewRootInj …` keeps
it. New: `rootInjectiveOn_all` (`Accountable.lean`), `viewRootInj_all`
(`Correspondence.lean`).

`Pins.lean`: the source pins, the ids and the manifest did not change. The
annotation texts changed: the module docstring has a new paragraph "Root
injectivity", the `fj.frame.v1` FJ_FRAME row text changed, and each other
`leanHyp` string that names `ViewRootInj` or `RootInjectiveOn` adds
`(viewRootInj_all)` or `(rootInjectiveOn_all)`. The coverage kind stays
`leanHyp`.

### 5.9 FG-SA

```text
┌────────────────────────────────────┬──────────────────────────────────┬────────────────────────────────────┐
│ Declaration (class)                │ Old text                         │ New text                           │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ eraseFG (Model/Objects.lean)       │ def eraseFG {V : Type} : FGBlock │ def eraseFG {V : Type} [RowCodec   │
│ Class (a), (b)                     │ V → Block … | .node p s r _ =>   │ V] : … | .node p s x rs => .node   │
│                                    │ .node (eraseFG p) s r            │ (eraseFG p) s (encFGBody x rs)     │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ fgBlock (Model/Handlers.lean)      │ .node P b.slot b.root            │ .node P b.slot (packInner (appOf   │
│ Class (a)                          │ (rows.filterMap RowWire.toRow?)  │ b.body) rows) (rows.filterMap      │
│                                    │                                  │ RowWire.toRow?)                    │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ blockAccepted, wellFormed          │ … | none => false)               │ … | none => false) && rowsOk b     │
│ (Model/Handlers.lean)              │                                  │ rows (last conjunct in both)       │
│ Class D9 (Task 9 Step 2)           │                                  │                                    │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ propose (Model/Frame.lean)         │ some (.proposal (.node H s ⟨s *  │ let rows := proposalRows p st H;   │
│ Class (a), D5                      │ (H.root.value + 1)⟩) …           │ some (.proposal (.node H s         │
│                                    │ (proposalRows p st H))           │ (packBody 0 rows)) … rows)         │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ eraseFG_fgBlock                    │ (hb : b ≠ .genesis) (hP :        │ (hb : b ≠ .genesis) (hP : eraseFG  │
│ (Proofs/Admission.lean)            │ eraseFG P = b.parent) (rows :    │ P = b.parent) (rows : List         │
│ Class (c)                          │ List (RowWire n)) : eraseFG      │ (RowWire n)) (hrows : rowsOk b     │
│                                    │ (fgBlock P b rows) = b           │ rows = true) : eraseFG (fgBlock P  │
│                                    │                                  │ b rows) = b                        │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ fgBlock_root                       │ (P : FGBlock (Fin n)) (b :       │ (P …) (b …) (rows …) (hb : b ≠     │
│ Class (c)                          │ Block) (rows : List (RowWire n)) │ .genesis) (hP : eraseFG P =        │
│                                    │ : (fgBlock P b rows).root =      │ b.parent) (hrows : rowsOk b rows = │
│                                    │ b.root := rfl                    │ true) : (fgBlock P b rows).root =  │
│                                    │                                  │ b.root                             │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ fgBlock_notMem                     │ (st) (P) (b) (rows : List        │ (st) (P) (b) (rows) (hb : b ≠      │
│ Class (c)                          │ (RowWire n)) (hfresh : ¬ ∃ Y ∈   │ .genesis) (hP : eraseFG P =        │
│                                    │ st.fg.TF, Y.root = b.root) :     │ b.parent) (hrows : rowsOk b rows = │
│                                    │ fgBlock P b rows ∉ st.fg.TF      │ true) (hfresh : …) : …             │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ metaInv_accepted                   │ … (hdec : ∀ a ∈ rows,            │ … (hdec : ∀ a ∈ rows,              │
│ (Proofs/Metadata.lean:340)         │ (RowWire.decode? a).isSome) :    │ (RowWire.decode? a).isSome) (hrows │
│ Class (c)                          │ MetaInv p X                      │ : rowsOk b rows = true) : MetaInv  │
│                                    │                                  │ p X; `metaInv_process` passes      │
│                                    │                                  │ `blockAccepted_rowsOk hacc`        │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ MetaInv.wireTree                   │ o = ⟨.proposer s, .proposal b    │ o = ⟨.proposer s, .proposal b raw  │
│ (Statements/Invariants.lean)       │ raw sup rows⟩ ∧ (∀ a ∈ rows,     │ sup rows⟩ ∧ rowsOk b rows = true ∧ │
│ Class (c)                          │ (RowWire.decode? a).isSome) ∧ ∃  │ (∀ a ∈ rows, (RowWire.decode?      │
│                                    │ B ∈ st.fg.TF, …                  │ a).isSome) ∧ ∃ B ∈ st.fg.TF, …     │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ Carrier, 12 theorems:              │ variable {V : Type} [DecidableEq │ variable {V : Type} [DecidableEq   │
│ eraseFG_slot, eraseFG_root,        │ V]                               │ V] [RowCodec V]                    │
│ eraseFG_parent,                    │                                  │                                    │
│ eraseFG_eq_genesis,                │                                  │                                    │
│ eraseFG_preceq,                    │                                  │                                    │
│ eraseFG_compatible, eraseFG_injOn, │                                  │                                    │
│ preceq_of_eraseFG_preceq,          │                                  │                                    │
│ compatible_iff_eraseFG,            │                                  │                                    │
│ viewRootInj_of_rootInj,            │                                  │                                    │
│ rootInjectiveOn_of_viewRootInj,    │                                  │                                    │
│ erase_rootInjective                │                                  │                                    │
│ Class (b)                          │                                  │                                    │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ not_contentAgree                   │ theorem not_contentAgree : ¬     │ deleted; replaced by `theorem      │
│ (Tests/RootCollision.lean)         │ ContentAgree stX stY             │ contentAgree_stX_stY :             │
│ Class (c)                          │                                  │ ContentAgree stX stY`              │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ negated cross-store example        │ example : ¬ (∀ {B₁ B₂ : FGBlock  │ example : ∀ {B₁ B₂ : FGBlock (Fin  │
│ (RootCollision)                    │ (Fin 4)}, B₁ ∈ stX.fg.TF → B₂ ∈  │ 4)}, B₁ ∈ stX.fg.TF → B₂ ∈         │
│ Class (c)                          │ stY.fg.TF →                      │ stY.fg.TF → KitFG.RootInjectiveOn  │
│                                    │ KitFG.RootInjectiveOn B₁ B₂)     │ B₁ B₂                              │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ fg_ba, fg_bb (RootCollision)       │ theorem fg_ba : ∃ X ∈ stX.fg.TF, │ deleted in Task 9, restored after  │
│ No class (restored)                │ eraseFG X = ba; theorem fg_bb :  │ the final review (Astra F1) with   │
│                                    │ ∃ Y ∈ stY.fg.TF, eraseFG Y = bb  │ the old text; no net statement     │
│                                    │                                  │ change                             │
├────────────────────────────────────┼──────────────────────────────────┼────────────────────────────────────┤
│ ba, c1, bb (RootCollision)         │ .node .genesis 4 ⟨4⟩; .node      │ pb .genesis 4 0 []; pb .genesis 1  │
│ Class (a)                          │ .genesis 1 ⟨1⟩; .node c1 2 ⟨4⟩   │ 0 []; pb c1 2 0 []                 │
└────────────────────────────────────┴──────────────────────────────────┴────────────────────────────────────┘
```

Kept text, proofs adapted: `parentFG_spec`, `rootTest_iff_blockTest` (its
`hinj` premise is now provable, but it stays), `blockAccepted_of_wellFormed`,
`blockAccepted_facts`, `accepted_base_facts`, `fg_on_block_accepts`,
`admitBlock_sufficient`, `admitBlock_sufficient_absent`,
`admitBlock_accepted_eq`, `admitProposal_base_view`, `actView_admitBlock_sameF`,
`actView_admitBlock_movedF`, `contentAgree_self`,
`fg_eq_of_eraseFG_eq_across`, the `Fields`, `Nesting`, `Reconcile`,
`ActView` and `StoreInv` statements, and the cross-node theorems. The
cross-node theorems keep their `ContentAgree` premise, which is now redundant.

New (Task 9 and 731b4c5): `encLabel`, `encAuth`, `encRowBody`, `encRowWire`,
`packInner`, `packBody`, `appOf`, `rowsOk` (Model); `eraseFG_injective`,
`encLabel_inj`, `encAuth_inj`, `encRowBody_inj`, `encRowWire_inj`,
`appOf_packBody`, `packInner_inj`, `packBody_inj`, `rowsOk_iff`,
`rowsOk_node_packBody`, `rows_eq_of_rowsOk` (Carrier);
`parentFG_isSome_iff_root`, `admitBlock_missingParent`,
`blockAccepted_rowsOk` (Admission); `contentAgree`, `contentAgree_reachable`
(CrossNode); `rootInj_all` (StoreInv); `admitWith`, `process_eq_admitWith`
(`Tests/Support.lean`); `ba_root_ne_bb_root`, `contentAgree_stX_stY`
(RootCollision).

### 5.10 Named exception I9-A01: deleted private helpers

Astra's pre-final audit (prompt `docs/audit/i9-branch-audit-0-8.md`, report
`docs/audit/i9-branch-audit-0-8-report.md`) found one major finding,
I9-A01: Tasks 4 and 6 deleted five private helper theorems, and the r4
statement rule had no exception for them. The helpers served only the
removed root proofs of kept statements.

```text
┌────────────────────────┬──────────────────────────────────────────┬────────────────────────────┐
│ Helper                 │ File (at a5aaf3c)                        │ Kept statement now         │
├────────────────────────┼──────────────────────────────────────────┼────────────────────────────┤
│ delivered_blocks,      │ AvailableChainSAPC/Tests/                │ `rootInjective` of         │
│ emitted_blocks,        │ CleanInvariantCounterexample.lean        │ `sleepy`, by               │
│ named_block, roots     │                                          │ `rootInjective_all`        │
│ (all private)          │                                          │                            │
├────────────────────────┼──────────────────────────────────────────┼────────────────────────────┤
│ emitted_proposed       │ AvailableChainWitnesses/Sanity.lean      │ `exampleRootInjective`, by │
│ (private)              │                                          │ `Block.root_injective`     │
└────────────────────────┴──────────────────────────────────────────┴────────────────────────────┘
```

Disposition: the controller ruled for a named exception, not a restore
(commit `6ebbb26`). The plan's exception table has the row "Deleted private
helpers (5 names)", and the note under the table gives the names, the rule
and the audit path. Astra found no soundness defect. The reasons and the
cost are in §7, decision 4.

## 6. Fixtures whose intent changed

The plan rule: a fixture keeps its intent and its cause; a fixture that
asserted a root collision becomes a positive injectivity or duplicate test.
Most recoded fixtures keep their intent (task reports, fixture tables). This
section lists the fixtures whose intent, cause or strength changed, and the
root orders that the fixtures now prove.

### 6.1 Changed intent or cause

```text
┌──────────────────────────────────┬────────────────────────────────────┬────────────────────────────────────────┐
│ Fixture                          │ Old intent                         │ New intent                             │
├──────────────────────────────────┼────────────────────────────────────┼────────────────────────────────────────┤
│ SimplexFG `Frame.lean` collision │ `B1c` has the same root `⟨1⟩` as   │ The collision cannot occur. `B1a.root  │
│ view `{genesis, B1a, B1c,        │ `B1a`; `pickPair` returns `none`,  │ ≠ B1c.root` from                       │
│ childA, childC}` (named          │ and the frame falls back to `(0,   │ `FGBlock.root_injective`;              │
│ exception)                       │ genesis)`; `ViewRootInj` fails on  │ `ViewRootInj` holds on the view;       │
│                                  │ the view                           │ `B1a.root.value < B1c.root.value`; the │
│                                  │                                    │ frame selects `j = 2 ∧ J = B1c`. No    │
│                                  │                                    │ empty-candidate fallback test is added │
├──────────────────────────────────┼────────────────────────────────────┼────────────────────────────────────────┤
│ FG-SA `Tests/RootCollision.lean` │ Negative example: honest `ba` and  │ Positive tests: `ba_root_ne_bb_root`,  │
│ (named exception)                │ `bb` share root 4.                 │ `contentAgree_stX_stY`, duplicate      │
│                                  │ `not_contentAgree`; the conclusion │ refusal and the wrong-row-list         │
│                                  │ of `rootInjectiveOn_across` is     │ refusals. The full list is in §5.9 and │
│                                  │ false; a reader that holds `ba`    │ in `FGSA-STORE-REPORT.md` §7           │
│                                  │ accepts `c1` and refuses `bb`      │                                        │
├──────────────────────────────────┼────────────────────────────────────┼────────────────────────────────────────┤
│ FG-SA Smoke DQ2 case (old        │ A distinct block with the same     │ The declared duplicate test `wDup =    │
│ `:208–210`)                      │ root is refused                    │ wProp B3 1 [v2]`: the stored slot-3    │
│                                  │                                    │ block of `B3` with its rows and the    │
│                                  │                                    │ carried label-2 vote `v2`;             │
│                                  │                                    │ `wellFormed` true; refused; votes      │
│                                  │                                    │ unchanged. Direct delivery admits `v2` │
│                                  │                                    │ at `stA`, so the carried-vote check is │
│                                  │                                    │ not vacuous (Astra F2; before the fix, │
│                                  │                                    │ a label-1 vote that direct delivery    │
│                                  │                                    │ also refused)                          │
├──────────────────────────────────┼────────────────────────────────────┼────────────────────────────────────────┤
│ FG-SA Smoke `X` (stK contest)    │ `X` (root `⟨100⟩`) wins the root   │ Same intent, new cause: `X` has        │
│                                  │ tie against `childA` (`⟨11⟩`) in   │ application value `2 ^ 4096`. With     │
│                                  │ the wrong-controls alternative     │ value `0`, `X.root < childA.root`, and │
│                                  │                                    │ the wrong-controls alternative also    │
│                                  │                                    │ gives `childA`, so the test cannot     │
│                                  │                                    │ detect wrong controls. `childA.root <  │
│                                  │                                    │ X.root` is proved                      │
├──────────────────────────────────┼────────────────────────────────────┼────────────────────────────────────────┤
│ FG-SA Smoke `:374` `deepest`     │ A depth tie decided by the greater │ A depth tie between `.node g 1 5 []`   │
│                                  │ root                               │ and `.node g 2 9 []`; the root order   │
│                                  │                                    │ is proved before `deepest`; the slot-2 │
│                                  │                                    │ block wins                             │
├──────────────────────────────────┼────────────────────────────────────┼────────────────────────────────────────┤
│ FG-SA Smoke `yB` (old `:363`,    │ One block that carries two         │ Two blocks: `yB3 = pb (eraseFG B2) 3   │
│ `:415`, `:534`)                  │ different row lists                │ 95 [q 3]` (stP) and `yB = pb (eraseFG  │
│                                  │                                    │ B2) 3 95 [q 1]` (stB), because the     │
│                                  │                                    │ rows are now in the block identity     │
├──────────────────────────────────┼────────────────────────────────────┼────────────────────────────────────────┤
│ FG-SA refusal fixtures (`wX`,    │ Each is refused by its named check │ Same cause; each block packs its       │
│ `wFut`, `r0`/`r1` blocks, future │                                    │ carried rows, so `rowsOk` is true and  │
│ slot, slot-2 key)                │                                    │ cannot be the refusal cause (Review    │
│                                  │                                    │ Focus 5)                               │
├──────────────────────────────────┼────────────────────────────────────┼────────────────────────────────────────┤
│ SimplexFG equal-content pairs    │ Different blocks by supplied root  │ With body `0` they are the same block. │
│ (`B2 = childA`, `B1' = B1c`)     │ only                               │ No view, fold or store holds both      │
│                                  │                                    │ members of a pair. `clientB1alt = B1b` │
│                                  │                                    │ was already the same term before I9    │
├──────────────────────────────────┼────────────────────────────────────┼────────────────────────────────────────┤
│ KitFG `TwoChanges` `K3`          │ Satisfies only the decidable       │ Stronger: a new example applies        │
│                                  │ hypotheses of `Fmove_atTop`;       │ `Fmove_atTop` to `K3` with             │
│                                  │ `ViewRootInj` "not decidable here" │ `viewRootInj_all _` for `hinj`, so     │
│                                  │                                    │ every hypothesis is discharged in Lean │
├──────────────────────────────────┼────────────────────────────────────┼────────────────────────────────────────┤
│ SA Smoke `C`, `X` order          │ `C.root < X.root` (`⟨2⟩ < ⟨3⟩`)    │ `X.root < C.root` (3,800 < 21,660). No │
│                                  │                                    │ check compares them: they are not      │
│                                  │                                    │ siblings and not at equal depth        │
├──────────────────────────────────┼────────────────────────────────────┼────────────────────────────────────────┤
│ Smoke pins: Grid CO (f821a9f),   │ `#eval` lines; a false result does │ `example … := by decide` pins; a false │
│ L* (3b0a0b5)                     │ not fail the build                 │ result fails the build. Grid CO: eight │
│                                  │                                    │ pins; L*: four pins. `#guard` was      │
│                                  │                                    │ refused by the `hashCommand` linter    │
│                                  │                                    │ under `--wfail`                        │
└──────────────────────────────────┴────────────────────────────────────┴────────────────────────────────────────┘
```

### 6.2 Root orders that the fixtures now prove

Before I9 the fixture roots were literals, so the orders were literal
comparisons. Now each order that decides an outcome, or that protects one, is
a proved example.

```text
┌────────────────────────────────────────┬────────────────────────────────┬────────────────────────────────┐
│ Library, file                          │ Order                          │ Purpose                        │
├────────────────────────────────────────┼────────────────────────────────┼────────────────────────────────┤
│ Grid CO `Tests/Smoke.lean:64`          │ blockB.root < blockC.root (84  │ keeps the old sibling order    │
│                                        │ < 156)                         │ ⟨1⟩ < ⟨2⟩; no check reads it   │
├────────────────────────────────────────┼────────────────────────────────┼────────────────────────────────┤
│ SA `Tests/Smoke.lean:17`               │ B.root < X.root (84 < 3,800)   │ keeps the old sibling order    │
│                                        │                                │ ⟨1⟩ < ⟨3⟩                      │
├────────────────────────────────────────┼────────────────────────────────┼────────────────────────────────┤
│ SA-PC                                  │ y_root_lt_x_root : y.root <    │ decides the score tie: honest  │
│ `CleanInvariantCounterexample.lean:33` │ x.root (84 < 3,800)            │ nodes choose `x` because its   │
│                                        │                                │ root is larger. `x` has body 1 │
│                                        │                                │ (faulty proposer). With the    │
│                                        │                                │ order reversed,                │
│                                        │                                │ `signature_checks` and         │
│                                        │                                │ `broadcasts` fail              │
├────────────────────────────────────────┼────────────────────────────────┼────────────────────────────────┤
│ SA-PC `Tests/Smoke.lean:17–19`         │ x.root < y.root; c.root <      │ keeps the old orders; a        │
│                                        │ d.root; d.root < (Block.node x │ reversal experiment changed no │
│                                        │ 4 1).root                      │ check; `carriedDisableCheck`   │
│                                        │                                │ uses body 1 to keep `d < b`    │
├────────────────────────────────────────┼────────────────────────────────┼────────────────────────────────┤
│ SimplexFG `Frame.lean:176`             │ B1a.root.value <               │ the frame selects `J = B1b`    │
│                                        │ B1b.root.value                 │ (B1b has body 1)               │
├────────────────────────────────────────┼────────────────────────────────┼────────────────────────────────┤
│ SimplexFG `Frame.lean:216`             │ B1a.root.value <               │ the frame over the old         │
│                                        │ B1c.root.value                 │ collision view selects `J =    │
│                                        │                                │ B1c`                           │
├────────────────────────────────────────┼────────────────────────────────┼────────────────────────────────┤
│ FG-SA `Tests/Smoke.lean:460`           │ .node g 1 5 [] root < .node g  │ the `deepest` depth tie        │
│                                        │ 2 9 [] root                    │                                │
├────────────────────────────────────────┼────────────────────────────────┼────────────────────────────────┤
│ FG-SA `Tests/Smoke.lean:613`           │ childA.root < X.root ∧         │ the stK alternatives: wrong    │
│                                        │ B1a.root < B1b.root            │ controls give `X`; the         │
│                                        │                                │ full-store witness gives `Y`   │
│                                        │                                │ (B1b wins at genesis)          │
├────────────────────────────────────────┼────────────────────────────────┼────────────────────────────────┤
│ FG-SA `Tests/Smoke.lean:696`           │ b1.root < b1'.root             │ the `liveRoot` alternative     │
│                                        │                                │ over Σ.T gives `b1'`; the      │
│                                        │                                │ result is `b1`                 │
└────────────────────────────────────────┴────────────────────────────────┴────────────────────────────────┘
```

Task 7's `fgBodyTag` commit (4885a83) recomputed the SimplexFG orders; both
kept their direction. Tasks 5, 6 and 8 have no fixture whose outcome depends
on a root order (task reports and reviews).

## 7. Decisions taken without the user

The user decided D1, D2 and D8 (§1). The controller took the decisions below.
The plan-level ones were audited (§1, "Audits and reviews"); the
execution-level ones are in the ledger.

```text
┌────────────────────────────────────────┬────────────────────────────────────────┬───────────────────────────┐
│ Decision                               │ Reason                                 │ Cost if wrong             │
├────────────────────────────────────────┼────────────────────────────────────────┼───────────────────────────┤
│ 1. D9: `rowsOk` is one function, used  │ Astra A02 and fgsa-impl F1/F6: a       │ It is a wire-validity     │
│ in both `wellFormed` and               │ weaker check lets FG and base content  │ choice. A failed `rowsOk` │
│ `blockAccepted`. It is a full          │ differ. The same function in both      │ is a permanent refusal of │
│ reconstruction check: `b.body ==       │ places means a wire that `wellFormed`  │ that wire. If the P2P     │
│ packBody (appOf b.body) rw`            │ accepts passes the admission content   │ spec wants a different    │
│                                        │ test. It is a content check, not a     │ split (for example the    │
│                                        │ root check, so it is inside D2. DC m5  │ check only at admission), │
│                                        │ accepted it as a decision without the  │ `wellFormed`,             │
│                                        │ user                                   │ `blockAccepted`,          │
│                                        │                                        │ `MetaInv.wireTree` and    │
│                                        │                                        │ the FG-SA fixtures change │
├────────────────────────────────────────┼────────────────────────────────────────┼───────────────────────────┤
│ 2. D4: the codec is `epair`            │ `Nat.pair` and r1's `lpair` double the │ The kernel fast path for  │
│ (length-delimited: the delimiter codes │ size at each nesting level (Finding 1: │ `2 ^ k` holds only for `k │
│ `bitLen b`, not `b`) with a total,     │ about 1.1·10^13 bits and 1.6·10^9 to   │ < 2^24`. FG-SA roots grow │
│ globally correct log-step `bitLen` and │ 5.5·10^10 bits at B3). `Nat.log2`      │ about 8× per level, so    │
│ `tz` on input-dependent fuel           │ unfolds in quadratic time in the       │ this limit is near B7. A  │
│                                        │ kernel. A truncated `bitLen` makes     │ deeper concrete fixture   │
│                                        │ `epair` collide (Astra R01). The Task  │ does not finish in the    │
│                                        │ 0 spike measured B3 at 21,373 bits and │ kernel. A change of codec │
│                                        │ B4 at 166,846 bits                     │ changes every root, every │
│                                        │                                        │ proved order and every    │
│                                        │                                        │ lock hash again           │
├────────────────────────────────────────┼────────────────────────────────────────┼───────────────────────────┤
│ 3. `decide +kernel` for fixtures with  │ Plain `decide` cannot evaluate `2 ^ k` │ The checks depend on      │
│ large roots                            │ above `exponentiation.threshold`       │ kernel evaluation cost. A │
│                                        │ (256), and a raised threshold reaches  │ false goal shows as       │
│                                        │ the recursion limit (Finding 2).       │ "maximum recursion        │
│                                        │ `decide +kernel` adds no axiom.        │ depth", not as false, so  │
│                                        │ Switches: SimplexFG 14, KitFG 5        │ a failure is harder to    │
│                                        │ examples and one new example, FG-SA    │ read (DC m2: `#eval` the  │
│                                        │ Smoke 62 (10 → 76 sites), all of       │ Boolean first). Large     │
│                                        │ `RootCollision.lean`                   │ stores need the           │
│                                        │                                        │ `process_eq_admitWith`    │
│                                        │                                        │ rewrite (§8)              │
├────────────────────────────────────────┼────────────────────────────────────────┼───────────────────────────┤
│ 4. I9-A01: a named exception allows    │ The helpers served only the removed    │ None for soundness. If a  │
│ the deletion of five private helpers   │ root proofs of kept statements. The    │ later plan needs these    │
│ (`delivered_blocks`, `emitted_blocks`, │ kept statements are now proved by      │ facts, it proves them     │
│ `named_block`, `roots` in the SA-PC    │ `rootInjective_all` or                 │ again from the fixture    │
│ file                                   │ `Block.root_injective`. A restore adds │ definitions               │
│ `CleanInvariantCounterexample.lean`;   │ dead code with no user. Astra found no │                           │
│ `emitted_proposed` in                  │ soundness defect                       │                           │
│ `Witnesses/Sanity.lean`). Commit       │                                        │                           │
│ 6ebbb26                                │                                        │                           │
├────────────────────────────────────────┼────────────────────────────────────────┼───────────────────────────┤
│ 5. `fgBodyTag = 1` added to            │ r203 §3 asks for a domain tag, so that │ One extra small commit.   │
│ `encFGBody` at Task 7 (4885a83),       │ a later typed domain for base          │ The tag does not change   │
│ before Tasks 8–9 fixed their root      │ application bodies does not collide    │ `FGBlock.root_injective`  │
│ orders                                 │ with FG codes. A later addition would  │ or the erasure law. B3    │
│                                        │ recompute every proved order of Tasks  │ grows from 2,871 to 3,297 │
│                                        │ 8 and 9                                │ bits                      │
├────────────────────────────────────────┼────────────────────────────────────────┼───────────────────────────┤
│ 6. Placement: the SA-PC lemma          │ Consistency with Grid CO               │ One move back. No         │
│ `blockKnown_parent_slot_iff_root`      │ (`Proofs/Handling.lean`) and the       │ statement changes         │
│ moved from `Model/Handlers.lean` (the  │ separation of model and proofs. SA-PC  │                           │
│ plan's file list) to                   │ `Model/` files had no theorem before   │                           │
│ `Proofs/BaseViews.lean` (98bd9a7); the │                                        │                           │
│ L* lookup and no-op lemmas are in      │                                        │                           │
│ `LStar/Proofs/Hooks.lean`, not in a    │                                        │                           │
│ Model file                             │                                        │                           │
├────────────────────────────────────────┼────────────────────────────────────────┼───────────────────────────┤
│ 7. The four `hroot`-taking Grid CO     │ The plan says "keep names and          │ None now. The premises    │
│ lemmas                                 │ statements". A proof from              │ stay redundant until the  │
│ (`stored_ancestors_root_injective`,    │ `Block.root_injective` leaves `hroot`  │ API plan removes them     │
│ `stateBefore_rootInjectiveBelow`,      │ unused, and the linter fails under     │                           │
│ `time_input_rootInjectiveBelow`,       │ `--wfail`; a rename to `_hroot` is a   │                           │
│ `proposalState_rootInjectiveBelow`)    │ text change. The removal of `hroot`    │                           │
│ keep their old proofs and statements.  │ belongs to the later API plan (D6)     │                           │
│ `rootInjectiveBelow_all` is new        │                                        │                           │
├────────────────────────────────────────┼────────────────────────────────────────┼───────────────────────────┤
│ 8. `contentAgree` takes only `MetaInv` │ `CStoreInv` is not needed: equal roots │ None for callers with     │
│ at the two stores, not `CStoreInv` and │ give equal blocks by                   │ both invariants. The T7   │
│ `MetaInv` as the plan says.            │ `Block.root_injective`, and `wireTree` │ plan r10 text still says  │
│ `contentAgree_self` keeps its old      │ gives `rowsOk` for both wires. An      │ "CStoreInv and MetaInv";  │
│ proof                                  │ unused premise fails the linter. A     │ T7 must cite              │
│                                        │ theorem with fewer premises is         │ `contentAgree_reachable`  │
│                                        │ stronger                               │ or `contentAgree` with    │
│                                        │                                        │ two arguments (§8)        │
├────────────────────────────────────────┼────────────────────────────────────────┼───────────────────────────┤
│ 9. Task 10 (documents) ran in a        │ Task 10 never raced Task 9's commits   │ Stale docs if a slot is   │
│ separate worktree (session scratch     │ in one work tree. The docs are text    │ missed. Two slots stayed  │
│ `wt-i9-docs`, branch `i9-docs` from    │ only                                   │ for Task 11               │
│ `e42bb37`) while Task 9 ran; facts     │                                        │ (`CONTRACT.md`,           │
│ that depend on Task 9 or Task 11 were  │                                        │ `GRIDCO-STATUS.md`);      │
│ `[[CONTROLLER]]` slots. The controller │                                        │ 9b5892b filled them. The  │
│ merged it after Task 9 (4bdb7fa) and   │                                        │ docs review (§9) found 20 │
│ filled six slots (b89ed5a)             │                                        │ items; the final docs     │
│                                        │                                        │ commit fixed them         │
├────────────────────────────────────────┼────────────────────────────────────────┼───────────────────────────┤
│ 10. D3: store-only variant. Payloads   │ The smallest change that gives D1 and  │ It is a resolved-block    │
│ keep resolved blocks; no `Msg`,        │ D2. It keeps the contract statements   │ model, not a root-only    │
│ `Interface` or contract change         │ and the payload types. DC-simplify     │ wire. A root-only wire    │
│                                        │ agreed. The user was asked and did not │ needs an adapter that     │
│                                        │ answer, so the plan went ahead on its  │ keeps authentication,     │
│                                        │ default                                │ dependencies, handler     │
│                                        │                                        │ calls, refusals and       │
│                                        │                                        │ proposal origin (§8)      │
├────────────────────────────────────────┼────────────────────────────────────────┼───────────────────────────┤
│ 11. D10: `RowCodec V` is a type class  │ fgsa-impl F2: statement texts keep     │ 141 KitFG theorems carry  │
│ with a `Fin n` instance                │ their form; only an instance binder is │ the binder. A later       │
│                                        │ added (class (b))                      │ change to an explicit     │
│                                        │                                        │ codec argument changes    │
│                                        │                                        │ all of them               │
├────────────────────────────────────────┼────────────────────────────────────────┼───────────────────────────┤
│ 12. D5, D6, D7 (from r203): honest     │ r203 §1, §3, §4, §9. D5: the honest    │ D6: redundant fields and  │
│ body 0; regime root fields stay,       │ body gets a run input only in Phase 2c │ premises stay until the   │
│ filled by the universal lemmas; one    │ (I1). D6: the fields stay, so no       │ API plan. D7: one large   │
│ joint change on the merged tree, FG-SA │ contract statement changes. D7: the    │ branch; main moved during │
│ included                               │ type change breaks every library that  │ the work (merged in       │
│                                        │ uses `Block`, so all change together   │ f756404)                  │
│                                        │ (plan Architecture)                    │                           │
├────────────────────────────────────────┼────────────────────────────────────────┼───────────────────────────┤
│ 13. The real FG-SA `stA` measurement   │ The real `process` cannot run on       │ Late discovery. It        │
│ moved from Task 0 to Task 9, with the  │ post-I9 types before Tasks 1, 7 and 9. │ happened: without a       │
│ same stop rule                         │ The Task 0 sketch showed no measurable │ rewrite, four Smoke       │
│                                        │ codec cost at B4                       │ checks took more than 60  │
│                                        │                                        │ s and 1–6 GB. Task 9      │
│                                        │                                        │ changed the tests, not    │
│                                        │                                        │ the model (decision 14)   │
├────────────────────────────────────────┼────────────────────────────────────────┼───────────────────────────┤
│ 14. FG-SA tests use the proved rewrite │ The kernel reduces `fgBlock P b rows`  │ Each new large concrete   │
│ `process_eq_admitWith` (and `stP_eq`,  │ again at each use and decodes the body │ fixture (FG-SA or T7)     │
│ `stB_eq`, `stK_eq`) instead of a model │ each time. The rewrite is a theorem    │ needs the same rewrite.   │
│ change that stores a pre-decoded FG    │ from the handler, so the tests still   │ Symbolic proofs are not   │
│ block                                  │ test `process`. A model change needs a │ affected (§8)             │
│                                        │ payload field, which the plan forbids  │                           │
├────────────────────────────────────────┼────────────────────────────────────────┼───────────────────────────┤
│ 15. Fixture `X` in FG-SA Smoke has     │ It keeps `X` as the winner of the      │ None for the model. A     │
│ application value `2 ^ 4096`           │ wrong-controls alternative, so the     │ reader can mistake it for │
│                                        │ test can detect wrong controls. The    │ an honest body; the       │
│                                        │ application value is free; no handler  │ docstring says it is a    │
│                                        │ reads it; `X` has no children          │ free test value           │
├────────────────────────────────────────┼────────────────────────────────────────┼───────────────────────────┤
│ 16. Smaller rulings: Grid CO and L*    │ Each keeps statements and intent with  │ Cosmetic or one-commit    │
│ Smoke pins as `example … := by         │ the smallest change. The Registry is   │ fixes                     │
│ decide`; `chain (k+1)` body `k` and    │ L4, and FRAMEWORK-DESIGN §1 forbids    │                           │
│ `clockBlock (k+1)` body 0; unused      │ Kit imports only in L0–L3              │                           │
│ `chain_injective`,                     │                                        │                           │
│ `clockBlock_injective` and older       │                                        │                           │
│ unused Registry lemmas kept; KitFG     │                                        │                           │
│ pattern binders named `r` kept (Task 8 │                                        │                           │
│ m1); the 101-character line 160 of the │                                        │                           │
│ SA-PC counterexample file kept         │                                        │                           │
│ (unchanged text); Registry files       │                                        │                           │
│ import `AvailableChainKit.Roots`       │                                        │                           │
└────────────────────────────────────────┴────────────────────────────────────────┴───────────────────────────┘
```

## 8. Follow-ups

- Pins. For `fg.accountable.v1`, `fg.uniqueJust.v1` and `fg.finalLock.v1`,
  `RootInjectiveOn` is the only named hypothesis. Their coverage kind
  `leanHyp` becomes `.lean` when a later plan removes the binders (Task 8
  review m2). The other annotated `leanHyp` strings then drop the
  `(viewRootInj_all)` or `(rootInjectiveOn_all)` notes.
- Regime fields and `hroot`. A later API plan removes the five regime root
  fields, `CStoreInv.rootInj`, the `Inv0` conjunct, the `hroot` premises of
  the four Grid CO `Proofs/Roots.lean` lemmas, the `RootInjectiveOn` and
  `ViewRootInj` binders, and the redundant `ContentAgree` premises of the
  FG-SA cross-node theorems (r203 §9 step 5). Each removal is a statement
  change and changes lock lines again.
- Relay feasibility (plan 1c). A missing dependency is a handler fact, not a
  run fact. `PartialSynchrony` and `HealthyPrefixDelivery` have relay
  obligations with no dependency guard
  (`AvailableChainStatements/Generic/Conditions.lean`). I9 proves only the
  lookup lemmas and the no-op facts. Plan 1c must classify "dependencies
  never present".
- Root-only wire. The P2P spec discussion is deferred (D2). A root-only wire
  needs an adapter that keeps authentication, dependencies, handler calls,
  refusals and proposal origin. The L* adapter must apply the L* parent-slot
  test after the store lookup, because the L* handler does not repeat the
  `wellFormed` test (`AvailableChainLStar/Model/Protocol.lean:283, 300`).
- `fgBlock` kernel cost. A `decide +kernel` over a large concrete FG-SA store
  can take minutes and GBs, because the kernel decodes the body at each use of
  `fgBlock`. New large fixtures (FG-SA, T7) must use `process_eq_admitWith`
  (`AvailableChainFGSA/Tests/Support.lean`). Record this in T7's TR7. The T7
  plan r10 text about `contentAgree` ("CStoreInv and MetaInv") needs the
  `MetaInv`-only form.
- `docs/FG-COMPOSITION.md`. The entries that call `ViewRootInj` or root
  injectivity an idealization are stale: §0.4 (573–580), §0.2 (360, 513),
  `fg.frameCompat.v1` (870), `fg.finalLock.v1` (3514–3515; the pinned DC
  quote at 3534 stays), `fj.frame.v1` (4020), `fj.frame.v2` (4130–4132),
  `fj.frame.v3` (4357–4359), `fj.frameFeasible.v1` (4646),
  `fj.inBandLock.v1` (4876), `fj.twoChanges.core.v1` (4997, 5064). The
  Lean statements keep the premises, so each line needs a dated note that
  `viewRootInj_all` or `rootInjectiveOn_all` discharges it. §8 f1
  (6962–6963) is a dated history note; it stays. The line numbers are from
  the Task 8 report and the docs review. DC-simplify owns the file.
  The I9 branch does not edit it; the controller handles it after the merge.
- SA-PC `Pending/*`. The three modules are in no default target, so no
  standard check compiles them (§3). The controller compiled them on this
  tree with no error, but a later `Block` change can break them silently.
- Smaller items: L* has no `Tests/Axioms.lean`, so its two new lemmas have
  no committed `#print axioms` line (the Grid CO lemmas are in SA's file);
  the KitFG pattern binders named `r` (Task 8 m1); the `2 ^ k` kernel
  fast-path limit (`k < 2^24`) for deeper fixtures; `CatalogLock --check`
  output interleaves stdout and stderr under `2>&1` (capture the streams
  apart).

## 9. Docs review

The docs review (`.superpowers/sdd/2026-09-29-i9-derived-roots/docs-review.md`,
not in Git) read the docs diff of the branch at `f756404`. Result: Needs
fixes (3 factual, 5 stale, 3 inconsistencies, 9 minor); fixed in the final
docs commit before the merge. It also checked every Lean name in the new
text against the tree, with no finding.

```text
┌────────────────────────────────┬────────┐
│ Section                        │ Count  │
├────────────────────────────────┼────────┤
│ Factual errors                 │ 3      │
│ Stale current-state text       │ 5      │
│ Inconsistencies                │ 3      │
│ Minor/style                    │ 9      │
│ FG-COMPOSITION (not counted)   │ 10     │
└────────────────────────────────┴────────┘
```

The final docs commit fixed all 20 counted items. Factual error 2 (a
dangling link to this report) and inconsistency 1 (the record of the
deleted helpers) are fixed by this report (§5.10) and by the plan's
exception row with the audit path. The field-removal wording is now "a
later plan (plan I9 D6)" in `CONTRACT.md`, `FRAMEWORK-DESIGN.md`,
`PHASE0-REPORT.md` and `GRIDCO-STATUS.md`. `SA-STATUS.md` and
`SAPC-STATUS.md` have dated I9 sections. The audit report
`docs/audit/i9-branch-audit-0-8-report.md` stays verbatim; its new first
lines give a title and say so. The FG-COMPOSITION items are in §8.

## 10. Merge

main was fast-forwarded to 3403e58 on 2026-09-29. Checks on the merged
tree: `lake build --wfail` 3629 jobs, `CatalogLock --check` exit 0,
`CheckFrameworkAxioms` 771 constants, `Registry --check` exit 0.
