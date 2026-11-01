# FG-SA model store: report (Tasks 1–13)

Branch `fgsa-composition`. Plan: `docs/plans/2026-09-29-fgsa-model-store.md`.
Gate reports: `docs/audit/fgsa-task{6..12}-opus-review.md`,
`docs/audit/fgsa-model-check-report.md`, and the final audit (G13):
`docs/audit/fgsa-final-audit-astra.md`, `docs/audit/fgsa-final-audit-opus.md`,
with the verification of its fold: `docs/audit/fgsa-final-audit-fold-verify.md`.
This file is the Task 13 report with the G13 corrections. §7 adds the
status after plan I9 (2026-09-29).

Scope. All results are LOCAL store facts over the over-approximate `Reachable`
(no input check, any clock value; DQ14). The cross-node results take the
store-pair property `ContentAgree`. After I9 it is a theorem for any two stores
with `MetaInv` (`contentAgree`; §7). Before I9 (2026-09-29), it was a
store-pair premise, and the cross-node results held only for store pairs under
it. They do not establish a common full proposal payload, a run adapter, or
safety across nodes. `FastOrigin` is the local
relation that K1 needs; it is not a proof of every clause of
`bp.leaseOrigins.v1` or K6. Run lifts are composition task T7.

## 1. K table: completed local facts and remaining run lifts

```text
┌──────────────────┬──────────────────────────────────────┬────────────────────────────────────┐
│ K id / bp id     │ Lean names                           │ Extra hypotheses / remaining lift  │
├──────────────────┼──────────────────────────────────────┼────────────────────────────────────┤
│ K1               │ reconcile_harmless_origin (Proofs/   │ origin form: FastOrigin F₀ st,     │
│ bp.reconcile.v1  │ Reconcile); admitBlock_reconcile_    │ F₀ ⪯ F, hL, hG, hS. Block step:    │
│                  │ harmless (Proofs/StoreInv). No       │ CStoreInv st, hP, hacc, hL, hG, hS │
│                  │ fastWrite premise. reconcile_        │ (all at the new F). hL = every row │
│                  │ harmless = HELPER only (it has the   │ of obligations, due leases         │
│                  │ fastWrite premise)                   │ included (G9 m2). Lift: T7 (b), K7 │
│ K2               │ outputNesting_stored,                │ none (no other invariant). Run     │
│ comp.outputNest- │ outputNesting_v1,                    │ lift: T7. Conjuncts 2–3 are rfl    │
│ ing.v1/v2        │ finalized_preceq_stable              │ (DQ7)                              │
│ K3               │ reconcile_frame,                     │ none for reconcile_frame and       │
│ bp.frame.v1,     │ storeControls_reconcile,             │ storeControls_reconcile;           │
│ bp.reconcile.v1  │ storeControls_eq                     │ storeControls_eq needs CStoreInv   │
│ K4 core          │ storeInvariant (CStoreInv, 9         │ none. "F, J ∈ T": Fmem + J_mem     │
│ bp.store.v1      │ fields), fMonotone, process_F_mono,  │ (G11 m2). Tick part of "pair, H    │
│                  │ clock_F_eq, process_hmax_mono,       │ monotone": clock_fg                │
│                  │ process_pair_mono, J_mem             │                                    │
│ K4 metadata      │ metadataInvariant (MetaInv, 9        │ none. "T cumulative", "old stamps  │
│ bp.store.v1      │ fields incl. noGenesisWire),         │ unchanged": process_cumulative,    │
│                  │ process_cumulative, clock_cumulative │ clock_cumulative, MetaInv          │
│ K5 local         │ viewRootInj_TF, viewRootInj_of_      │ CStoreInv (root injectivity of Σ.T │
│ bp.carrier.v1    │ rootInj, compatible_iff_eraseFG,     │ holds by construction, DQ2). After │
│                  │ preceq_of_eraseFG_preceq,            │ I9: rootInj_all, viewRootInj_all;  │
│                  │ rootInjectiveOn_of_viewRootInj       │ no premise                         │
│ K5 cross-node    │ fg_eq_of_eraseFG_eq_across,          │ CStoreInv, MetaInv at both stores, │
│ bp.carrier.v1    │ preceq_iff_across,                   │ ContentAgree st st' (DQ3(b),       │
│                  │ compatible_iff_across,               │ narrowed at G12). After I9 it is a │
│                  │ rootInjectiveOn_across (the two-     │ theorem (contentAgree: MetaInv at  │
│                  │ chain KitFG.accountable premise);    │ both stores); no run premise.      │
│                  │ contentAgree_self; after I9:         │ Before I9 (2026-09-29): a store-   │
│                  │ contentAgree, contentAgree_reachable │ pair premise (reversed comp D4);   │
│                  │                                      │ run form ContentRootInjective: T7. │
│                  │                                      │ contentAgree_self: no content      │
│                  │                                      │ premise; needs CStoreInv, MetaInv  │
│ K8 input         │ admitBlock_sufficient,               │ CStoreInv, wellFormed wire, stored │
│ bp.receipt-      │ admitBlock_sufficient_absent         │ parent, slot ≤ Σ.s, fresh root     │
│ Coverage.v1      │                                      │ (DQ2) or absent + root premise,    │
│                  │                                      │ F ⪯ b. Run form of K8: T7. After   │
│                  │                                      │ I9 the root premise is a theorem   │
│                  │                                      │ (Block.root_injective); fresh root │
│                  │                                      │ = absent                           │
│ bp.activeView.v1 │ items 1–6: actView_blocks,           │ items 1, 2, 4 and actView_eq_image │
│                  │ actView_genesis_F (1); actView_      │ need CStoreInv; items 3, 5, 6 need │
│                  │ ancestor_closed (2); actView_        │ none (item 6: K ⪯ F). A result at  │
│                  │ antitone (3); actView_path (4);      │ the anchor F of item 6 (walk from  │
│                  │ blockExcluded_stable, actView_eq,    │ F since 4e85ff34): F ∈ A by        │
│                  │                                      │ actView_genesis_F (G7 m4)          │
│                  │ actView_fields (5); actView_noVeto,  │                                    │
│                  │ actView_releaseCount_zero (6);       │                                    │
│                  │ actView_eq_image                     │                                    │
│ SA bridges       │ clock_eq_saClock_offGate,            │ offGate: t not a gate time. gate:  │
│ comp D3, J3      │ clock_eq_saClockFrom_gate (and       │ gate time of s, hnew (label not    │
│                  │ _gate'), actView_admitBlock_sameF,   │ saved; DQ5); the SA tick with the  │
│                  │ actView_admitBlock_movedF            │ walk from F (SA.clockFrom at       │
│                  │                                      │ eraseFG F; spec 4e85ff34). Block:  │
│                  │                                      │ CStoreInv, hP, hacc, F same / F    │
│                  │                                      │ moved (movedF is the SA admission, │
│                  │                                      │ filtered by the new F, plus        │
│                  │                                      │ reconcile's 3 writes)              │
└──────────────────┴──────────────────────────────────────┴────────────────────────────────────┘
```

Not done here (out of scope): K6–K11, theorems (b), (c), (c′), (d)
(composition T8–T16); the lease parts of bp.leaseOrigins.v1; every run lift.

## 2. Differences found

Against the spec (archive 2e884811): no new undeclared rule difference at the
stated protocol boundary (checked inputs, scheduled event order; G3–G6
reviews, the Astra model check r195, G13). Since the spec sync (branch
fgsa-spec-sync, 2026-09-29) the model follows spec 4e85ff34 in
`genuine_result` (the walk from Σ.F with the final test also at F), so it
differs from 2e884811 there: in Smoke test T1, 2e884811 saves `some genesis`
and the model saves `none`. Every other rule is unchanged.

Declared differences:
- DQ10/DQ2 (G13 Opus m4): closed by I9. Roots are derived and injective, so
  the DQ2 root test refuses a block only when the same block is stored. This
  agrees with the spec idealization of distinct roots (spec 167, 521).
  Before I9 (2026-09-29): under a root collision of the GridCO formula, the
  DQ2 root test refused an honest block, and `Tests/RootCollision.lean`
  showed it.
- Release cutoff (r195 D2; `Reachable` docstring; G13 Astra N2):
  `GridCO.releaseCount` (`AvailableChainGridCO/Model/Protocol.lean:397`)
  tests equivocation in all stored label-r votes; spec 1197–1200 tests the
  votes stamped before `q_r`. They agree at the scheduled release before
  same-time deliveries. They can differ after later votes and a repeated or
  backward clock. No statement claims release equivalence on an arbitrary
  store.
Declared model-only fields:
`goldfishRecord`, `frozen`, `early`, `releaseSnapshots`, `base.proposals`
(DQ8); no FG-SA output or duty reads them. Known limits, both inherited or T7
obligations: `goldfishScore` equals the spec score only when support ⊆ raw
(checked by `wellFormed`, not by `process`; G6 O-m4); `headVote` and
`propose` agree with the spec only when `s = st.slot p` (G6 O-m3).

Against the blueprint:
- DQ1 flat wire: `eraseFG (fg B) = erase B` is `eraseFG_fgBlock`.
- DQ2: the duplicate test is root freshness, not "absent". K8
  (`admitBlock_sufficient`) takes a fresh root; `admitBlock_sufficient_absent`
  takes "absent" plus a root premise (G10 m2). After I9 the root premise
  is a theorem (`Block.root_injective`); fresh root = absent.
- K1: `hL` quantifies over every row of `obligations`, including due leases
  that the next tick expires (spec 447–448, 736–741). With "live" read as
  "deadline in the future", the blueprint claim is false for such a row
  (G9 m2). T7 (b) and K7 must show compatibility for due leases too.
- bp.store.v1 "F, J ∈ T": `KitFG.StoreInv` has no J field; `J_mem` proves it.
- Stronger than planned: `admitBlock_accepted_eq` has no `Inv0` premise
  (G10 m1); `fastSet_prefix` has `B ≠ genesis` (G7 m2); `ContentAgree` is
  narrowed (G12 M1), so the four cross-node theorems are stronger.
- One extra `MetaInv` field (risk R11): `noGenesisWire` (G12 m1). It needs no
  new premise; it gives `contentAgree_self`.
- Nesting holds for COMPLETED events; the state inside `admitBlock` before
  `reconcile` can have a moved F and the old S (G8 m3).

Against comp §4: after I9, D4 holds in content: `rowsOk` is a model content
check, and `ContentAgree` is a theorem, so no run premise is necessary. It is
not the root equation of DQ3(a), because roots are derived. Before I9
(2026-09-29), D4 was REVERSED (DQ3(b)): a named content premise, no model
check. D3: the tick bridge needs `hnew` (the evaluate-once guard, DQ5) and,
at run level, one tick per public time. J3: with a moved F the block-step
bridge is the SA admission with the blocks filtered by the new F and
reconcile's three writes, not the plain SA admission.

Smoke tests: every planned value agreed with the hand computation (Tasks 3–6;
each docstring has the computation). R1 fallback: `decide +kernel` for the
`stP` test and six G6 tests (plain `decide` hits the recursion limit). No
value rests on `#eval` alone. The G6 negative controls show that each
plausible wrong rule gives a different value.

Kernel cost after I9 (Task 9). A kernel check that uses `fgBlock` on a concrete
store is slow. The kernel reduces `fgBlock P b rows` again at each use, and each
reduction decodes the body (`appOf`). Before the fix, some Smoke checks took
more than 60 s each, and the whole file used up to 7.1 GB. So a test on a
concrete store first rewrites the delivery with the proved equation
`process_eq_admitWith` (`Tests/Support.lean`). Then each check takes less than
1 s, and the test still tests `process`. Use `rw`, not `simp`, for this rewrite.
Symbolic proofs do not pay this cost: they use `rowsOk_iff`, `eraseFG_fgBlock`
and `fgBlock_root` under hypotheses. After Task 9, every Smoke check that reads
a packed block uses `decide +kernel`, because plain `decide` cannot evaluate the
large codes.

## 3. DQ answers used and open findings

DQ1 (a) flat wire. DQ2 (a) root test. DQ3 (b) content premise, narrowed at G12
(after I9 a theorem, `contentAgree`). DQ4 (a) Λ outside `State`. DQ5 (a)
evaluate-once guard. DQ6 (a) spec HEAD tree at read time. DQ7 v2 reading (F ⪯ S,
both accessors = S). DQ8 keep the model caches, declared. DQ9 no hooks;
`blockExcluded`, `wellFormed`; "processed by root". DQ10 keep the GridCO root
formula; limit stated (superseded by I9, 2026-09-29: roots are derived). DQ11
docstring tags now, pin table in T15. DQ12 refuse undecodable carried rows. DQ13
spec `deepest` tie rule (`deepest_spec`). DQ14 `process` separate from
`wellFormed`; `Reachable` over-approximates.

Open: no gate finding is open (G1–G13 closed; each disposition is in the
plan). The last test gap of r195 N3 (an active stored target that only the
FJ filter excludes) is closed by the `stL` tests in `Tests/Smoke.lean` (G13
Astra N3). The user decision DQ10/DQ3 is closed (I9, 2026-09-29): roots are
derived from the content, and the parent-root check is the store dependency
lookup (§7). Before I9, it was open: arithmetic roots plus a content premise,
or content-coded roots with an admission check across GridCO/SA/FG-SA.
Q1 (engine) and Q5 (deliverable) stay open; objects are v1-typed (J1).

## 4. Validation

Before I9 (2026-09-29). The values after I9 Task 9 are in §7.

```text
┌────────────────────────────────────────────────────┬──────────────────────────────────────┐
│ Command                                            │ Result                               │
├────────────────────────────────────────────────────┼──────────────────────────────────────┤
│ lake build --wfail (full project target)           │ pass, 3601 jobs                      │
│ bash scripts/check-fgsa.sh                         │ exit 0: build; root imports and      │
│                                                    │ direct-import allowlist on parsed    │
│                                                    │ headers (fail closed; find -L        │
│                                                    │ -iname); native scan; Q1/Q5 grep     │
│                                                    │ (Run, Env, Interface, Claims added); │
│                                                    │ axioms (805 constants, 442           │
│                                                    │ theorems), build coverage, direct    │
│                                                    │ imports of 21 FGSA modules on the    │
│                                                    │ compiled data, import closure (5503  │
│                                                    │ modules, no forbidden library);      │
│                                                    │ lease instances (788 constants, 17   │
│                                                    │ generated equation lemmas skipped,   │
│                                                    │ 335 imported definitions inspected,  │
│                                                    │ 76 lease arguments, backstop over    │
│                                                    │ 4203 reached constants)              │
│ negative controls in check-fgsa.sh                 │ all rejected: unlisted library;      │
│                                                    │ wrong-layer import (KitFG in Model/, │
│                                                    │ Proofs in Statements/); import after │
│                                                    │ a comment and a line break; orphan   │
│                                                    │ modules with a sorry (behind a       │
│                                                    │ commented root import, and with a    │
│                                                    │ .LEAN name; root check and compiled  │
│                                                    │ coverage check); SAPC in the         │
│                                                    │ closure; a «» module name, a prelude │
│                                                    │ line, a .LEAN file and a linked      │
│                                                    │ directory (text allowlist, Q1/Q5     │
│                                                    │ grep, compiled allowlist); lease:    │
│                                                    │ direct default call, alias wrapper   │
│                                                    │ with its own policy parameter,       │
│                                                    │ generic wrapper with an alias policy │
│                                                    │ type, imported wrapper that fixes    │
│                                                    │ the default, LeasePolicy.mk outside  │
│                                                    │ AvailableChain; imported let, beta,  │
│                                                    │ private, irreducible-alias and non-  │
│                                                    │ AvailableChain wrappers (G13 fold    │
│                                                    │ verification)                        │
│ lake env lean --run scripts/CheckFGSAAxioms.lean   │ exit 0                               │
│ --expect <the 15 names of Step 2>                  │                                      │
│ Tests/Axioms.lean (206 #print axioms)              │ only propext, Classical.choice,      │
│                                                    │ Quot.sound (8 theorems: none)        │
│ grep sorry/admit/native_decide/axiom               │ none in AvailableChainFGSA (outside  │
│                                                    │ comments)                            │
└────────────────────────────────────────────────────┴──────────────────────────────────────┘
```

Import closure after the merge with post-1b main (checked read-only on main
5f65103): FGSA's transitive closure reaches the libraries
`AvailableChainGridCO`, `AvailableChainKit`, `AvailableChainKitFG`,
`AvailableChainModel`, `AvailableChainSA`, `AvailableChainSimplexFG` and
`AvailableChainStatements`. `AvailableChainKit` enters through the Grid CO
proofs (`AvailableChainKit.Engine.EngineClock` and `.Execution`, after the
Kit split c79b473); like `AvailableChainStatements`, it is a declared
transitive dependency. No module of `AvailableChainFramework`,
`AvailableChainRegistry`, `AvailableChainSAPC`, `AvailableChainWitnesses` or
`AvailableChainEngineV2` is reached. FGSA imports no Kit module directly, so
the direct-import allowlist does not change.

## 5. Inputs for composition task T7

- Duty slot: `headVote` and `propose` need `s = st.slot p` (G6 O-m3).
- Q1 boundary table (plan §Q1) with the v1 object dependency (J1); a v2
  decode adapter keeps Store, Statements and Proofs (R10).
- `blockExcluded` and `blockExcluded_stable` (DQ9 exclusion hook);
  `wellFormed` and `blockAccepted_of_wellFormed` (input check; every handler
  call must have a checked input, `DeliveryWellFormed`, DQ14).
- "Processed" for a proposal = by root (`∃ Y ∈ Σ.T, Y.root = b.root`, DQ9).
- `attest` takes Λ and returns (row, Λ′); Λ is not in `State` (DQ4); the
  record/emission order and own-row admission (spec 681) are T7 obligations.
- Content premise: none after I9. `contentAgree_reachable` gives
  `ContentAgree st st'` for any two reachable stores, and `contentAgree`
  gives it for any two stores with `MetaInv`. T7 needs no run premise
  `ContentRootInjective`. Before I9 (2026-09-29): the run premise was
  `ContentRootInjective` (DQ3), and the derivation of `ContentAgree st st'`
  for two honest stores needed `MetaInv` and the run lemma "every stored
  wire is a payload that the node processed" (G12).
- `ContentAgree` is the store-pair property (DQ3(b), narrowed at G12 to the
  erased block and the rows). After I9 it is a theorem. Equal roots give
  equal blocks (`Block.root_injective`), and `rowsOk` gives equal ordered
  rows (`rows_eq_of_rowsOk`). So honest forks and faulty content
  equivocation cannot make it false. The cross-node lemmas keep it as a
  premise, which is now redundant. `contentAgree_self` keeps its own proof
  from `CStoreInv` and `MetaInv`. Before I9 (2026-09-29): it was false on
  honest-fork runs under the GridCO root formula (DQ10/I9) and on runs with
  faulty content equivocation; the cross-node lemmas were vacuous for such
  store pairs (`Tests/RootCollision.lean`: `not_contentAgree`, now deleted).
- DQ10 root limit: gone after I9. `RootInjective` holds for every run
  (`rootInjective_all`), and FG roots are injective
  (`FGBlock.root_injective`). Before I9 (2026-09-29): `RootInjective` and
  `ContentRootInjective` failed on honest forks (roots `s·(parent+1)`
  collided), and a faulty proposer could force this; the limit was inherited
  from GridCO/SA/SA-PC/L*.
- DQ10 and DQ2 together (G13 Opus m4): closed by I9. The DQ2 root test
  refuses a block only when the same block is stored. In
  `Tests/RootCollision.lean`, a node that holds `ba` accepts `c1` and then
  `bb`. Before I9 (2026-09-29): under DQ10 collisions the DQ2 root test
  refused honest blocks (a node that held `node(genesis, 4)` refused the
  honest `node(node(genesis, 1), 2)`, root 4). So the model differed from the
  spec there, and the K8 run form and every coverage claim needed
  `RootInjective` for this reason too.
- `clock_eq_saClockFrom_gate` needs one tick per public time (DQ5).
- Release event order (G13 Astra N2): the release at `q_r` must run before
  the deliveries of the same time and must not repeat at `q_r` or run after a
  backward clock; then `GridCO.releaseCount` equals the spec count. One tick
  per public time alone does not state this order.
- K1 reading: "K1 `hL`: live = present in `Σ.lease` (`obligations`),
  including due leases that the next tick expires (spec 447–448, 736–741)".
  So theorem (b) and K7 must show compatibility for due leases as well.
- K8 run form needs `hfresh` from `RootInjective` plus absence (or use
  `admitBlock_sufficient_absent`), and `hwf` from `DeliveryWellFormed`.
  After I9, `RootInjective` is a theorem (`rootInjective_all`), and
  `Block.root_injective` gives `hinj` of `admitBlock_sufficient_absent`.

## 6. Inputs for composition task T1 (registry)

```text
┌─────────────────────────┬────────────────────────────────────────────────────────────┐
│ Registry id             │ Lean names                                                 │
├─────────────────────────┼────────────────────────────────────────────────────────────┤
│ comp.outputNesting.v2   │ OutputNestingStored, outputNesting_stored,                 │
│                         │ finalized_preceq_stable (v1: outputNesting_v1)             │
│ bp.store.v1             │ StoreInvariant/storeInvariant, CStoreInv, J_mem,           │
│                         │ FMonotone/fMonotone, process_F_mono, clock_F_eq,           │
│                         │ process_hmax_mono, process_pair_mono,                      │
│                         │ MetadataInvariant/metadataInvariant, MetaInv,              │
│                         │ process_cumulative, clock_cumulative                       │
│ bp.frame.v1             │ storeControls_eq, storeControls_reconcile, fg_step_cases,  │
│                         │ reconcile_frame                                            │
│ bp.reconcile.v1         │ reconcile_* exact effects, reconcile_idem,                 │
│                         │ reconcile_harmless_origin (K1), admitBlock_reconcile_      │
│                         │ harmless (K1 at a block step), reconcile_fastOrigin        │
│ bp.carrier.v1           │ Carrier.lean (local), viewRootInj_TF, CrossNode.lean       │
│                         │ (cross-node, ContentAgree), stored_wire_of_block; after    │
│                         │ I9: contentAgree, contentAgree_reachable, rootInj_all      │
│ bp.activeView.v1        │ the six items above, actView_eq_image, saCompat_gateStep,  │
│                         │ fastOrigin_gateStep                                        │
└─────────────────────────┴────────────────────────────────────────────────────────────┘
```

## 7. Status after plan I9 (2026-09-29)

Sections 1–5 keep the text before I9 as dated notes ("Before I9"). Plan I9
(`docs/plans/2026-09-29-i9-derived-roots.md`) makes block roots derived
(`FRAMEWORK-DESIGN.md` §12 I9). The user decided the open DQ10/DQ3
question of §3: content-coded roots, with the parent-root check as the
store dependency lookup.

- DQ10 is superseded. The GridCO root formula is removed. Base and FG
  roots use the same `nodeRoot`, and both root functions are injective
  on their whole types (`Block.root_injective`,
  `FGBlock.root_injective`). So the DQ10 root limit of §2, §3 and §5 does
  not hold now: honest forks and faulty proposers cannot give two
  distinct blocks with one root. `RootInjective` holds for every run
  (`rootInjective_all`).
- DQ2 keeps its root test, but its declared difference in §2 is gone.
  The case "same root, distinct block" is impossible now. So the DQ2
  root test refuses a block only when the same block is already stored.
  Task 9 changed `Tests/RootCollision.lean` into positive tests.
  `ba_root_ne_bb_root` shows distinct roots, with no computed root value.
  `contentAgree_stX_stY` shows that `ContentAgree` holds. A node that
  holds `ba` accepts `c1` and then `bb`, and a repeated `bb` is refused
  as a duplicate. More checks: genesis versus a slot-0 node; one parent
  and slot with different bodies; the same decoded rows with different
  rounds; and two wrong row lists that `rowsOk` and `wellFormed` refuse
  with no store change. `not_contentAgree` and the negated cross-store
  example are deleted. Its helpers `fg_ba` and `fg_bb` were deleted in
  Task 9 and restored after the final review (Astra F1), with the old
  text; they are still true after I9.
- DQ3(b) and `ContentAgree`: done in Task 9 (commits 8298916, 731b4c5).
  `packInner app rw` packs the application value and the ordered signed
  rows. `packBody app rw` puts `packInner app rw` and the decoded rows into
  `encFGBody`. `appOf` reads the application value back. `rowsOk b rw`
  holds when `b.body = packBody (appOf b.body) rw`. `wellFormed` and
  `blockAccepted` use this same function (D9). It is a content check, not
  a root check. `fgBlock` builds the FG body from `packInner`, not from
  `b.root`. `eraseFG` maps an FG block to the base block with the body
  `encFGBody`. `MetaInv.wireTree` carries `rowsOk` for every stored wire.
- `contentAgree` proves `ContentAgree st st'` from `MetaInv` at the two
  stores only. `CStoreInv` is not necessary. `contentAgree_reachable`
  gives it for any two reachable stores. `rootInj_all` fills
  `CStoreInv.rootInj` by `FGBlock.root_injective`. The FG-SA lookup form
  is `parentFG_isSome_iff_root`, and the no-op fact for a missing parent
  is `admitBlock_missingParent`. The cross-node theorems keep their
  `ContentAgree` premises, which are now redundant.
- The run premise `ContentRootInjective` of §5 is not necessary. It was
  never a Lean definition. T7 uses `contentAgree_reachable`.
- Validation after Task 9 (731b4c5): `lake build --wfail
  AvailableChainFGSA` passes (3382 jobs, no warnings). `bash
  scripts/check-fgsa.sh` exits 0: axioms 893 constants, 495 theorems and
  22 FGSA modules; lease 875 constants and 76 lease arguments; all 10
  negative controls are refused. `Tests/Axioms.lean` has 223
  `#print axioms` lines (206 in §4); each prints a subset of {propext,
  Classical.choice, Quot.sound}. There is no `sorry`, `admit`,
  `native_decide` or new axiom. The full-project job count of §4 was not
  measured again in Task 9.
