# G7 review — Task 7 (write sets, active view, tick SA bridge)

Reviewer: Opus (independent; did not write the code). Date: 2026-09-29.
Commit: `2e684fa` (parent `8947f48`), branch `fgsa-composition`.
Plan: `docs/plans/2026-09-29-fgsa-model-store.md`, Task 7 (lines 1719–1889),
Global Constraints, review gates G7–G12 and the blocking list (lines 2420–2433).
Blueprint: bp00 `00-outline.md` §3.1 `bp.activeView.v1` (the pinned
`03afa5ae` text; the current file has the same `bp.activeView.v1` text, checked
by diff), bp01 `01-foundations.md` §5 (sha256 `989289cc…`, as pinned).

## Verdict: PASS

No BLOCKING finding. No MAJOR finding. Four MINOR findings. None of them
stops the checkpoint.

## Validation

- Scratch worktree at `2e684fa`, `.lake/packages` symlinked. I deleted the
  build products of `Statements/Invariants`, `Proofs/Fields` and
  `Proofs/ActView`, so these three modules compiled again (8.1 s, 8.3 s,
  3.8 s).
- `bash scripts/check-fgsa.sh`: exit 0. `lake build --wfail AvailableChainFGSA`
  passes (3341 jobs, no warning). Root imports, native scan, direct imports,
  import closure and the Q1/Q5 grep print nothing.
- Axioms: `checked 537 constants, 217 theorems`, exit 0. With `--expect` and
  all 48 names of the Task 7 code blocks and field list: every name is
  checked. `#print axioms` of `clock_eq_saClock_gate`,
  `clock_eq_saClock_offGate`, `gateStep_fresh`, `actView_releaseCount_zero`,
  `actView_path`: `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, `admit`, `axiom`, `set_option`, `implemented_by`, `unsafe`,
  `local instance` or `native_decide` in the three files.
- The scratch worktree is removed.

## Check 1 — statements against the plan code blocks

- `Statements/Invariants.lean` contains the Step 1 code block byte for byte
  (exact substring test).
- Steps 2–4: every declaration is present with the same text after whitespace
  normalization. An exact line test finds only these differences:
  `gateStep_fresh` (Fields.lean:205–206) and `clock_eq_saClock_offGate`
  (ActView.lean:200–201) are wrapped at the 100-column limit; the
  `saGate_blocks` docstring has a `[helper]` tag and new line breaks. This
  agrees with the implementer's note.
- The commit changes the plan only in the check boxes and the execution note.
  The code blocks of the plan are unchanged (`git diff 8947f48 2e684fa`).
- Every lemma of the Step 2 name list is present, with the plan types where
  the plan gives them (`clock_fg`, `clock_base_blocks`, `admitRow_eq`).

Forms that the implementer chose:

```text
┌──────────────────────┬──────────────────────────────────────┬─────────────────┐
│ Lemma                │ Chosen form                          │ Strength        │
├──────────────────────┼──────────────────────────────────────┼─────────────────┤
│ admitBlock_refused   │ parentFG = none ∨ ∃ P, parentFG =    │ Equal to the    │
│ (Fields.lean:60)     │ some P ∧ blockAccepted … P rows =    │ plan text. It   │
│                      │ false → admitBlock … = st; raw,      │ covers both     │
│                      │ support, rows are universal          │ refusal arms of │
│                      │                                      │ admitBlock      │
│                      │                                      │ (Handlers:60)   │
│ normalizeS_fields    │ exact equation: normalizeS st =      │ Stronger than   │
│ (Fields.lean:94)     │ {st with base := {st.base with       │ "only S": it    │
│                      │ stableRecord := if F ⪯ S then S      │ also gives the  │
│                      │ else F}}                             │ new value       │
│ clockPre_fields      │ conjunction: fg, blocks, proposals,  │ Equal or        │
│ (Fields.lean:251)    │ rowPool, genuine, fastWrite; the     │ stronger. Also  │
│                      │ plan names clockPre_fg, _genuine,    │ clockPre_eq     │
│                      │ _fastWrite exist as projections      │ (ActView:166)   │
│                      │                                      │ is exact        │
└──────────────────────┴──────────────────────────────────────┴─────────────────┘
```

## Check 2 — invariant definitions

- `Reachable` (Invariants.lean:21): the least set that contains
  `initial p.n` and is closed under `clock p · t` and `process p · o`. It is
  the reflexive-transitive closure of the local steps from the initial
  state. The docstring states the over-approximation (no `wellFormed`,
  arbitrary clocks).
- `CStoreInv` is not vacuous and is satisfiable. A scratch proof (not
  committed) shows `CStoreInv p (initial p.n)` from `KitFG.storeInv_init`
  and list facts, and shows that a state with an empty base block list fails
  `baseTree`. Its fields are substantive: the FG invariant (closure,
  genesis, F ∈ T, `h_max`, lex pair, F ⪯ J, carrier), root injectivity, the
  base list as the erased T, SA compatibility, S stored, fast-write origin
  and domain, and key uniqueness.
- `FastOrigin` agrees with bp01 §6.1: a member that stays after reconcile
  empties `C` is compatible with F and is below `C`. `C` conflicts with F, so
  the member is below F. Thus the disjunct `B ⪯ Fb` is the correct
  after-reconcile form.
- `SACompat`, `NestOK`: as the plan and bp00 (`bp.reconcile.v1`,
  `comp.outputNesting.v2`).

## Check 3 — bp.activeView.v1 items 1–6

```text
┌──────┬────────────────────────────────┬──────────────────────────────┬────────┐
│ Item │ Blueprint (bp00 §3.1, bp01 §5) │ Lean                         │ Result │
├──────┼────────────────────────────────┼──────────────────────────────┼────────┤
│ 1    │ A ⊆ T, g ∈ A, F ∈ A            │ actView_blocks (:54),        │ equal  │
│      │                                │ actView_genesis_F (:59)      │        │
│ 2    │ A is ancestor-closed           │ actView_ancestor_closed (:67)│ equal  │
│ 3    │ fixed T, F ⪯ F' → A(F') ⊆ A(F) │ actView_antitone (:76); no   │ equal  │
│      │                                │ CStoreInv premise            │        │
│ 4    │ F ⪯ B ⪯ K, K ∈ T → K ∈ A and   │ actView_path (:86); B is     │ strong-│
│      │ every path vertex is in A      │ universal, need not be in A  │ er     │
│ 5    │ removed block never returns;   │ blockExcluded_stable (:97);  │ equal  │
│      │ no signed pool or stamp change │ actView_fields (:108) has    │        │
│      │                                │ votes, proposals, both stamps│        │
│ 6    │ K ⪯ F → active heads compatible│ actView_noVeto (:117),       │ equal  │
│      │ with K; release count 0; no    │ actView_releaseCount_zero    │ (see   │
│      │ veto of active genuine result  │ (:126), any q, any label     │ below) │
└──────┴────────────────────────────────┴──────────────────────────────┴────────┘
```

Premises: items 1, 2 and 4 take `CStoreInv`, which is the blueprint premise
`bp.store.v1`. Items 3, 5 and 6 take no invariant. No statement is weaker
than its blueprint statement.

The claim "item 6 for a genesis or view result needs no separate lemma" is
correct, with one implicit step. `GridCO.confirmation_mem` gives
`B = .genesis ∨ B ∈ v.blocks`. For `v = actView st`, the second case is
directly an active block, so `actView_noVeto` applies. The genesis case
needs `actView_genesis_F` (with `CStoreInv`) or `block_genesis_preceq`
first. The veto test (`GridCO.gate`, Protocol.lean:474) reads only
`Block.compatible target h`, so this composition gives the third clause.
The plan does this composition in Task 11 (`cstoreInv_clock`, plan
line 2252). Task 7 does not need a lemma for it. See MINOR m4.

## Check 4 — the two SA bridges

- Premises are exactly the plan's. `clock_eq_saClock_offGate`: only `hg`.
  `clock_eq_saClock_gate`: `hs`, `hg`, `ht`, `hnew`. No fault, synchrony or
  FG-safety premise. The conclusions are the plan text.
- The premises are consistent for every slot: `proposalTime s = 4Δs` and
  `Δ > 0`, so `t = gateTime s` gives `hg` and `hs`.
- The proofs do not use the "freeze and release do not run at a gate tick"
  argument. `clockPre_eq` (ActView.lean:166) proves that `clockPre` is ONE
  `onView` step in all 8 branch cases. So the bridge is general.
- Use by later tasks: the offGate form and the gate form together cover each
  tick except a gate tick of a saved label. That case is `gateStep_saved`
  (Fields.lean:229); the plan gives it to composition T7 as the
  one-tick-per-public-time premise (plan line 2495). The `fastSet` argument
  is `actView (clockPre p st t)`, which equals the SA pre-gate view by
  `clockPre_eq` and `actView_onView`. Task 11 (`cstoreInv_process` for votes
  and rows, line 2251) needs the vote write sets; `admitHead_obligations`,
  `admitHead_genuine`, `admitHead_fastWrite`, `admitHead_base_stable` and
  `admitHead_base_blocks` supply them.

## Check 5 — lease instance, parameter indexing, imports

- Every lease-dependent GridCO lemma has the explicit instance:
  `@GridCO.admitVote_blocks`, `@GridCO.admitVote_stable`,
  `@GridCO.admitVote_obligations` (Fields.lean:26, 30, 34),
  `@GridCO.gate_blocks` (:119), all with `GridCO.slowLeasePolicy`.
  `saGate_genuine` uses `@GridCO.recordGenuine GridCO.slowLeasePolicy`
  (:174). `GridCO.admitVote` has no `[LeasePolicy]` argument; the Map.lean
  lemmas get it from a section `variable`, so the explicit instance is
  correct and harmless.
- No free `n` next to `p : Params`. Each declaration that takes
  `p : Params` uses `State p.n` or `GridCO.State p.n`. `saGate_blocks`,
  `release_blocks` and `saGate_genuine` take `p : SA.Params`, which has no
  `n`.
- Imports: Invariants — `Model.Frame`, `KitFG.Correspondence` (as Step 1).
  Fields — `Model.Frame`, `Proofs.BlockAncestry`, `GridCO.Proofs.Map`,
  `GridCO.Proofs.History` (allowed in `Proofs/`). ActView — only FGSA
  modules. The root imports all three files.
- File form (module header, `@[expose] public section`, `end …`, `end`) is
  correct. Statements are in `Statements/`, proofs in `Proofs/`.

## Findings

BLOCKING: none.

MAJOR: none.

MINOR:

- **m1** — `AvailableChainFGSA/Proofs/ActView.lean:106–113`
  (`actView_fields`). The docstring says "no other SA field", but the
  statement names 8 fields and omits `frozen`, `early`, `releaseSnapshots`
  and `goldfishRecord`. The blueprint needs only the signed pools and the
  stamps, and the statement has them. So the statement is not weaker than
  the blueprint. The text is the plan text. Fix: change the docstring, or
  add `actView st = { st.base with blocks := … }` (it is `rfl`).
- **m2** — `AvailableChainFGSA/Proofs/Fields.lean:234–237`
  (`fastSet_prefix`). The docstring says "non-genesis prefix", but the
  statement does not have `B ≠ .genesis`. The proof has the fact
  (`hB.2.1.1`). The text is the plan text. Fix: add the conjunct, or remove
  "non-genesis" from the docstring. Add the conjunct if Task 11 needs it for
  `fastOrigin_gateStep`.
- **m3** — `AvailableChainFGSA/Proofs/ActView.lean:212–215`
  (`clock_eq_saClock_gate`). `hs` and `hg` follow from `ht` because
  `Δ > 0` and `proposalTime s = 4Δs`. The premises are the plan's and are
  harmless. A caller must supply two premises that it can derive. Optional:
  add a wrapper that takes only `ht` and `hnew`.
- **m4** — plan line 1889 (execution note), item 6. "`actView_noVeto`
  covers every active block" is correct, but the genesis result of
  `confirmation_mem` is active only by `actView_genesis_F` (`CStoreInv`) or
  is compatible by `block_genesis_preceq`. Fix: add this clause to the note,
  so that Task 11 does not miss the genesis case.

## Notes for later gates (not G7 findings)

- `bp.store.v1` says `F, J ∈ T`. `KitFG.StoreInv` has `Fmem` and `F ⪯ J`,
  but no `J ∈ T` field. I did not check whether `pair` gives `J ∈ TF`. G11
  should check it against `bp.store.v1`.
- The base admission `GridCO.admitProposal` tests the same conditions as
  `blockAccepted` (slot bound, known parent, new block, parent slot, proposer
  slot). G10 checks `base_admitProposal_accepts` over the
  over-approximate `Reachable`.
