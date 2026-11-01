# G11 review — Task 11 (composite store invariant, K4 core; F monotone; K1)

Reviewer: Opus (independent; did not write the code). Date: 2026-09-29.
Commit: `5e62302` (branch `fgsa-composition`). Scratch worktree at
`5e62302`, with `.lake/build` copied and the outputs of `Statements/Store`
and `Proofs/StoreInv` deleted so that they compile again.

## Verdict

**PASS WITH FIXES.** 0 BLOCKING, 1 MAJOR, 5 MINOR.

All 20 planned declarations (2 statements and 18 theorems) have the plan
text exactly. No statement is weaker than its blueprint statement. No
statement has a new premise. The build and the axiom check are clean.
The MAJOR finding is one GridCO lemma with a `[LeasePolicy]` argument that
elaborates at the default GRID instance. Its statement does not read the
instance, so the result is correct. But the Global Constraints rule
forbids this form, and the execution note says that the lemma has no
lease argument, which is false.

## Validation

```text
┌──────────────────────────────────────────────┬──────────────────────────────────────┐
│ Check                                        │ Result                               │
├──────────────────────────────────────────────┼──────────────────────────────────────┤
│ bash scripts/check-fgsa.sh (scratch wt)      │ exit 0; 3373 jobs; Statements.Store  │
│                                              │ and Proofs.StoreInv rebuilt ("Built")│
│ root imports, native eval, direct imports,   │ pass                                 │
│ import closure, Q1/Q5 grep                   │                                      │
│ CheckFGSAAxioms (in the script)              │ 708 constants, 370 theorems; only    │
│                                              │ propext, Classical.choice, Quot.sound│
│ CheckFGSAAxioms --expect (21 Task 11 names + │ all present and clean, except        │
│ J_mem, process_F_mono, clock_F_eq)           │ process_F_mono, clock_F_eq: NOT      │
│                                              │ CHECKED (absent; see m1)             │
│ sorry / admit / axiom grep (2 files)         │ none                                 │
│ Statement compare (script, whitespace- and   │ 20/20 equal to the plan code block   │
│ docstring-normalized)                        │ (Task 11, Steps 1–2)                 │
│ Docstrings vs plan                           │ equal where the plan has one         │
│ Lease-instance scan (Lean meta script over   │ see M1                               │
│ every constant of the two modules, values    │                                      │
│ included)                                    │                                      │
└──────────────────────────────────────────────┴──────────────────────────────────────┘
```

Lease-instance scan result (instance argument of each GridCO/SA constant
with a `[LeasePolicy]` binder, in `Proofs/StoreInv` and `Statements/Store`):

```text
┌────────────────────────────────┬──────────────────────────────────────┐
│ Constant                       │ Instance used                        │
├────────────────────────────────┼──────────────────────────────────────┤
│ GridCO.gate_target_origin      │ slowLeasePolicy                      │
│ GridCO.confirmation_mem        │ slowLeasePolicy                      │
│ GridCO.gate_eq_writeKeys       │ slowLeasePolicy                      │
│ GridCO.gate, gateWriteKeys,    │ slowLeasePolicy                      │
│ recordGenuine, admissionLevels │ (admissionLevels.eq_1 is generic)    │
│ GridCO.ghostWalk_mem           │ gridLeasePolicy (DEFAULT)  ← M1      │
│ GridCO.RootInjectiveBelow      │ no policy argument                   │
└────────────────────────────────┴──────────────────────────────────────┘
```

## Carried items — rulings

**(a) `J ∈ T` (G7, G10).** Not dropped; not a weakening. `CStoreInv` has no
`J ∈ TF` field, and `KitFG.StoreInv` has none either. `J_mem`
(`Proofs/StoreInv.lean:31–43`) proves `st.fg.J ∈ st.fg.TF` from
`CStoreInv` alone: `pair` with `lexMax_spec` gives `J = σ[K].J` for some
`K ∈ TF`, and `derive_anchors_preceq` with ancestor closure puts it in TF;
if no candidate exists, `lexMax_of_none` gives `J = genesis ∈ TF`. The
blueprint (01 §4.1) says the same thing: "Use exactly the fields of
KFG.StoreInv … The selected J is in T by chain order and ancestor
closure." So `StoreInvariant` plus `J_mem` gives the clause "F, J ∈ T" at
every reachable state. The statement has the full strength of
bp.store.v1's per-state clauses. See m2 for the tag.

**(b) Inv0 circularity (G10).** None. `cstoreInv_accepted_pre`
(`:156`) builds `h0 : Inv0 p st` from the PRE-state hypothesis
`h : CStoreInv p st`, and gives it to `accepted_base_facts` and
`base_admitProposal_accepts` (both take `Inv0 p st` of the pre-state,
`Admission.lean:138, 240`). `baseTree` of the post-state comes from
`base_admitProposal_accepts` (blocks `= old ++ [b]`), `fg_on_block_accepts`
with `KitFG.update_finality_TF` (TF `= insert B TF`), and `eraseFG_fgBlock`
(`:184–196`), as G10 asked. `cstoreInv_admitBlock` (`:204–261`) and
`cstoreInv_process` (`:264–274`) use only this route.

**(c) `hL` and due leases (G9 m2).** The premise form is correct.
`admitBlock_reconcile_harmless` (`:634–647`) has
`hL : ∀ row ∈ st.base.obligations, Compatible row.1 (eraseFG F')`: every
lease row present in the store, including a due lease that the next tick
expires. This is the only true form of K1 (G9 m2). The pre-state
obligations equal the pre-reconcile obligations (`hob`), so the premise is
on the right list. K7 (Clean) can supply it: blueprint 02 §5.3 item 5
makes the new F compatible with "every existing I1 result and I3
target/body/S", and I3 (02:432) says each present target has its actual
gate origin. The origin argument (a prefix of a successful gate result,
kept by release, expiry and reconcile, which only delete) does not read
the deadline, so a due lease is covered. For the P1 form of K7 (only B is
protected), the run layer must use the per-target reconcile facts of
Task 9 (`reconcile_obligations`), not this lemma. The G9 m2 report line
is still not in the plan (see m5).

**(d) `cstoreInv_of_sublist`.** Sound and not weaker than needed.
`CStoreInv` (`Statements/Invariants.lean:54–65`) reads `fg` (fields `fg`,
`rootInj`; F in `saCompat`, `fastOrigin`), `base.blocks` (`baseTree`,
`Smem`), `base.obligations` (`saCompat.1`, `leaseKeys`), `base.genuine`
(`saCompat.2.1`, `genuineKeys`; `savedGenuine` in `fastOrigin`, `fastDom`,
which reads only `genuine`: `savedGenuine_congr`), `base.stableRecord`
(`Smem`) and `fastWrite`. No other field. Only `saCompat.1` and
`leaseKeys` read the obligations, and both hold on a sublist. At each use
(head vote `:268`, row `:272`, `normalizeS` `:112`, `clockPre` `:291`) the
supplied facts are equalities or a filter sublist from the Task 7 field
lemmas. No use needs more.

**(e) Non-vacuity.** `StoreInvariant` quantifies over the inductive
`Reachable` (init, any tick, any delivery). `cstoreInv_init` (`:118`)
proves `CStoreInv p (initial p.n)` for every `p`, and `storeInvariant`
(`:540`) is the induction over the three constructors. The statement is
not vacuous, and `Reachable` is an over-approximation, so the invariant
is, if anything, stronger than the run form.

## Findings

### BLOCKING

None.

### MAJOR

- **M1 — `GridCO.ghostWalk_mem` at the default lease instance.**
  `AvailableChainFGSA/Proofs/StoreInv.lean:743`
  (`GridCO.ghostWalk_mem _ _ _ _ (liveRoot p st)`). `#check` gives
  `@GridCO.ghostWalk_mem : ∀ [GridCO.LeasePolicy] (tree …) …`: the
  section `variable [LeasePolicy]` of `GridCO/Proofs/RecordSlots.lean:11`
  is included (it has no dependency, and the file disables the
  unused-variable linter). The instance is therefore synthesized as
  `gridLeasePolicy`. The statement does not read the instance (`ghostWalk`
  and `ghost` take none); I checked this in Lean with `rfl` between the
  `slowLeasePolicy` and `gridLeasePolicy` applications. So
  `fgHead_stored` is correct. But the Global Constraints rule (plan line
  232) says: "If it has a `[LeasePolicy]` argument and it is used for the
  SA base, apply it as `@GridCO.<lemma> GridCO.slowLeasePolicy …`", and the
  execution note (plan line 2268) says "`ghostWalk_mem` … ha[s] no lease
  argument", which is false. Fix: write
  `@GridCO.ghostWalk_mem GridCO.slowLeasePolicy _ _ _ _ (liveRoot p st)` and
  correct the note.
  Related plan-text error (for the coordinator, not the implementer): plan
  line 232 says that `GridCO.admitVote_blocks` and `GridCO.confirmation_mem`
  "have no policy argument". `#check` shows that both have
  `∀ [GridCO.LeasePolicy]`. The code already applies both with
  `slowLeasePolicy` (`Fields.lean:26`, `StoreInv.lean:421`), so the code is
  correct, but the rule text can mislead later tasks. Correct line 232.

### MINOR

- **m1 — Two Produces names are absent.** Plan line 2175 lists
  `process_F_mono` and `clock_F_eq`. Neither exists (grep; the axiom
  `--expect` reports NOT CHECKED). Their content is the two conjuncts of
  `fMonotone` (`(fMonotone p st).1 o`, `(fMonotone p st).2 t`), so nothing
  is lost, and no later task names them. But the execution note does not
  report the omission. Fix: add the two one-line corollaries, or add a
  report line.
- **m2 — `J_mem` carries a blueprint clause but is tagged `[helper]`.**
  `Proofs/StoreInv.lean:30`. It is the proof of the bp.store.v1 clause
  "F, J ∈ T" (item (a)). Fix: tag it `[bp bp.store.v1; K4]`, and let the
  Task 13 K table cite `storeInvariant` + `J_mem` for that clause.
- **m3 — `fMonotone` has no docstring.** `Proofs/StoreInv.lean:577`. Global
  Constraints ("Faithfulness", plan line 231) ask for a blueprint id in
  each proof docstring. The plan code block has the same gap. Fix:
  `/-- [bp bp.store.v1; K4] -/`.
- **m4 — Execution note omits two helpers.** `cstoreInv_clockPre`
  (`:289`) and `cstoreInv_gateStep` (`:509`) are not in the note's helper
  list (plan line 2268). Add them.
- **m5 — "live lease" in the K1 docstring; G9 m2 line still open.**
  `Proofs/StoreInv.lean:629–633` says "every live lease"; `hL` is over
  every row of `obligations`, due leases included. The docstring comes from
  the plan. Fix: add "(every row of `obligations`, due leases included;
  G9 m2)". The G9 m2 report line for Task 13 ("K1 `hL`: live = present in
  `Σ.lease` (`obligations`), including due leases that the next tick
  expires") is not yet in the plan; record it with the G9 dispositions.

### Observations (no action)

- `fastOrigin_gateStep` (`:524`) says "A fresh gate …", but the statement
  covers every gate (saved labels go through `normalizeS`). The statement
  is stronger than the docstring; the text is from the plan.
- `saGateWriteKeys_level` (`:341`) and `saGate_cases` (`:359`) take
  `(p : SA.Params) {n : Nat}`. M11 names FGSA `Params`; these helpers
  follow the signature of `SA.gate`/`GridCO.gate` themselves, and they are
  applied to `actView st : GridCO.State p.n`. Not an M11 violation.
- bp.store.v1 clauses outside Task 11: "T is cumulative" and "old
  states/stamps are unchanged" are Task 12 (`process_cumulative`,
  `clock_cumulative`, `MetaInv`). The tick part of "pair and H monotone"
  has no named lemma; it follows from `clock_fg`. The K table of Task 13
  should cite these.
- Imports: `GridCO.Proofs.RecordSlots`, `GenuineHistory`, `Roots` are in
  the allowed list and in the disclosed transitive set (plan lines
  222–223). The closure check passes.
- Model coverage by the proof: the four `process` cases and both `clock`
  branches are handled; refused blocks rewrite to the identical state
  (`admitBlock_refused`).

## Blueprint map (Task 11 statements)

```text
┌───────────────────────────────┬──────────────────────────────┬───────────────────┐
│ Lean                          │ Blueprint                    │ Ruling            │
├───────────────────────────────┼──────────────────────────────┼───────────────────┤
│ StoreInvariant/storeInvariant │ bp.store.v1 per-state clauses│ equal (J∈T via    │
│                               │ (KFG.StoreInv fields)        │ J_mem)            │
│ FMonotone/fMonotone           │ bp.store.v1 "F monotone"     │ equal             │
│ process_hmax_mono,            │ bp.store.v1 "H, (j,J)        │ equal (delivery); │
│ process_pair_mono             │ monotone"                    │ tick by clock_fg  │
│ fg_step_cases                 │ bp.frame.v1 projection       │ equal             │
│ storeControls_eq              │ bp.frame.v1 controls         │ equal             │
│ viewRootInj_TF                │ bp.carrier.v1 local, DQ2     │ equal             │
│ actView_eq_image              │ bp.activeView.v1             │ equal             │
│ saCompat_gateStep,            │ bp.activeView.v1,            │ equal             │
│ fastOrigin_gateStep           │ bp.leaseOrigins.v1 (fastW.)  │                   │
│ admitBlock_reconcile_harmless │ bp.reconcile.v1 K1           │ stronger (equal-  │
│                               │                              │ ities); hL = G9 m2│
│ fgBlockOf_spec, deepest_spec, │ DQ13, DQ2, G3 m3 helpers     │ equal to plan     │
│ fgHead_stored,                │                              │                   │
│ rootInjectiveBelow_base,      │                              │                   │
│ leaseOf_eq_deadlineOf         │                              │                   │
└───────────────────────────────┴──────────────────────────────┴───────────────────┘
```

## Cleanup

The scratch worktree `/Users/francesco/.claude/jobs/22f59f85/tmp/g11wt` was
removed after the checks (`git worktree remove --force`). The two scan
scripts stay in `/Users/francesco/.claude/jobs/22f59f85/tmp/g11/`.
