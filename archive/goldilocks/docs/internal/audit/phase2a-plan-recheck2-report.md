VERDICT: REVISE

```text
┌──────┬──────────┬──────────────────────────────────────────────────────┐
│ Item │ Status   │ Plan line evidence                                   │
├──────┼──────────┼──────────────────────────────────────────────────────┤
│ A02  │ RESOLVED │ 124: emission, indices, honesty, HooksSound and       │
│      │          │ receiver-state equation are explicit.                │
│ A03  │ RESOLVED │ 139: recordOwn has field equality or prefix premises.│
│ A05  │ RESOLVED │ 39–41, 190, 208–211: full HooksSound cannot use a     │
│      │          │ NoRestart alternative.                               │
│ A07  │ RESOLVED │ 176–179: build, then coverage, then lock; reject a   │
│      │          │ missing anchor.                                      │
│ N01  │ RESOLVED │ 80–84, 132: create the KitV2 root before its build.  │
│ N02  │ PARTLY   │ 140–146: the prefix clock bound is fixed, but some   │
│      │          │ restore cases remain false. See below.               │
│ N03  │ RESOLVED │ 97: first matching tick; agreement requires          │
│      │          │ ScheduleWellFormed.                                  │
└──────┴──────────┴──────────────────────────────────────────────────────┘
```

Line numbers refer to the [r3 plan](/Users/francesco/ethereum/lean/available-chain/docs/plans/2026-09-29-phase2a-engine-v2-core.md). Checked at `d8c7509`. No files changed; no Lean build run.

**2. D9 and Task 4 Step 3**

The following assignments are sufficient, with the v1 premises and the new `recordOwn` laws:

- `stateBefore_invariant`: **both** `hrestore` and `hrestore_now`. Lines 141–142 jointly require these.
- `stateBefore_now_le_event`: `hrestore_now`.
- `stateBefore_now_mono`: `hrestore_now` plus interval `restartFree`.
- `stateBefore_stable`: interval `restartFree`.
- `delivery_now_ge_public`, `stateBefore_tick_eq_stateBeforeTime`, `ownRecord_fold`: `NoRestart`.
- The remaining schedule, prefix-read and other-node lemmas need no restore premise.

**M1 — MAJOR; N02 remains partly open.** Two clock-suite statements need correction:

- `stateBefore_stable_clock` also needs **`hrestore` or interval `restartFree`**. The [v1 statement](/Users/francesco/ethereum/lean/available-chain/AvailableChainKit/Engine/EngineClock.lean:175) propagates an arbitrary predicate from an intermediate state. A restart can clear that predicate while resetting `now` to zero. Thus `hrestore_now` alone, as assigned at plan line 142, is insufficient.
- The unchanged [stateBefore_now_source](/Users/francesco/ethereum/lean/available-chain/AvailableChainKit/Engine/EngineClock.lean:23), included by “port each lemma” at line 138, is false under `hrestore_now`. `Time` is `Int`: restore may set `now := -1`. This satisfies `now ≤ 0`, but the value is neither zero nor an earlier tick time. Weaken its first alternative to `now ≤ 0`, or require exact zero for this lemma.

**M2 — MAJOR; missing field restore laws.** Lines 138–144 remove the general `NoRestart` fallback but assign no adequate restore premises to the field lemmas:

- [clock_field_origin](/Users/francesco/ethereum/lean/available-chain/AvailableChainKit/Engine/EngineClock.lean:208) needs restore to add no rows. Otherwise restore can insert a row when the source predicate is `False`. Require membership inclusion; field equality also suffices.
- [stateBefore_field_prefix](/Users/francesco/ethereum/lean/available-chain/AvailableChainKit/Engine/EngineClock.lean:249) needs `field st <+: field (restore (durable st))`, or interval `restartFree`. Otherwise restore can delete a row.

The `recordOwn` fixes resolve A03, but they do not cover these restart cases.

**3. Task 3 Steps 3–4**

Step 3 is sufficient **with `EmitOk` as a premise**, as intended. `HooksSound.recordOwn_processed` preserves post-clock freshness through the fold. The state equation transfers the checks to the delivery prefix. Tick membership supplies signature provenance.

**M3 — MAJOR; the append form at line 125 is false as stated.** It omits `HooksSound P`, which `ExecutionValid` does not contain: see [its constituent conditions](/Users/francesco/ethereum/lean/available-chain/AvailableChainStatements/Generic/Conditions.lean:86).

Counterexample: use one honest node, horizon zero and one tick at zero. Emit a self-visible object. Let post-clock `processed` be false, but let `recordOwn` set it true. Let wire and dependency checks pass and let the object carry nothing. The original run is `ExecutionValid`, and `EmitOk` holds. The appended delivery fails freshness.

Add `HooksSound P`, or at least its required record preservation law. With that addition, the append form works. Sortedness follows from the key bound; the last-local-event premise excludes a duplicate delivery; old prefixes and emissions remain unchanged.

**4. New defects**

M2 and M3 are new defects in r3. M1 is the remaining N02 defect in the revised clock-premise assignments.

**5. Can Tasks 0–4 start now?**

Tasks **0–2 can start**. Task 3 Step 3 can proceed. Correct M3 before Step 4, and correct M1–M2 before the Task 4 port. Tasks 0–4 are therefore **not ready as one unchanged plan**.

RECHECK COMPLETE: 0 blocking, 3 major, 0 minor