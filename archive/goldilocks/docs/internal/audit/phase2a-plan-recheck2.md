# Astra re-check 2: Phase 2a plan r3

Work read-only in `lean/available-chain`. ASD-STE100 prose; Unicode box-drawing tables in fenced `text` blocks.

Your re-check `docs/audit/phase2a-plan-recheck-report.md` gave REVISE (0 blocking, 5 major, 2 minor) on r2. DC-simplify's review `docs/audit/phase2a-plan-claude-review.md` gave ADOPT WITH FIXES (0/1/9). The plan `docs/plans/2026-09-29-phase2a-engine-v2-core.md` is now r3 (commit d8c7509; see the second table in "Audit disposition").

Check, briefly:
1. For each of your open items (A02, A03, A05, A07, N01, N02, N03): RESOLVED, PARTLY or OPEN, with plan line evidence.
2. D9 and Task 4 Step 3 (restore premises `hrestore`, `hrestore_now`; `NoRestart` only where named). Are the premise assignments per lemma correct against the v1 proofs in `AvailableChainKit/Engine/{EngineClock,Execution,Stable}.lean`? Is any lemma still false with its stated premises?
3. Task 3 Step 3 (`selfDelivery_admissible` premises) and Step 4 (`ExecutionValid.snoc_selfDelivery`): are the premises enough, and is the append form true as stated against the v2 `ExecutionValid` text of Task 2?
4. Any new defect that r3 introduced.
5. Can Tasks 0–4 start now?

Output: `VERDICT: ADOPT | ADOPT WITH FIXES | REVISE`, a table, then answers. End with `RECHECK COMPLETE: <b> blocking, <m> major, <n> minor`.
