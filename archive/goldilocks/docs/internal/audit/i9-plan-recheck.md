# Astra re-check: I9 plan r3

Work read-only in `lean/available-chain`. ASD-STE100 prose; Unicode box-drawing tables in fenced `text` blocks.

Your audit `docs/audit/i9-plan-audit-report.md` gave REVISE (3 blocking, 5 major, 2 minor) on r1 (24ecaaa). The plan `docs/plans/2026-09-29-i9-derived-roots.md` is now r3 (HEAD). r2 folded in your findings and fgsa-impl's review (`docs/audit/i9-plan-fgsa-review.md`); r3 folds in DC-simplify's Claude review of r2 (`docs/audit/i9-plan-claude-review.md`). See "Audit disposition" at the end of the plan.

Check:
1. For each of your findings A01–A10: RESOLVED, PARTLY or OPEN, with plan line evidence.
2. The codec (Task 0): `epair a b := lpair (a * 2^bitLen b + b) (bitLen b)`, `lpair` in arithmetic form, the log-step `bitLen`, `tz` by fuel recursion. Are the laws and the size bound correct as stated? Is the fuel of 64 for `bitLen` and the fuel for `tz` adequate for the stated range, and is the fallback "prove only the two bounds" enough for `epair` injectivity and decoding?
3. FG-SA (Task 9): `packInner`, `packBody`, `appOf`, `rowsOk b rw := b.body == packBody (appOf b.body) rw`, `fgBlock` from `packInner`. Is this enough for the erasure law, `MetaInv.wireTree` preservation and `ContentAgree`, as the plan states?
4. The statement rule (classes (a)–(c) and the exception table): does any required change fall outside it?
5. The lock stop rule of Task 11 against `docs/plans/i9-lock-expected.tsv`.
6. Any new defect that r2 or r3 introduced.
7. Can execution start at Task 0?

Output: `VERDICT: ADOPT | ADOPT WITH FIXES | REVISE`, a findings table (id, severity, evidence, fix), then answers. End with `RECHECK COMPLETE: <b> blocking, <m> major, <n> minor`.
