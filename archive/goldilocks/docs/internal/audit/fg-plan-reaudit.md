# Audit job: FG-module plan, second audit (re-audit)

You are an independent auditor. Re-audit the implementation plan
`lean/available-chain/docs/plans/2026-09-28-fg-module.md` after its
revision. Your first audit is `lean/available-chain/docs/audit/fg-plan-audit-report.md`
(REVISE, 2 blocking, 8 major, 2 minor: G01–G12). The research session's
answers to that audit are in `lean/available-chain/log.md` (tail) and in
the registry `lean/available-chain/docs/FG-COMPOSITION.md` (commits
27fa4b9, 9c4df0a and later: the twoChanges formal reading, comp.outputNesting.v1,
fj.frameFeasible.v1, ap.headReachesLo.v1). Do not edit any file. Read-only.

Use the same sources and audit items as the first audit job
`lean/available-chain/docs/audit/fg-plan-audit.md` (read it). In addition:

1. For each of G01–G12, give a disposition: FIXED, PARTLY FIXED, NOT
   FIXED, with evidence (plan file:line).
2. Check the new material for errors, in particular:
   - the three F-move lemmas (Fmove_below, Fmove_atTop, Fmove_atFrontier)
     against the registry's formal reading of fj.twoChanges.core.v1 and
     against your G02 counterexample (now a `decide` test);
   - the store invariant (StoreInv, fBasis_duty) and the admitted tree;
   - the client record invariant (RecordInv, createRow_noSelfSlash,
     clientRun_noSlash) against the spec's finality_pair and DC's client;
   - the evidence-bit form of twoChanges (effFrame_of_bits, twoChanges_count)
     with non-nested views and the normalized root;
   - the new hypotheses `2 ≤ m` and `ViewRootInj`: needed, sufficient,
     and consistent with the registry text;
   - the pin checker's negative tests and the clause-level coverage table.
3. Say whether the plan's six open questions block implementation or can
   be settled during it.

## Output

ASD-STE100 Simplified Technical English.
1. The G01–G12 disposition table (Unicode box-drawing in a fenced `text` block).
2. A findings table for NEW issues (IDs H01, H02, …): ID, severity
   (BLOCKING, MAJOR, MINOR), task, finding, evidence (file:line), fix.
3. For each BLOCKING or MAJOR finding, a short argument or counterexample.
4. A verdict: ADOPT, ADOPT WITH FIXES, or REVISE, and why.

End with the exact final line:
`AUDIT COMPLETE: <n> blocking, <n> major, <n> minor`
