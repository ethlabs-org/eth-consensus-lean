# I9 final branch review (Astra), 2026-09-29

You are an adversarial reviewer. Read-only: do not edit files, and do not build.

Repository: /Users/francesco/worktrees/available-chain-i9, branch i9-derived-roots.
Review the whole branch against main: `git diff main...HEAD` (the merge base diff).
Plan: docs/plans/2026-09-29-i9-derived-roots.md (read "Global Constraints", the
statement rule, the exception table, D1–D9 and Tasks 9–11). A pre-final audit
of Tasks 0–8 is in docs/audit/i9-branch-audit-0-8-report.md (READY WITH FIXES
0/1/0; fixed by a named exception). Focus on what that audit did not cover:
Task 9 (FG-SA: packInner, packBody, appOf, rowsOk in wellFormed and
blockAccepted, fgBlock, eraseFG with encFGBody, MetaInv.wireTree, contentAgree,
rootInj_all, Tests/Support.lean), Task 11 (docs/catalog.lock, the §8 lock log),
and whole-branch consistency.

Questions:
1. Soundness: does any theorem become vacuous or weaker than its name and
   docstring claim (for example, a premise that can never hold, or a
   statement that silently lost a conjunct)? Compare changed statements with
   main.
2. Statement rule: is every changed public statement in class (a), (b) or (c)?
   List any change outside the rule.
3. D9: is `rowsOk` exactly the same function in `wellFormed` and in
   `blockAccepted`, and can an honest proposal fail it?
4. Codec: are `epair_inj`, `bitLen` and `tz` total and correct for all inputs,
   with no bounded fuel that truncates?
5. Lock: does docs/catalog.lock change only the 91 names of
   docs/plans/i9-lock-expected.tsv?
6. Tests: does any test in FG-SA, Grid CO, SA, SA-PC, L* or KitFG pass only
   vacuously after the root change (for example, a refusal test whose input is
   never processed)?

Output: a verdict line `VERDICT: MERGE | MERGE WITH FIXES | DO NOT MERGE`, a
findings table (ID, severity blocking/major/minor, file:line, claim, evidence,
fix) as a Unicode box-drawing table in a ```text block, and a last line
`REVIEW COMPLETE: <b> blocking, <M> major, <m> minor`. Be concise. Write in
ASD-STE100 Simplified Technical English.
