# Audit job: FG plan, Task 14 pin machinery after the re-check fixes

You are an independent auditor. Do not edit any file. This is a read-only
task. Find what is wrong, missing or unsound. Do not rubber-stamp.

Paths are relative to `/Users/francesco/ethereum`.

## Inputs

- Plan: `lean/available-chain/docs/plans/2026-09-28-fg-module.md` at HEAD.
  Only Task 14 and the Review status line changed in commit 80df98a (and one
  File-structure row after it). Diff: `git -C lean/available-chain diff fc63dc7 HEAD -- docs/plans/2026-09-28-fg-module.md`.
- Your previous re-check: `lean/available-chain/docs/audit/fg-plan-filtered-recheck-report.md`
  (Q01–Q03 major, Q05, Q06 minor).
- Registry: `lean/available-chain/docs/FG-COMPOSITION.md` at HEAD.

## Check

1. Are Q01, Q02, Q03, Q05 and Q06 fixed? Try your earlier counterexamples
   against the new design (structured `.ap`/`.external` ids, `.apData`,
   `.runFact`, one elaborated manifest with an `END` trailer, the shell
   reading only that manifest, `--names` for the axiom check).
2. Can the check still report success while a required datum escapes
   validation: a source hash, a pin id, an active reference, a historical id,
   or a pinned Lean name? Consider missing, duplicated, reordered, truncated
   and malformed manifest lines, and data that the emitter does not emit.
3. Do the coverage clauses still say what the registry entries say, after
   clauses with two ids were split in two?
4. Anything else in the diff that is wrong.

## Output

Write in ASD-STE100 Simplified Technical English. Give a findings table
(Unicode box-drawing, in a fenced `text` block) with columns: ID (T01, …),
severity (BLOCKING, MAJOR, MINOR), finding, evidence (file:line), proposed
fix. Add a short counterexample for each BLOCKING or MAJOR finding. Then
give a verdict: ADOPT, ADOPT WITH FIXES, or REVISE.

End with the exact final line:
`AUDIT COMPLETE: <n> blocking, <n> major, <n> minor`
