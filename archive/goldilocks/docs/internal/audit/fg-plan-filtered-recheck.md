# Audit job: FG plan, filtered-base edit, final state (re-check)

You are an independent auditor. Check the FINAL state of one proposed edit
of the FG-module implementation plan, after the fixes of two earlier
reviews. Do not edit any file. This is a read-only task. Find what is wrong,
missing, unsound or mis-pinned. Do not rubber-stamp.

All paths are relative to `/Users/francesco/ethereum`, except the scratch
directory `SD` =
`/private/tmp/claude-501/-Users-francesco-ethereum/81138be2-3084-412a-91f7-34a802c39546/scratchpad/sdd-fg`.

## Inputs

- Committed plan: `lean/available-chain/docs/plans/2026-09-28-fg-module.md`
  (commit 195d31a).
- Proposed final plan (not committed): `SD/fg-module-filtered.md`; diff
  against the committed plan: `SD/fg-module-filtered.diff`.
- The first two reviews of the earlier draft, whose findings the author
  says are applied:
  - Astra: `lean/available-chain/docs/audit/fg-plan-filtered-check-report.md`
    (P01–P04);
  - async session: `lean/available-chain/docs/audit/fg-plan-filtered-async-review.md`
    (M1, M2, minors 1–6, small items).
- Controller rulings on those findings:
  - M1: `on_block` tests the parent-slot order `B.parent.slot < B.slot` in
    Lean. The future-slot bound, the proposer signature and the row-round
    check form one FG admission input contract.
  - M2: add `on_block_TF_subset` and `update_finality_TF`.
  - P01: pin ids come from the elaborated Lean data (`scripts/FGPinIds.lean`),
    not from text.
- Spec `alfs4`:
  `research/async-resilient-committees/tip-stability/spec/archive/fgsa-protocol-bd942ca0.tex`.
- Registry: `lean/available-chain/docs/FG-COMPOSITION.md` at HEAD
  (`fj.frame.v3`, `ap.headReachesLo.v5`).
- DC paper `research/healing/rewrite/consensus.tex` (on_block near line
  1720).

## Check

1. Is each finding of the two earlier reviews correctly applied? Name any
   that is not applied, or applied wrongly.
2. The new and changed Lean in Task 7: `on_block` (four refusals, in the
   spec's order), `Store`, `Store.init`, `StoreInv`, `activeView`,
   `activeView_subset`, `on_block_TF_subset`, `update_finality_TF`. Are the
   statements true, with correct proof guides? Is `StoreInv` still preserved
   in both branches, with the new parent-slot refusal?
3. The `decide` examples built with `on_block` (B1′, then B1, B2, B3): do
   they model reachable stores, and do they test what they claim?
4. The pin machinery in Task 14: `idTokens`, `emitIds`, `scripts/FGPinIds.lean`
   and the shell check. Can a superseded id in a pin, an `.ap` reference or
   an `.external` reference still pass? Can the check succeed on missing or
   partial input? Are the failure tests sufficient?
5. The `fj.frame.v3` and `ap.headReachesLo.v5` clauses, line ranges and
   coverage labels (Trees, on_block, reconcile, the two head clauses)
   against the registry and `alfs4`.
6. Is any statement that the edit does not change now false or vacuous
   (Tasks 7, 12, 13)? Anything else in the diff that is wrong.

## Output

Write in ASD-STE100 Simplified Technical English. Give a findings table
(Unicode box-drawing, in a fenced `text` block) with columns: ID (Q01, …),
severity (BLOCKING, MAJOR, MINOR), task, finding, evidence (file:line),
proposed fix. For each BLOCKING or MAJOR finding, add a short argument or a
counterexample. Then give a verdict: ADOPT, ADOPT WITH FIXES, or REVISE.

End with the exact final line:
`AUDIT COMPLETE: <n> blocking, <n> major, <n> minor`
