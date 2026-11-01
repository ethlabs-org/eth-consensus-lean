# Audit job: FG plan, filtered-base edit (short check)

You are an independent auditor. Check one proposed edit of the FG-module
implementation plan. Do not edit any file. This is a read-only task. Find
what is wrong, missing, unsound or mis-pinned. Do not rubber-stamp.

All paths are relative to `/Users/francesco/ethereum`.

## The edit

- Committed plan: `lean/available-chain/docs/plans/2026-09-28-fg-module.md`
  (commit 195d31a).
- Proposed plan (not committed):
  `/private/tmp/claude-501/-Users-francesco-ethereum/81138be2-3084-412a-91f7-34a802c39546/scratchpad/sdd-fg/fg-module-filtered.md`
- Diff: `…/scratchpad/sdd-fg/fg-module-filtered.diff` (same directory).

The edit adopts the "filtered base":
- one admitted, cumulative, parent-closed tree (no raw tree);
- `on_block` refuses a duplicate, a missing parent or `F ⋠ B` with no change;
- `reconcile_with_finality` writes only SA fields;
- `activeView` (the spec's `act(Σ)`) is AP data;
- the ids move to `fj.frame.v3` and `ap.headReachesLo.v5`;
- the executable reference is `alfs4`
  (`research/async-resilient-committees/tip-stability/spec/archive/fgsa-protocol-bd942ca0.tex`);
- the pin check rejects SUPERSEDED ids.

## Sources

- Spec `alfs4` (above); the analysis
  `research/async-resilient-committees/tip-stability/codex/filtered-base.md`
  (r161, §2 has the exact rule).
- Registry: `lean/available-chain/docs/FG-COMPOSITION.md` at HEAD (entries
  `fj.frame.v3`, `ap.headReachesLo.v5`).
- DC paper `research/healing/rewrite/consensus.tex` (on_block near line
  1720; Σ.hmax near line 864).
- Earlier audits of this plan: `lean/available-chain/docs/audit/fg-plan-*`.

## Check

1. Task 7: `Store`, `Store.init`, `on_block`, `update_finality`,
   `activeView`, against the `alfs4` spec, line by line. Report every
   difference.
2. `StoreInv` after the edit: is each remaining field preserved by the new
   `on_block`, both branches? Is any removed field still used by a later task
   (Tasks 7, 12, 13, 14)? In particular: `hmax = frontier TF` and
   `storeControls_eq_fjControls` with a cumulative tree, and `Fcar` and
   `pair` after an F advance, where stored blocks conflict with the new F.
3. Is a statement that the edit does not change now false or vacuous under
   the new definitions (Tasks 7, 12, 13)?
4. The pins: do the `fj.frame.v3` and `ap.headReachesLo.v5` clauses and line
   ranges in the edited Task 14 match the registry? Does the new
   SUPERSEDED check work, and can it give a false success?
5. Anything else in the diff that is wrong.

## Output

Write in ASD-STE100 Simplified Technical English. Give a findings table
(Unicode box-drawing, in a fenced `text` block) with columns: ID (P01, …),
severity (BLOCKING, MAJOR, MINOR), task, finding, evidence (file:line),
proposed fix. For each BLOCKING or MAJOR finding, add a short argument or a
counterexample. Then give a verdict: ADOPT, ADOPT WITH FIXES, or REVISE.

End with the exact final line:
`AUDIT COMPLETE: <n> blocking, <n> major, <n> minor`
