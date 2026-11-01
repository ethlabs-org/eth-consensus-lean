# Audit job: short check of the FG plan's ALFS restructure

You are an independent auditor. You audited this plan twice
(`lean/available-chain/docs/audit/fg-plan-audit-report.md`, REVISE;
`lean/available-chain/docs/audit/fg-plan-reaudit-report.md`, ADOPT WITH
FIXES). Since your re-audit, the plan
`lean/available-chain/docs/plans/2026-09-28-fg-module.md` was restructured
because the FG-SA spec moved to DC's form ("ALFS"): the frame controls come
from the full store (live caches); the domain filter `filteredFrom` applies
to any block set (the HEAD uses the frozen voter tree); the F basis and J
carrier were deleted; the plan is pinned to the new registry entry
`fj.frame.v2` in `lean/available-chain/docs/FG-COMPOSITION.md`. Sources:
the archived ALFS spec
`research/async-resilient-committees/tip-stability/spec/archive/fgsa-protocol-183f2c40.tex`
and `research/async-resilient-committees/tip-stability/codex/fgsa-live-dc-port.md`.
Paths are relative to `/Users/francesco/ethereum`. Read-only; do not edit.

Scope: ONLY the restructured parts. Use `git -C lean/available-chain diff
62f6145 HEAD -- docs/plans/2026-09-28-fg-module.md` to see them. Check:

1. `storeControls`, `Controls`, `fjControls`, `filteredFrom`, `storeFrame`,
   `acceptViable`, `update_finality`, `on_block` (with the new guards),
   `Store.init` against the archived ALFS text, line by line.
2. The central lemma `storeControls_eq_fjControls` and `StoreInv` (with
   `Fcar`, which replaces the F basis): true, sufficient, preserved by
   `on_block`? Give a counterexample if not.
3. Which frame form each lemma uses (the plan's table): is each lemma true
   in the form it states? In particular `Fmove_filtered` for any block set,
   `filteredFrom_viable_child` (needs an ancestor-closed set),
   `fjFrame_D_nonempty` and `storeFrame_feasible`.
4. Did the restructure reopen any G01–G12 or H01–H06 finding, or drop a
   lemma that later work (SA instance, Kit.Compose) needs?
5. Pins to `fj.frame.v2`: clauses, line ranges, sources, the AP-data
   clauses.

## Output
ASD-STE100. A findings table (Unicode box-drawing in a fenced `text`
block): ID (K01, …), severity (BLOCKING, MAJOR, MINOR), task, finding,
evidence (file:line), fix. A short argument for each BLOCKING or MAJOR
finding. A verdict: ADOPT, ADOPT WITH FIXES, or REVISE.

End with the exact final line:
`AUDIT COMPLETE: <n> blocking, <n> major, <n> minor`
