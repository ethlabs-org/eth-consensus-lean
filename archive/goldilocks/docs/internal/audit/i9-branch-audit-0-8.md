# Astra audit: I9 branch, Tasks 0–8 (pre-final)

Work read-only in the git worktree `/Users/francesco/worktrees/available-chain-i9` (branch `i9-derived-roots`). ASD-STE100 prose; Unicode box-drawing tables in fenced `text` blocks.

## Object

The implementation of the I9 plan `docs/plans/2026-09-29-i9-derived-roots.md` (r4) from a5aaf3c to e42bb37 (Tasks 0–8: codec, Block with a body, Kit/EngineV2/Framework, Grid CO, SA, SA-PC, L*, Witnesses, Registry, SimplexFG, KitFG). Task 9 (FG-SA) is still running; do not review FG-SA. Per-task reviews passed; ledger and reports: `.superpowers/sdd/2026-09-29-i9-derived-roots/` in that worktree (`progress.md`, `task-N-report.md`, `task-N-review.md`).

## Questions

1. Codec (`AvailableChainModel/Objects/Codec.lean`): are all laws unrestricted and correct as stated; is every evaluated-path function kernel-efficient (structural recursion on input-dependent fuel; no `Nat.log2`/`Nat.size`/well-founded recursion); is the fuel-sufficiency argument complete?
2. `Block.root_injective`, `parent_mem_iff_root`, `parent_mem_and_iff_root`, `rootInjective_all`: correct and as the plan states?
3. Statement rule: list every theorem whose statement text changed between a5aaf3c and e42bb37 (use `git diff a5aaf3c e42bb37` on `theorem`/`lemma` lines) and classify each as class (a), (b), a named exception, or OUTSIDE the rule.
4. Fixtures: any fixture that now passes for a different cause than before (root order, coinciding blocks, refusal by a different check)?
5. `encFGBody` (with `fgBodyTag`) and `FGBlock.root`: is `(eraseFG B).root = B.root` provable by structural induction once FG-SA's `eraseFG` uses `encFGBody x rows` (Task 9)? Any obstacle?
6. Anything else that should block the merge.

## Output

`VERDICT: READY | READY WITH FIXES | NOT READY`, a findings table (id, severity BLOCKING/MAJOR/MINOR, file:line, fix), then answers 1–6. End with `AUDIT COMPLETE: <b> blocking, <m> major, <n> minor`.
