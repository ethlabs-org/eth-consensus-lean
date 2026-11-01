# Audit job: FG-module implementation plan (DC-fj)

You are an independent auditor. Audit the implementation plan
`lean/available-chain/docs/plans/2026-09-28-fg-module.md`. The plan
formalizes in Lean 4 the fixed finality-gadget module "DC-fj": the FG of
decoupled consensus (DC), without SG and grades, with the FJ root rule in
place of NJ. The module exports the FG frame (Z, lo, D, viability) and
static FG facts. Head selection (the walk, score and eligibility) is AP
data, constrained by `ap.headReachesLo.v1`. The plan was reviewed by the
research session that owns the FG results; its findings were applied.
The user will decide on the plan after your audit. Find what is wrong,
missing, unsound, infeasible or mis-pinned. Do not rubber-stamp. Do not
edit any file. This is a read-only task.

## Sources (read what you need; cite file:line)

All paths are relative to `/Users/francesco/ethereum`.

- The plan: `lean/available-chain/docs/plans/2026-09-28-fg-module.md`.
- The framework design: `lean/available-chain/docs/FRAMEWORK-DESIGN.md`
  (§7.1, §7.2 define the module scope: fj only, FG-only, frame only).
- The FG registry: `lean/available-chain/docs/FG-COMPOSITION.md` (pinned
  statements, SHA-256 of sources, "Lean plan" column).
- The research session's review of an earlier plan version and its
  follow-up notes: `lean/available-chain/docs/audit/fg-plan-async-review.md`.
- The FJ source: `research/async-resilient-committees/tip-stability/`
  `codex/fj-redteam.md` (r148) and the spec
  `research/async-resilient-committees/tip-stability/spec/fgsa-protocol.tex`
  (locate the exact paths if they differ; the plan cites them).
- DC paper: `research/healing/rewrite/consensus.tex` (FG in the fork
  choice, `update_finality`, `get_fg_root`, `viable_tree`).
- DC Lean model: `lean/decoupled-consensus/verified-consensus/`
  (`DecoupledConsensusModel/Protocol/*`, the proofs the plan cites).
- The existing Lean project and style:
  `lean/available-chain/` (AGENTS.md, lakefile.toml, the new
  `AvailableChainFramework/`), and the Phase 0 plan
  `lean/available-chain/docs/plans/2026-09-28-framework-phase0.md` for
  the plan conventions.

## Audit items

1. **Scope.** Does the plan stay FG-only and fj-only? Does anything port
   DC's NJ recovery or DC's AP walk (Goldfish GHOST, majority,
   current-slot eligibility)? Does any statement assume facts that are
   AP data or run facts without stating them as hypotheses?
2. **Faithfulness to the fj rule.** Check the definitions (frame: H, the
   lex pair with F ⪯ J, the contest test, Z/lo table, viability, D;
   the chain state transition without NJ; `update_finality`; the FG
   client and `createRow`) against r148 and the spec, line by line.
   Report every difference.
3. **Statements vs pinned registry text.** For each Lean statement that
   pins a registry id, check that it states the pinned math (or that
   its coverage is marked partial, with the missing part named). Check
   ids, source files, line ranges and the SHA-256 policy. Check that no
   statement depends on `δ_t > 0`.
4. **DC port.** Are the DC lemmas that the plan says "port unchanged"
   really independent of NJ and of the SG? Are the cited DC files and
   lines right (verified-consensus at b97b902)? Is the own `FGBlock`
   type sound, and does the port remain feasible with it?
5. **Proof feasibility.** For each task, is the statement provable as
   written in Lean 4 (v4.30.0-rc2, Mathlib)? Flag false or vacuous
   statements, missing hypotheses (for example `fjFrame_D_nonempty`'s
   extra hypotheses `hVw`, `hHF`), and circular dependencies between
   tasks. Give counterexample sketches where a statement is false.
6. **Plan quality.** Task order and interfaces (Produces/Consumes),
   tests that actually test (the review-focus tests, the `decide`
   examples), no placeholders, the pin-check script, build targets, the
   workspace rules (no `sorry`/`native_decide`, the Mac Lean throttle,
   commits per task).
7. **Missing pieces.** What the module needs for later `Kit.Compose` and
   the SA instance (for example the view-monotonicity lemmas, the
   F-basis lemma, `ap.headReachesLo.v1` feasibility) that the plan
   omits or states in a form that later work cannot use.

## Output

Write the report in ASD-STE100 Simplified Technical English.

1. A findings table (Unicode box-drawing, in a fenced `text` block) with
   columns: ID (G01, G02, …), severity (BLOCKING, MAJOR, MINOR), task,
   finding, evidence (file:line), proposed fix.
2. For each BLOCKING or MAJOR finding, a short paragraph with the
   argument or a counterexample sketch.
3. A table: registry id → Lean statement → coverage verdict (full,
   partial-correct, wrong).
4. A verdict: ADOPT, ADOPT WITH FIXES, or REVISE, and why.

End with the exact final line:
`AUDIT COMPLETE: <n> blocking, <n> major, <n> minor`
