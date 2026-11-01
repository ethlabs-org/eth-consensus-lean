# Astra audit: Phase 2a engine v2 core plan

You are an auditor. Work read-only in `lean/available-chain` (paths relative to
it). Write prose in ASD-STE100 Simplified Technical English and tables in
Unicode box drawing inside fenced `text` blocks.

Object: `docs/plans/2026-09-29-phase2a-engine-v2-core.md`. Inputs: design
`docs/FRAMEWORK-DESIGN.md` (§1, §2 E1–E6 and Lift, §8 "Order after plan 1b",
§9), `docs/audit/phase2-order-check-report.md`, the survey
`claude-files/p2/survey.md`, the FG-SA T7 plan (`git show
a0f08c6:docs/plans/2026-09-29-fgsa-composition-t7-t1.md`), the I9 plan
`docs/plans/2026-09-29-i9-derived-roots.md`, the v1 engine
(`AvailableChainModel/Generic/*.lean`, `AvailableChainStatements/Generic/*.lean`,
`AvailableChainFramework/Hooks.lean`, `AvailableChainKit/Engine/*.lean`), and
`AvailableChainEngineV2/Sketch.lean`.

This is a "really major" change (a new engine that FG-SA builds on). Audit it
fully.

Questions:
1. Does 2a implement design §2 E1, E2 and E5 faithfully (dependent auth, no
   global n, one `act` for all duties, seat maps, CStar/Linked/SingleSeat,
   the atomic tick order, separation, isolation laws including the restore
   law's reservation and hook projection)? Name every deviation.
2. Are the reservations (restart constructor, `Durable`/`durable`/`restore`
   fields, `Run.input`, `restartFree`-based HooksSound stability) enough so
   that 2b and 2c never change a 2a type? Name any 2b/2c item that would.
3. D3: is `ProtocolSpec (In : Type)` with `Run.input : V → Time → In` the
   right input shape for the I1 fix (a floor claim that binds the proposal to
   the input, in the conclusion)? Compare with a spec field and with a
   per-label input. Does anything in the lift break with a type parameter?
4. The self-delivery lemma (Task 4 Step 3): are the hypotheses (`EmitOk`)
   sufficient and satisfiable? Is the delivery "after the tick phase at the
   same time" consistent with the v2 event order and `DeliveryWellFormed`
   (freshness, provenance)?
5. HooksSound v2 (Task 4 Step 2): is the restart-free interval form correct
   for E6 epochs (receipt facts reset at restart, design §2 E6)? Are the three
   `recordOwn_*` fields the right laws?
6. Does the 2a scope unblock FG-SA T7.0–T7.9 as the survey's §3 table claims?
   Name any T7 step that needs something not in 2a.
7. Task 6: may `AvailableChainFramework` import `AvailableChainEngineV2` under
   design §1's layers? Is the anchor + `lockedModulePrefixes` change sound, and
   does it change only by ADDED lines?
8. D8 and the worktree plan: can Tasks 0–2, 4, 5 run before the I9 merge
   without rework? Which of them read `Block`?
9. Anything missing for Phase 2 acceptance that 2a must prepare (finite traces
   of lifted instances, the Registry, the toy protocol)?

Output: `VERDICT: ADOPT | ADOPT WITH FIXES | REVISE | REJECT`, a findings table
(id, severity BLOCKING/MAJOR/MINOR, evidence file:line, fix), then answers
1–9. End with `AUDIT COMPLETE: <b> blocking, <m> major, <n> minor`.
