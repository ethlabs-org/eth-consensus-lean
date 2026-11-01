# Astra check: move plan 1c after Phase 2

You are an auditor. Work read-only. Repository: `lean/available-chain`
(paths below are relative to it). Write prose in ASD-STE100 Simplified
Technical English and tables in Unicode box drawing inside fenced `text`
blocks.

## Proposal to check

The user wants Phase 2 (engine v2 and the lift, design §8 row 2) as soon as
possible. The proposed order is:

1. Close plan 1b (`docs/plans/2026-09-29-phase1b-instances.md`).
2. Merge the FG-SA branch `fgsa-composition` into main.
3. The I9 plan: derived roots (design §12, the I9 note with the user's two
   decisions of 2026-09-29).
4. The Phase 2 plan, in three stages: 2a = the v2 core, E1, E2 (Linked) and
   E5 (`recordOwn`); 2b = the lift (design §2, "Lift (v1 → v2)"); 2c = E6
   (restart), the toy Linked/self-visible/restart protocol, and the I1 fix
   (design §12).
5. Plan 1c after Phase 2, on engine v2: `Eligible`, the run-extension
   theorem, inhabitation, certificates, `candidateOfAc43`, and the shared-C
   SA-PC pair (see the "Plan 1c (outline)" section of the plan 1b file).

The design order (§8) puts "eligibility per migrated instance" in the
Phase 1 acceptance. Step 5 moves it after Phase 2. The reasons given: the
lift transports claim PROPOSITIONS, and eligibility is proved separately per
instance (design §2, Lift paragraph); `Eligible` and the run-extension
theorem are locked on first write, so writing them on v1 and again on v2
duplicates locked work; design §9 makes v2 the reference engine.

## Questions

1. Does any Phase 2 item (2a, 2b or 2c), as the design states it, need
   `Eligible`, the run-extension theorem, inhabitation or a certificate?
   Name each dependency with file:line in the design or the code.
2. Does the lift (every v2 run in the lifted legacy regime has a
   corresponding v1 run) need a v1 run-extension theorem or v1 eligibility?
   What does "certificate eligibility is proved separately per instance"
   require after the lift, and can it be proved on v2 for the lifted
   Grid CO, SA and SA-PC instances?
3. Does the I1 fix in Phase 2 ("a floor claim that binds the proposal to the
   input, and a refutation of `clockChain`", design §12) need `Candidate`,
   `Eligible` or certificates? The I1 witness is compiled in
   `AvailableChainRegistry/Gaps/NoInput.lean`.
4. Does anything already locked (`docs/catalog.lock`, `scripts/CatalogLock.lean`)
   or already in the Registry assume that plan 1c comes before Phase 2?
5. Which risks does the new order create? Consider: MATRIX shows only
   `holds*` rows (no certificates) for longer; `holds` can be vacuous; the
   FG-SA run lift (T7) goes on v2; a v1 result that nobody certifies could
   hide a defect that v1 inhabitation would show.
6. The async session asks that engine v2 allow a self-visible object to be
   delivered to its own node at emission, through the normal handler
   (research file
   `../../research/async-resilient-committees/tip-stability/codex/own-row-delay.md`,
   r201). Does this conflict with design §2 E5 (separation, the isolation
   laws, the hook projection)? If it does, state the smallest design change
   that allows it, and what it costs.

## Output

A verdict line `VERDICT: ADOPT | ADOPT WITH CONDITIONS | REJECT`, then a
findings table (id, severity BLOCKING/MAJOR/MINOR, evidence, fix), then the
answers to questions 1–6. End with `CHECK COMPLETE: <b> blocking, <m> major,
<n> minor`.
