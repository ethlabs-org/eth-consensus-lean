# Audit job: Phase 1b plan (E4 exclusion, protocol instances, Kit split)

You are an independent auditor. Audit the implementation plan
`lean/available-chain/docs/plans/2026-09-29-phase1b-instances.md`. It
changes protocol libraries: it gives Grid CO (and SA, which is Grid CO under
another lease policy) and L* a real `excludes` hook (design §2 E4), adds a
premise to five Grid CO relay lemmas, moves about 30 engine-generic lemmas
from the Grid CO library into a new Kit library, builds framework `Instance`
values for four protocols, and proves the `ac-4.3` and `strong-1`
propositions for them. The plan claims that the contract
(`AvailableChainStatements`) needs NO change and that the catalog lock has
NO break. The user is asleep; under the session rule this plan runs only
after your audit and a second review. Your job is to find what is wrong,
unsound, infeasible, inconsistent with the design, or not future-proof,
before the plan runs. Do not rubber-stamp. Do not edit any file. This is a
read-only task.

## Sources (read what you need; cite file:line)

All paths are relative to `/Users/francesco/ethereum/lean/available-chain`.

- The plan (above). Its section "Findings that change the premises" makes
  seven factual claims from a code survey. Check each one against the code.
- The design: `docs/FRAMEWORK-DESIGN.md` v7, §2 E4 (lines 111–197), §3, §5,
  §6, §8. The user APPROVED §0–§6 and §9.
- `docs/PHASE0-REPORT.md` §6; `docs/PHASE1A-REPORT.md` ("Inputs for plan
  1b"); `docs/CONTRACT.md` (lines 283–299: the receipt-relay change).
- The contract: `AvailableChainStatements/Generic/{Conditions,Regimes}.lean`,
  `AvailableChainStatements/Strong/Regimes.lean`.
- Grid CO: `AvailableChainGridCO/Model/Protocol.lean` (`admitVote` 300–309,
  `admitProposal` 313–325, `processed`/`handles` 349–368, `gridCO` 566–589),
  and the five relay lemmas the plan names (ClockBounds.lean:139,
  ProposalDelivery.lean:139, CrossView.lean:17, Paths.lean:288,
  Proposals.lean:102) and their callers (ProposalViewRelay.lean and the
  others).
- The existing variant: `AvailableChainRegistry/GridCOHooks.lean`
  (`gridExcludes`, `gridCOx`, `gridCOx_hooks`).
- SA: `AvailableChainSA/Model/Protocol.lean`. SA-PC:
  `AvailableChainSAPC/Model/{Protocol,Handlers}.lean`,
  `Proofs/ReceiptRelay.lean`. L*: `AvailableChainLStar/Model/Protocol.lean`.
- The framework: `AvailableChainFramework/{Hooks,Instance,Profile}.lean`,
  `Facets/Strong.lean`, `Catalog/{Core,Profiles}.lean`;
  `scripts/{CatalogLock,Registry}.lean`.
- The I9 root proposals that share code with this plan:
  `/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/root-nonce.md`
  (r196) and `root-design.md` (r194).

Toolchain: Lean 4 v4.30.0-rc2, Mathlib v4.30.0-rc2. You may elaborate a
small scratch file with `lake env lean <file>` in that directory (the Mac
allows 3 Lean processes: run `pgrep -fl lean` first). Do not run a full
`lake build`, and do not write inside the repository; put scratch files
under `/private/tmp`.

## What to check

1. **The premises.** Is the contract really unaffected? Confirm that no
   regime uses `AcceptedObjectRelay` or `HealthyAcceptedObjectRelay`, that
   `PartialSynchrony` and `HealthyPrefixDelivery` have the exclusion
   exemption, and that the design's E4 coverage gap (a faulty HEAD released
   in the last Δ of its window takes the run out of every regime) is closed
   today. If it is NOT closed, say exactly which regime field still carries
   it: the plan would then be missing a contract change.
2. **Grid CO `excludes` (Task 1 Step 1).** Is it exactly the set of
   permanent refusals of a not-yet-processed HEAD? Check both directions
   against `admitVote`, `process` and `handles` (carried raw HEADs). Is the
   refusal really permanent (the clock only goes forward; equivocation
   evidence only grows) in every state reachable in a run? Is a processed
   HEAD never excluded, and a proposal never permanently refused outside
   `wellFormed`? Would this `excludes` make any existing Grid CO/SA proof
   false, not only harder? Consider a HEAD accepted by an honest source in
   the last Δ before `proposalTime (r+2)`, and a third HEAD of an
   equivocating faulty seat. Find the callers that relay faulty HEADs and
   say whether their conclusions already allow "∨ equivocates".
3. **WindowMargin and the relay premise (Task 1 Steps 4–5).** Is adding the
   premise "not excluded at the deadline" to the five lemmas sound and
   sufficient? Can every caller discharge it (cutoffs ≤ gateTime r = t_r+6Δ
   for label-r HEADs vs. exclusion at t_r+8Δ)? Is the interface right for a
   later I9 root guard: if I9 extends `excludes` to bad-root proposals,
   do only WindowMargin lemmas change, or also the relay lemmas and the SA-PC
   `receipt_acceptedRelay` `rfl` sites?
4. **SA-PC `excludes = false` (finding 2).** Is it really the correct E4
   classification? Look for any SA-PC refusal that can never end
   (HEADs, proposals through `GridCO.admitProposal`, PCs). If one exists,
   the plan is wrong to leave SA-PC unchanged.
5. **L* (Task 2).** Is "third equivocation, not processed" the exact
   permanent refusal? Anything else permanent?
6. **Kit split (Task 0).** Are the files the plan moves really free of Grid
   CO declarations? Does the move break the constraint of the FG-SA branch
   (no move of `AvailableChainGridCO.Proofs.{GenuineHistory, History, Map,
   RecordSlots, Roots}`)? Does it change any lock line?
7. **Instances and `holdsAt` (Task 5).** Do the `Instance` values type-check
   as sketched (field order, `sa p` and `p.engine.Δ = p.Δ`, `sface` =
   `sapcInterface p` for `strong1_iff`)? Is `holdsAt` honestly presented as
   "not a certificate" in the registry and MATRIX (Task 6)? Is anything in
   MATRIX able to show `holds` as if it were `cert`?
8. **The split into 1b and 1c (finding 5).** Is deferring `Eligible` and the
   run-extension theorem to 1c sound, or does 1b need any part of them to
   be consistent (for example, does the E4 `excludes` need `RelayFeasible`
   to be defined first to know it is right)? Is anything that 1c needs
   missing from 1b's interfaces?
9. **Lock and layering.** Confirm the plan's claim of ADDED lines only
   (Task 4) and no change otherwise. Confirm that a protocol library cannot
   import `AvailableChainFramework` today, so hook facts must be stated
   in the protocol library and assembled in the Registry.

## Output

Write a table (Unicode box drawing in a fenced `text` block) with one row
per finding: id (P1b-NN), severity (BLOCKING / MAJOR / MINOR), task,
finding, evidence (file:line), proposed fix. Then give a counterexample or
a scratch-file result for each BLOCKING and MAJOR finding. Then the
answers to questions 1–9, one short paragraph each. End with a verdict
line: ADOPT, ADOPT WITH FIXES, or REVISE, and the final line
`AUDIT COMPLETE: <b> blocking, <m> major, <n> minor`. Write in ASD-STE100
Simplified Technical English.
