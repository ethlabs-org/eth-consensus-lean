# Re-check job: Phase 1b plan revision (13fabba)

You audited `lean/available-chain/docs/plans/2026-09-29-phase1b-instances.md`
at commit `0d8d995` (your report: `docs/audit/phase1b-plan-audit-report.md`,
REVISE 1/4/4). A second review (`docs/audit/phase1b-plan-claude-review.md`,
0/3/13) also ran. The plan was revised at commit `13fabba`; its new section
"Audit disposition" maps every finding to a change. See the diff with
`git -C /Users/francesco/ethereum/lean/available-chain diff 0d8d995 13fabba -- docs/plans/`.

This is a focused, read-only re-check. Do not edit any file. Paths are
relative to `/Users/francesco/ethereum/lean/available-chain`. You may
elaborate small scratch files under `/private/tmp` with `lake env lean`
(run `pgrep -fl lean` first; 3 slots; no full build).

Check:
1. For each of your findings P1b-01 … P1b-09: is it resolved by the
   revision? Say RESOLVED, PARTLY, or NOT, with one sentence and evidence.
2. For the second review's majors M1 (a case split with
   `head_excluded_before_equivocates` at CrossView.lean:84 and
   ProposalViewRelay.lean:91), M2 (the premise
   `∀ u ≤ cutoff, excludes (stateBeforeTime u reader) o = false`) and M3
   (the L* clause `o ∉ proposals ∧ b ∈ blocks`): is each fix sound and
   sufficient?
3. The new registry family rule (Task 6 Step 1: a data binder gives
   `LEAN (family)`, a Prop binder gives CONDITIONAL). Is it sound? Can a
   data binder hide an unproved assumption (for example a binder whose type
   is a structure carrying a Prop field, or a function type into Prop)?
   Propose the exact rule if not.
4. Did the revision introduce any new defect?

Output: a table (Unicode box drawing in a fenced `text` block) with one row
per item: item, status, evidence, fix if needed. Then new findings, if any,
with severity. End with `VERDICT: ADOPT | ADOPT WITH FIXES | REVISE` and
`RECHECK COMPLETE: <b> blocking, <m> major, <n> minor` (new or unresolved
only). ASD-STE100 Simplified Technical English.
