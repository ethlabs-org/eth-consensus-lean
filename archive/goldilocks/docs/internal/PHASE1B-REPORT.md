# Plan 1b report: E4 exclusion, protocol instances, Kit split

_Closed 2026-09-29. Plan: `docs/plans/2026-09-29-phase1b-instances.md`
(Astra audit and two re-checks, final ADOPT WITH FIXES; DC-simplify review
PASS). Executed under the user's rule for the night, as DC-simplify relayed
it: "act independently. Just get review from you and Astra before big
decisions, and a proper audit before really major ones." Range
`fe6c654..5f65103` on main._

## Result

Plan 1b is complete. The contract (`AvailableChainStatements`) did not
change, and the lock gained one ADDED line only.

- **E4 permanent exclusion.** Each protocol has an `excludes` that holds
  only for refusals that never end, and only for objects that are not
  processed. So `excludes` and `processed` are disjoint in every state.
  ```text
  ┌───────────┬────────────────────────────────────────────────────────────┐
  │ Protocol  │ `excludes`                                                 │
  ├───────────┼────────────────────────────────────────────────────────────┤
  │ Grid CO,  │ an unprocessed HEAD of an old label (`r + 1 < current`),   │
  │ SA        │ or of a seat that already equivocates at its label         │
  │ L*        │ an unprocessed HEAD of a seat that already equivocates;    │
  │           │ an unprocessed proposal wire whose block is already stored │
  │ SA-PC     │ none (`fun _ _ => false`): no refusal at the level of      │
  │           │ `processed` is permanent                                   │
  └───────────┴────────────────────────────────────────────────────────────┘
  ```
  Lean proves one direction against the handlers: an excluded object is
  refused for the rest of the run (`excludes_inert`, `excludes_stable`).
  The other direction is a plan 1c input.
- **WindowMargin.** The five Grid CO relay lemmas that used
  `excludes = false` by `rfl` now take the premise "not excluded up to the
  cutoff". `AvailableChainGridCO/Proofs/WindowMargin.lean` discharges it for
  every caller. No protected statement changed.
- **Hook facts** for all four protocols in their own libraries;
  `gridHooks`, `sapcHooks` and `lstarHooks` assemble `HooksSound` in the
  Registry.
- **Kit split.** `AvailableChainKit` (Core, Engine) and
  `AvailableChainEngineV2` (the L0 sketch). Namespaces did not change.
- **Instances and `holdsAt`.** `gridInst`, `saInst`, `sapcInst`
  (`StrongInstance`) and `lstarInst`; `ac43.holdsAt`, `strong1.holdsAt` and
  `core.holdsAt` for Grid CO, SA and SA-PC at `G = 1` for every parameter
  record, the `*_of_pos` forms for every `0 < G`, and
  `sapc_holds_shared` at `C := sapcConstants p G`. L* has an instance and no
  `holdsAt` theorem, because it has no contract proof.
- **Registry.** The row kind `profile-holds`; a narrow family rule; the
  status `UNSOUND(unsafe)`; the generated `docs/MATRIX.md`; a committed
  self-test under `scripts/registry-selftest/`.

`holdsAt` is not a certificate. It proves the claim propositions at one
constant, without inhabitation, so a row can be vacuous. MATRIX shows these
cells as `holds*`, with that sentence next to the table.

## Tasks and commits

```text
┌──────┬──────────────────────────────────────────┬─────────────────────────┬──────────────────────────┐
│ Task │ Deliverable                              │ Commits                 │ Review                   │
├──────┼──────────────────────────────────────────┼─────────────────────────┼──────────────────────────┤
│ 0    │ Kit and EngineV2 libraries               │ c79b473                 │ pass, 2 minor accepted   │
│ 1    │ Grid CO/SA excludes, WindowMargin, hooks │ 05cec33, cbac45b        │ pass, 3 minor (2 fixed)  │
│ 2    │ L* excludes (two clauses), hooks         │ 41750af, 1b34326        │ pass, 2 minor fixed      │
│ 3    │ SA-PC hooks                              │ 22e29b7                 │ pass, no findings        │
│ 4    │ core_holdsAt_of_ac43                     │ 06a5267                 │ pass, 1 minor (to T7)    │
│ 5    │ Instances and holdsAt theorems           │ 5fa3ad5, 3c339d5,       │ pass, 2 minor fixed      │
│      │                                          │ 15f7992                 │                          │
│ 6    │ profile-holds, family rule, MATRIX.md    │ efce412, f515f57        │ 1 major, 5 minor; fixed; │
│      │                                          │                         │ re-review clean          │
│ 7    │ Documents; full build                    │ e84658e                 │ pass, 1 minor (grep      │
│      │                                          │                         │ coverage; re-run clean)  │
│ —    │ Final review fixes                       │ 5f65103                 │ READY WITH FIXES,        │
│      │                                          │                         │ 2 major, 9 minor; re-    │
│      │                                          │                         │ review: all addressed    │
└──────┴──────────────────────────────────────────┴─────────────────────────┴──────────────────────────┘
```

## Checks at close

```text
┌──────────────────────────────────────────────┬──────┬──────────────────────────────┐
│ Check                                        │ Exit │ Result                       │
├──────────────────────────────────────────────┼──────┼──────────────────────────────┤
│ lake build --wfail (every default target)    │ 0    │ 3603 jobs (5f65103)          │
│ scripts/CatalogLock.lean --check             │ 0    │ no output; 250 lines, +1     │
│                                              │      │ against fe6c654              │
│ scripts/Registry.lean --check                │ 0    │ REGISTRY.md, MATRIX.md       │
│                                              │      │ current                      │
│ scripts/Registry.lean --selftest (3 files)   │ 0    │ compare with .expected; a    │
│                                              │      │ changed file gives exit 1    │
│ scripts/CheckFrameworkAxioms.lean            │ 0    │ 768 constants                │
│ bash scripts/check-fg.sh                     │ 0    │ all FG checks pass           │
│ SA and SA-PC Tests/Axioms.lean               │ —    │ output unchanged             │
│ grep sorry|admit|native_decide|^axiom over   │ —    │ 105 hits, all identifiers,   │
│ the 44 changed Lean files                    │      │ prose or script docstrings   │
└──────────────────────────────────────────────┴──────┴──────────────────────────────┘
```

`scripts/registry-selftest/Unsound.lean` has a deliberate `sorry` and
`unsafe def`; it is outside every Lake library (see the decisions).

## Lock history

One write: Task 4 (06a5267) added `core_holdsAt_of_ac43`. No line changed
or was removed. Every other checkpoint ran `--check` with no output and an
empty lock diff. The design §8 change log records the write.

## Decisions taken without the user

Each decision has a reason and a review in the ledger
(`claude-files/p1b-sdd/progress.md`).

- **I9 kept out of plan 1b.** The user decided I9 during execution (see
  "I9" below). It changes the shared `Block` type, so it is a contract and
  lock break, and it gets its own plan and audit.
- **Task 1 and 2 minors fixed by the controller** (docs and docstrings).
  One of these edits (1b34326) added a line of 111 characters. Commits
  1b34326, 22e29b7, 06a5267 and 5fa3ad5 therefore fail `lake build --wfail`
  over the default targets; 3c339d5 fixed it. The history stays. New rule
  for the controller: after any edit to a Lean file, run `lake build --wfail`
  over every default target before the commit.
- **The L* proposal clause matches `.proposer`/`.proposal`**, as `process`
  does. Other shapes fail `wellFormed`.
- **`sapc_holds_shared` names its constant** (`C := sapcConstants p G`)
  instead of the brief's `∃ C`, which did not use `G` and hid the witness.
  The named form is stronger.
- **Registry namespaces** `AvailableChain.Registry.<Proto>`; `sapcHooks`
  and `lstarHooks` were made in Task 5.
- **The family allowlist is syntactic**, with an explicit entry for
  `SAPC.Params` (an abbrev of `SA.Params`), not `whnfR`. Every admitted type
  is named.
- **Unsafe rows.** The Task 6 review found that an `unsafe def` row read as
  `LEAN`. The defect was older than plan 1b. It is fixed: such a row gets
  `UNSOUND(unsafe)`, and an unsafe witness exits 2.
- **A committed `sorry` fixture.** `scripts/registry-selftest/Unsound.lean`
  has a deliberate `sorry` and `unsafe def`. It is outside every Lake
  library, and its header says why: the self-test must show that the scanner
  marks them `UNSOUND`. AGENTS.md forbids `sorry` in committed proofs; this
  file is a detector test, not a proof. The user can overrule this.
- **The §8 lock log records the ADDED write**, as for plan 1a.
- **The Task 7 review and the final review ran in parallel**, with one
  merged fix round (Task 7 changed documents only).
- **Final review fixes.** The final review (READY WITH FIXES, 2 major, 9
  minor) found: F1, the §12 I9 note had only the user's point 1; F2, a
  Registry leak: a theorem about one parameter record could show as a
  family result on the family MATRIX line. Both are fixed (5f65103): the
  family binder must reach the instance argument, and a closed instance term
  shows in full on its own line. The same commit fixes F3–F9 and F11 (F8 in
  part: `votesAt_subset` is public; `eraseDups_nodup` stays), adds the
  self-test compare, and shows `at C = …` on the profile rows of
  REGISTRY.md.
- **Parked minors.** `eraseDups_nodup` is in Grid CO and, private, in L*;
  it moves to the Kit when plan 1c touches L*. Old tables that are not
  aligned (the L* table in MAP.md, design §0 and §11) stay.

## I9 (root collisions): decided by the user on 2026-09-29

Relayed by DC-simplify. Point 1: a derived root `root(B) := H(content)`, `H`
injective; a block carries its parent's root, not its own. Point 2: the
parent-root check is the store dependency lookup (`depsPresent` /
`blockKnown`); an unknown parent root is a temporary missing dependency, so
`excludes` gains no clause and SA-PC keeps its `rfl`; wire validity has no
root check, and wire forwarding waits for a P2P spec discussion. The plan's
"Shared sites with I9" table is superseded where it puts `rootOK` in
`wellFormed`; its list of sites stays an input. DC-simplify's Astra study
r203 (`codex/derived-root.md`, with `codex/scratch/r203-followups.md`) is
the input for the I9 plan.

## Order after plan 1b (decided 2026-09-29)

The user asked to reach Phase 2 as soon as possible, with both the engine
v2 extensions and the lift, and approved I9 before plan 1c. DC-simplify
agreed and added the FG-SA merge. Astra checked the order
(`docs/audit/phase2-order-check-report.md`, ADOPT WITH CONDITIONS, 0/2/2).

1. Merge `fgsa-composition` (DC-simplify and fgsa-impl run it: merge-tree
   against the current main, `--wfail`, `check-fgsa.sh`).
2. The I9 plan (derived roots), with a full audit. Input: r203
   (`research/async-resilient-committees/tip-stability/codex/derived-root.md`)
   in its root-only-wire variant, and `codex/scratch/r203-followups.md`.
3. Phase 2 in stages: 2a = the v2 core, E1, E2 (Linked), E5 (`recordOwn`),
   with the NoRestart, `durable` and input interfaces reserved (Astra O2);
   2b = the lift; 2c = E6, the toy protocol and the I1 fix with a versioned
   floor (Astra O1). FG-SA T7.0–T7.9 can start after 2a.
4. Plan 1c on engine v2.

The Phase 1 acceptance item "eligibility per migrated instance" (design
§8) is OPEN and moves to plan 1c (Astra O3). Until then MATRIX shows
`holds*` and no protocol certificate. Astra O4: the run-extension theorem
in the Kit is not a lock root; only the eligibility definitions need lock
planning.

Engine v2 input from the async session (N1, decided by DC-simplify under
the user's delegation, option (i-a)): a self-visible object can be
delivered to its own node at the emission timestamp, through the normal
`process`, after the tick phase. This needs no E5 change. The Phase 2 plan
states "`selfVisible` controls the private own-signature record. A normal
delivery to the emitting node may occur at the emission timestamp, after the
tick phase." and proves that such a delivery is admissible (wire,
dependency and freshness checks after `recordOwn`). Phase 2 acceptance adds
finite checked v2 traces for each migrated real instance (Astra).

## Inputs for plan 1c

1. `Eligible` with `EmitWellFormed`, `HandlerCoverage`, `Deliverable` and
   `RelayFeasible`, written with its consumer, the run-extension theorem
   from every valid prefix (locked on first write).
2. The other direction of E4 per protocol: an unprocessed object that the
   handler refuses, with a refusal that is not temporary, is excluded.
   RelayFeasible needs it.
3. Objects that never become deliverable: "deps never present" (for
   example a fabricated parent root, I9 point 2), a faulty HEAD with a far
   future label (all four protocols), and a PC whose paths never arrive
   (SA-PC). Deliverable and RelayFeasible must classify them as not
   deliverable.
4. Inhabitation runs for every horizon, at parameters with `η > 0` (every
   `Params` allows `η = 0`, and then the persistence regimes can be empty).
   Order (user, 2026-09-29): the I9 plan comes before plan 1c, so the
   inhabitation runs and certificates are built on derived roots and are not
   re-checked after a lock break.
5. Certificates, `ProfileCert ac43`, `candidateOfAc43 : ProfileCert ac43 I →
   Candidate I` with its first consumer, and the shared-C SA-PC certificate
   pair. `sapc_holds_shared` is a conjunction and has no row kind; the pair
   needs one.
6. The I1 witness against `Candidate × Eligible` (`clockInst`, and the
   `excludes := false` variant with delivery).
7. `holdsAt` does not read `I.hooks`. The run-extension theorem is the first
   consumer of `HooksSound`; it uses all five fields, or the plan records
   which it does not use.
8. The Registry self-test must cover every new row kind and MATRIX cell
   before plan 1c adds `cert` rows for the protocol instances.
9. Open from earlier plans: the Counter run and step helpers (PHASE0 §6
   Engine row), Registry M2 and M3, Lock M8.
10. `eraseDups_nodup` to the Kit if plan 1c touches L*.
11. Registry, from the final re-review: `headOf` is syntactic, so a
    declaration with a `let` or a beta-redex above `holdsAt` gives no row
    (an `unsafe` one of that shape is not flagged); normalize the type
    first. A closed instance term shows as printed, so use one spelling per
    record. A `profile-cert` whose value does not reduce to `ProfileCert.mk`
    shows `C = ?`.
12. The I1 floor is versioned (Astra O1): `candidateOfAc43` and the positive
    `clockInst : Candidate × Eligible` witness target the legacy floor.
13. `Cert.pull` needs a context equivalence. A one-way v2 → v1 simulation
    needs its own transport theorem.

The user's process rule: give no time estimates in days or weeks, only
scope.
