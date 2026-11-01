# Plan 1a report: framework gate and v1 catalog

_Closed 2026-09-29. Plan: `docs/plans/2026-09-28-phase1a-gate-catalog.md`
(approved by the user 2026-09-28). Range `47ad788..6c86590` on main._

## Result

Plan 1a is complete. The framework gate is in place, and the catalog
restates the two v1 bundles exactly:

- `ac43_iff`: the profile `ac-4.3` holds if and only if `AvailableChain`
  holds, for every validator set and environment with `E.Δ = I.Δ`.
- `strong1_iff`: the profile `strong-1` holds if and only if
  `StrongClaims` holds.

Known gap I2 (one early trigger serves every horizon) is closed: all 9
claims with a trigger other than `True` have a late trigger and a
`<claim>_trigger_late` lemma. Known gap I1 (a protocol with no input
passes the floor) is compiled in `AvailableChainRegistry/Gaps/NoInput.lean`
and stays open until plan 2. Known gap I9 (root collisions) is recorded in
design §12. No protocol library changed.

## Tasks and commits

```text
┌──────┬──────────────────────────────────────────┬────────────────────┬──────────────────────┐
│ Task │ Deliverable                              │ Commits            │ Review               │
├──────┼──────────────────────────────────────────┼────────────────────┼──────────────────────┤
│ 0    │ Lock and registry hardening (format only)│ 426009e, 6b7155a   │ pass; fixes verified │
│ 1    │ Claim domains, generic claims, late      │ 0e6898e            │ pass                 │
│      │ triggers, meaning pins                   │                    │                      │
│ 2    │ Profiles with shared constants           │ 1698a0c            │ pass, no findings    │
│ 3    │ HooksSound.deps_stable                   │ 44c09bb            │ controller (30 lines)│
│ 4    │ Facets as claim domains (DomainMap,      │ 99ffe0e            │ pass, 1 minor        │
│      │ StrongInstance, pull)                    │                    │                      │
│ 5    │ I1 witness clockChain                    │ 3c76e2b            │ pass, 3 minor        │
│ 6    │ Registry row kinds; the gate lock        │ 2f7a53c, 0b8ea16   │ pass, 6 minor, fixed │
│      │ regeneration                             │                    │                      │
│ 7    │ Standard tier (5 claims, Mono lemmas)    │ ba9dac9, 9e0b620   │ pass, 2 minor, fixed │
│ 8    │ Strong tier (5 claims)                   │ 843fad4, 4e6ddb9   │ pass, 2 minor, fixed │
│ 9    │ Profiles ac-4.3, strong-1; equivalences  │ 3e99183            │ pass, 2 minor (1b)   │
│ 10   │ Documents; full build                    │ b96a93f            │ pass, 1 minor        │
│ —    │ Final review fixes                       │ 6c86590            │ READY, 13 minor      │
└──────┴──────────────────────────────────────────┴────────────────────┴──────────────────────┘
```

Plan edits during execution: 8f31389 (lock diff hygiene, scratch-id rule)
and 5437521 (known gap I9 in Task 10).

## Checks at close

```text
┌──────────────────────────────────────────────┬──────┬──────────────────────────────┐
│ Check                                        │ Exit │ Result                       │
├──────────────────────────────────────────────┼──────┼──────────────────────────────┤
│ lake build --wfail (every default target)    │ 0    │ 3588 jobs (Task 10)          │
│ lake build --wfail Framework Registry        │ 0    │ 3358 jobs (final fixes)      │
│ scripts/CatalogLock.lean --check             │ 0    │ 249 lines, no change         │
│ scripts/Registry.lean --check                │ 0    │ REGISTRY.md is current       │
│ scripts/CheckFrameworkAxioms.lean            │ 0    │ 690 constants                │
│ bash scripts/check-fg.sh                     │ 0    │ all FG checks pass           │
└──────────────────────────────────────────────┴──────┴──────────────────────────────┘
```

No `sorry`, `admit`, `native_decide` or axiom is in the Framework, the
Registry or the three scripts.

## Lock history

The lock was written three times with removed or changed lines. Two of
these writes are the approved format change of Task 0 (426009e; 6b7155a
added the kind tag). One write, 2f7a53c, is the gate: 66 CHANGED, 1 REMOVED
(`Profile.claims`), 55 ADDED. The design §8 change log lists every name.
Tasks 7, 8 and 9 added lines only (+58, +40, +10).

## Decisions taken without the user

Each decision has a reason and a review in the ledger
(`claude-files/p1a-sdd/progress.md`).

- Task 3 was accepted on a controller review, because its diff has 30 lines
  and the kernel checks the proofs.
- `strongSafe` has `refutable := .run`. The rule is now in the
  `RefutationKind` docstring: the tag is the minimal refutation form that the
  claim admits.
- The regime adapters are in `Catalog/Profiles.lean`, not in `Mono.lean`.
- PHASE0-REPORT M7 is closed: each lock line hashes the set of its closure,
  and the cache holds only per-declaration data.
- Minor findings that stay open by decision: duplicated Block lemmas in
  `Gaps/NoInput.lean` (the gap module stays independent); the hard-coded
  `Candidate` path in `Registry.lean` (the lock guards it); inline v1
  inclusion triggers (a change is a CHANGED lock line); lock lines of
  derived instances (a possible cause of noise at a toolchain change); the
  plan text at line ~808 (the code docstrings are correct).

## Inputs for plan 1b

1. Compile the I1 witness with `excludes := false` and a run with delivery,
   against `Candidate × Eligible`.
2. `ac43` and `strong1` share `C` only by caller convention. The SA-PC
   statements (`AvailableChainSAPC/Statements/Contract.lean:27-34`) use one
   `C`. Add a combined profile, or a certificate pair with
   `pcS.shared.1 = pcA.shared`.
3. Add `ProfileCert ac43 I → Candidate I` (the first four entries, with
   `D := C.D_c`).
4. A `ProfileCert` of `ac43` needs `C.budget > 0`
   (`persistOutage_no_witness_at_zero_budget`). Thus the instance
   parameters need `η > 0` and a positive lifetime.
5. The SA-PC `receipt_acceptedRelay` re-check relies on `excludes = false`.
6. The KNOWN-GAP consumer contract: MATRIX.md, Pareto sets and the explorer
   ignore `KNOWN-GAP` rows.
7. The open PHASE0-REPORT §6 rows: Grid CO processed/excludes disjointness;
   Grid CO model facts outside the Registry namespace; the engine-generic
   lemmas to `Kit.Engine`; the Kit library split and one
   `block_preceq_trans`; Registry M2 and M3; Lock M8.
8. The plan-scope work: E4 excludes for Grid CO, SA and SA-PC; `Eligible I`
   as a structure indexed by the instance; run extension from every valid
   prefix; instance values and certificates for Grid CO, SA, SA-PC and L*;
   MATRIX.md.

The E5/E6 row (engine v2) belongs to plan 2. I9 needs a user decision with
a proper audit before any plan takes it.
