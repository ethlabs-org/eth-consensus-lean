# P-H1 Round 9 fixture status

The positive NonVacuity/HealingRun fixture is extended to horizon 310.
Its actual generated event list has 311 batches. original_events_prefix proves
that the complete old 305-batch event list is a prefix. generator_tick_eq
proves that the changed horizon leaves the generated tick operation equal.
No FG state, certificate or lease is assigned as a desired run field.
The common Shared/HealingFixture data and HealingPackages fixture are unchanged.

The extended run proves ExecutionValid, receipt-root collision freedom,
Linked/CStar, RestartsAtWakes, PartialSynchronyBy, RecoverySleep₂ and the real
nonempty source body at label 2. joined_full_horizon proves
recoveryStart + B_HF < 310; the complete budget is 309.
This closes the positive execution/extension obligation owned by P-H1.
It does not prove TPerm or an end-to-end Healing claim. Those still need P5
and the P-H2/P-As contract assembly.

The four adversarial replays remain OPEN/P-H1. Their exact parameters,
certificate prefixes, event facts, horizons and conclusions are unchanged
in P-H1.round7-fixtures.md. Each replay must prove all the following together:

- The complete finite event list with parent-first named bodies, distinct
  scoped roots, original signed certificates, actual admissions and emissions.
- ExecutionValid, NamedReceiptRootCollisionFree, Linked/CStar,
  RestartsAtWakes, and PartialSynchronyBy at every bounded ready anchor.
- RecoverySleep₂ with the stated faulty bound, horizon and joinedGap.
- The actual gate, saved-result, lease, proposal, HEAD and output facts in
  the Round 7 table, plus the failed old Transfers or early repair conclusion.

The required runs are healing-contract section F with k=3; tperm-decision
with k=4; its n=7 slow run; and early-lease section 5's split batch.
For the split batch, keep the same prefix and prove separate quiet extensions
to 2070 and 2080. Numerical JoinedStart tests are not execution replays.
The k=8 N4 expiry test remains numerical. Its cleanup route is the later
full-batch release theorem, not an assumption that every old lease expired.
