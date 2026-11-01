# WC corruption growth: remaining open items

Root integration and its import policy are applied. Assembly.Root exports
`fgsa_weakContinuationGrowthClaim` and imports both growth Assembly modules.
The API manifest includes the additive declarations. The two named Root
import exceptions and the Statements-order exception are applied.
The frozen FGSAClaims field and the original WC interface are unchanged.

## Non-vacuity fields (w6, closed)

`Tests/WeakContinuationGrowthNonVacuity.lean` adds a closed partial pair.
It adapts the W1 duty-engine generator to five validators. The source has
248 tick rounds and horizon 247 = GST + B_HF, with Delta = DeltaF = 1
and gap 4. The continuation retains validators 0, 1, and 2. It has
horizon 248 and actual suffix ticks at time 248. Faults rise from 0 to 2.
The test proves 5 < 3*2 and 2*2 < 5.

Closed proofs cover both schedules, the nonzero bounded endpoint,
retained local agreement, the full seat map, linked and fresh committees,
no restarts, proposer recurrence, source participation, the source fault
cap, the liveness bound, and continuation participation.

The full conjunction is closed by `nvGrowth_complete`. `nvGrowth_missing`
fills all eight fields of `MissingFields` for the concrete pair:

- `sourceValid`: closed in w6 by `nvGrowth_source_valid`. The W1 proof is
  parameterized by the positive validator count. Generic replay, dependency,
  origin, carriage, and wire lemmas certify the real five-validator prefix.
  A checked opaque certificate retains all execution-validity fields.
- `sourceRoots`: closed in w6 by `nvGrowth_source_roots`. The generic
  W1 final-store table covers delivered and held full named proposals,
  including their ancestors. The opaque certificate retains this proof.
- `sourceSync`: closed in w6 by `nvGrowth_source_sync`. Generic W1
  receipt proofs supply both family synchrony clauses. The HEAD/proposal
  and row delays are one. The opaque certificate retains this proof.
- `continuationValid`: closed in w6 by `nvGrowth_continuation_valid`.
  The continuation retains exactly nodes 0, 1, and 2 from a valid full
  five-validator reference run. Generic occurrence and full-state replay
  proofs preserve wire checks, dependencies, freshness, and both signature
  fields. The strict suffix still contains the tick at time 248.
- `continuationRoots`: closed in w6 by `nvGrowth_continuation_roots`.
  All retained stored bodies and delivered bodies occur in the reference
  named scope. Ancestry and full named identity are preserved.
- `continuationSync`: closed in w6 by `nvGrowth_continuation_sync`.
  Retained emission and receipt indices preserve both synchrony clauses,
  the original post-acceptance receiver guard, and the family deadlines.
- `pending`: closed in w6 by `nvGrowth_pending`. The generic duty-free-round
  lemmas prove that time 247 has no emissions or deliveries. Both original
  source guards and family deadlines remain in the theorem.
- `accountable`: closed in w6 by `nvGrowth_continuation_accountable`.
  Every continuation FinalityBlock occurs in the coherent reference run.
  Its zero-fault slashing bound covers the whole continuation.

`nvGrowth_complete_of_missing nvGrowth_missing` constructs both full records.
`nvGrowth_complete` has only propext, Classical.choice, and Quot.sound.
`nvGrowth_numbers` proves source faults 0, continuation faults 2, 5 < 6,
and 4 < 5. `nvGrowth_suffix_nonempty` proves the retained tick at time 248.
The source endpoint is 247 = GST + B_HF. The continuation endpoint is 248.
No non-vacuity gap remains for this witness. No statement defect was found.

## Reuse path (w6)

`GrowthGenerator` is in the existing non-vacuity test. TEST-USE forbids a
new import from one Tests module to another. The generic proofs therefore
stay in that file. No import policy or audit baseline is changed.

The W1 generator now has checked prefix proofs for every positive validator
count: `nvGen_prefix_execution`, `nvGen_prefix_roots`, `nvGen_prefix_sync`, and
`nvGen_prefix_accountable`. The source uses its fresh-only delivery generator.
The slot digest, five seats, endpoints, fault counts, and suffix remain.
The opaque certificate retains source validity, roots, and synchrony. It
retains all four reference-run fields for the next round. Generic retained
occurrence proofs then preserve the continuation fields.

The occurrence proofs preserve full local states at paired indices,
including the post-acceptance state. Root coverage includes delivered and
held full named bodies and their ancestors. All finality observations occur
in the valid, zero-fault reference run. The continuation uses two faults;
no one-third bound is assumed for it. Pending duties retain the original
source guards and deadlines.
