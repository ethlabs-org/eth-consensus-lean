# Clean lane W2a

## Current status — continuation 6

Base: `861ca1f8`. This includes `43733fe` and the slot/root PC relay fix.
The signed ack, HEAD, and proposal cases handle the added PC branch.
Whole-PC relay uses slot and target root. It does not assume that PC
carriage gives full target-block equality.

The following claims are proved. Clean claims are exported by
`Clean/Export.lean`. The C5 and M5 PC claim adapters are exported by
`Assembly/Small.lean`, which combines both lanes:

- C6 `CleanInvariantClaim`: all 14 fields, by joint induction with
  earlier-ack coverage. The successor uses the preceding invariant.
- C5 `AvailableMonotoneClaim`: inclusive reads through the full clean cut.
- `CleanDisseminationClaim`, `PCSACleanSafetyClaim`, and
  `PCSACleanInclusionClaim`.
- M1 `CleanResultsNonemptyClaim`, M2 `CleanResultsChainPendingClaim`,
  M3 `CleanDisseminationPendingClaim`, and M5 `LeaseBelowRecordClaim`.
- `CleanBlockReceiptClaim`, with the exact after-ticks target reader.

Each claim uses only `propext`, `Classical.choice`, and `Quot.sound`.
C3 positive-slot dissemination and PC snapshot stamps remain proved.
No existing claim statement was changed in continuation 6. The pending
claim declarations were copied verbatim from the outage branch.

### False pending claims

`CleanHeadsAbovePendingClaim` and `CleanHeadsPastCutClaim` are false
as stated. `Tests/PendingHeadCounterexample.lean` checks one full run:
five honest nodes, one faulty node, and delay 2. A carried faulty HEAD
reaches node 3 at time 17. Its relay deadline, 19, is outside cut 18.
At time 18, node 3 chooses Z. At the label-1 gate, time 20, node 0
returns X. X and Z are siblings. The run also passes CLEAN checks at
cut 12, so it refutes the past-cut statement strictly after the cut.

The executable audit checks all finite run premises. Kernel-checked
trace identities connect its cached reads to the exact claim readers.
Requiring the source gate by the cut is sufficient for the general
result-to-HEAD argument. That change would not supply the requested
past-cut guarantee. The outage lane needs a corrected statement.

### Remaining scope

C9 `StrongIncludedClaim` is closed (`pcsa_strongIncludedClaim`,
Assembly/Outage) by formation part 4 only: `pcsa_clean_honestProposal_stamped`
(Clean/Export, helpers in Clean/C9*.lean) stamps the proposal PC before the
freeze from predecessor C6 and Clean delivery, and C8 persistence with
`j₀ = u + 1` gives the strong output. C7 `FormationClaim` was not changed.

All module commits passed the full pre-commit list. There are no Lean
warnings, forbidden proof placeholders, or unaccepted equation exports.
The later sections preserve the earlier findings and proof plans. Their
old OPEN labels describe the state at the time; this section is current.

## Earlier findings and module plans

Base: `92a4673`, on `31fa4d7`. Stage 1 only.
Claim changes: the approved r4.3a correction to `CleanInvariantAt.roots`
and the approved `0 < s` premise of `PCDisseminationClaim`.
It now requires compatibility with honest results, not arbitrary honest HEADs.

## Resolved statement defect: C3 at slot zero

`AvailableChainPCSAProofs/Tests/ZeroSlot.lean` proves `refutes_unrestricted_C3`:
`¬ UnrestrictedPCDisseminationClaim p` (the former statement). This is a full run counterexample. It proves
`Clean₂`, `FaultsBelowQA`, and `StageOneFrame`, not only store behavior.
The theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.

Take one honest node, one seat, no faults, Δ = 1, and cut = horizon = 3.
The run has these six events, in order:

1. Tick at 0. The slot-zero proposer emits nothing.
2. Tick at 1. The node emits its slot-zero HEAD on genesis.
3. Deliver that HEAD at 1.
4. Tick at 2. The node emits its slot-zero ack on genesis.
5. Deliver that ack at 2.
6. Tick at 3. The ack pool has the ack. The PC set is empty.

The emitted ack quorum has size 1 = q_A. Delivery is strict: 1 < 2 and
2 < 3. The only label with e_j ≤ 3 is j = 0; its honest participation is
1 > 0. There are no proposal bodies, rows, restarts, or root collisions.
The proof checks schedule, delivery, signatures, committees, and frame.

`ackFor` permits this N target. `PC.wellFormed` requires `0 < slot` and a
non-genesis target. The lead approved `0 < s` for C3. The test now preserves
the former statement and proves `positive_slot_excludes` for this witness.
Positive-slot C3 is now proved; this test does not refute it.

Other slot statements were checked. No further statement change is needed:
- Formation already requires `FormationPrem.slotPos`.
- CleanDissemination requires prefix coverage, not a PC at slot zero.
  The genesis target is below every block.
- StrongIncluded requires an emitted honest proposal. The slot-zero
  proposal duty emits nothing.
- PCSnapshotStamp is equality of sets, including empty sets at slot zero.

Proved support:

- `Collect`: seat selection preserves all input seats without repeats; a pooled
  quorum assembles and collects the exact resolved target. Collection leaves
  a saturated store; collection of a saturated store changes nothing.
  `Saturation` proves this at every event state and discharges hFreezeKeep.
  Exact run-level receipt is proved by `BodyReceipt`.

- `AckStore`: decoded ack admission under the slot, root, and seat-cap checks;
  ack-pool preservation through every delivery and clock step.
- `AckRun`: ack-pool preservation between event indices without restarts;
  the after-ticks PC set at the freeze equals the strict pre-time PC set.
- `Shared/CleanPC`: CL4 count facts for the same label and later labels;
  strict score dominance from the Generic quorum inequality.
- `StepGate`: compatible PCs allow prefix lock writes; compatible live locks
  let the guard pass; compatible PC admission deletes no lock; a passed gate
  writes `GridCO.advance S X` to S.

These are exported by `Clean/Export`. They are not proofs of the open claims.

CI read-step support is exported:
- `StepVote`: an honest positive-slot HEAD extends its duty root; a block
  below that root is below the HEAD. A slot-zero honest HEAD is genesis.
- `StepAck`: an honest ack's full target is held, has the exact slot, and
  passes holdsN in the duty state. Its block is in the collision scope.
These do not yet provide the joint CI record or the composing induction.

## OPEN facts

- C6 (`CleanInvariantClaim`): generic HEAD/body receipt, stamp transport,
  exact resolution, proposal-pool provenance, and concrete voter list
  decomposition are proved. `ProposalReceipt` identifies the earlier
  accepted proposal and its carried raw HEAD handlers. `WalkInputs`
  proves the frozen/carried split and support membership in raw inputs.
  The next modules connect these facts to actual CL1–CL4 counts and
  retained paths. Then prove common proposal/voter views, label zero,
  and the Vote/Ack/Gate/PC steps of the joint record. The detailed module
  plans and completed boundaries are below. These remain proof tasks.
- C6 N-target helper: `StepPC.pcsa_clean_N_root` proves that the next
  root is below, and compatible with, the N target from the source bounds
  in r4.3a step (d). The run induction must still prove: the selected PC
  has slot ≤ i; earlier PCs are below the N target; same-slot PCs target
  it; live locks are below it. This helper is exported by `Clean/Export`.
- C3 (`PCDisseminationClaim`): proved for positive slots and exported as
  `pcsa_pcDissemination`. `BodyReceipt` proves an earlier accepting body
  origin, immutable-parent row validity, exact relay before its deadline,
  and exact body membership at every honest node before the freeze.
  Ack admission, pool transport, exact lookup, quorum assembly, and freeze
  preservation discharge all C3 store premises. The claim needs no extra
  premise. Its only axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- C5 (`AvailableMonotoneClaim`): prove S monotonicity, preservation of held
  PCs in stage 1, and prefix order of selected PC targets over time. Supply
  compatibility of the later target with the later S to Generic PCFloorMono.
- `CleanDisseminationClaim`: lift the N score gap through receipt and the
  next-label walk to HEAD coverage; lift the honest batch to result coverage.
- `PCSACleanSafetyClaim`: establish S/PC compatibility across nodes and times,
  plus the two monotonicity facts needed for C5, over the whole cut.
- `PCSACleanInclusionClaim`: prove equal honest HEADs at the proposal label,
  result = proposal at every honest gate, and persistence of its prefix in S
  and in the available output through the cut. The gate write fact is done.
- C9 (`StrongIncludedClaim`): closed by formation part 4 only
  (`pcsa_clean_honestProposal_stamped`, `pcsa_strongIncludedClaim`).
  Formation itself was not changed.

Do not fill these gaps by adding premises to any claim or by exporting a
conditional theorem as an unconditional claim.

## Formation interfaces

- `hAckPoolMono`: discharged by `pcsa_ackPool_stateBefore_mono`, with
  `FormationPrem.base.noRestart`; the honest-node binder is unused.
- `hAckAdmit`: the exact interface is `pcsa_formation_ack_admit`; its
  base theorem is `pcsa_honest_ack_admitted`. Use
  `FormationPrem.base` and the lower receipt-time bound. The theorem proves
  admission of direct and carried honest acks. The upper bound is unused.
- `hPCCollect`: discharged by `pcsa_formation_collect`. `HonestBody`
  proves immutable-parent row validity at the emitted proposal, then exact
  admission and preservation at every honest receiver before the freeze.
  `pcsa_formation_body_before_freeze` supplies the full named proposal body.
  No extra hypothesis remains in this interface.
- `hFreezeKeep`: the exact interface is `pcsa_clean_freeze_keep`; its
  base theorem is `pcsa_collectPCs_after_freeze`, using
  `FormationPrem.base.valid.toScheduleWellFormed`, `base.noRestart`,
  `base.delta`, and `freezeTime s < gateTime s ≤ horizon`.
- `BodyPersistence`: FG and base bodies persist through every delivery and
  clock. Exact bodies persist between run indices without restarts. Exported.
- `TreeReceipt`: reachable stores have identical base and erased FG body domains.
  The stage-1 full tree retains every stored FG block. These facts are exported.
- `BodyAdmission`: a body with valid rows for its immutable parent cannot
  be excluded in stage 1. A fresh, dependency-ready, well-formed body
  passes admission once the receiver slot is large enough. The run receipt
  proof must establish that these conditions hold on the actual delivery.

No open claim was exported as an unconditional theorem. AckStore now uses
constructor cases to avoid all 19 foreign match equation exports introduced
by the previous partial commit. The base W1 modules are unchanged.

## Continuation 4 plan (2026-10-06)

Validated and committed `bd73be1`. Main is `88c616d`; keep this branch base.
No rebase. C3 and the four Formation store interfaces are complete.

C6 receipt steps, with a commit after each completed module:
1. Preserve the exact HEAD receipt stamps through clocks and deliveries.
   Prove that stored HEADs have stamp entries. Use these facts to keep the
   first receipt time when the pool grows.
2. Prove HEAD stamp origin at a direct or accepted proposal-carried handler.
   Convert a stamp below a public cutoff into acceptance before that cutoff.
3. Relay each early HEAD before the late deadline. A receiver retains the
   exact HEAD or two distinct HEADs of its seat. Transport both cap witnesses
   back to the source denominator. Prove exact body receipt and stamp bounds
   for the resolved support HEADs with `BodyReceipt`.
4. Apply CL1–CL4 to these actual counts and `CommonResolution`. Then prove
   the Vote/Ack/Gate/PC record steps and compose the label induction.

### Pending-label targets after C6 (M1–M4)

The outage writer owns the claim statements on `pcsa-w3-outage`.
Do not prove these targets now. The following supply map is planned; a
module or lemma marked planned is not yet available.

- M1, results non-empty for `earlyTime j ≤ b₀`: the planned gate result
  existence lemma in StepGate uses the honest early HEAD batch,
  `Clean₂.labels`, receipt transport, and the majority walk from genesis.
  Apply it to the pending label with delivery only through `b₀`.
- M2, CI HEAD/result chain at pending labels: StepVote's
  `pcsa_honestHead_extends_root` and the planned CL2 run transport supply
  HEAD extension. The planned StepGate batch lemma supplies result extension
  and compatibility. These facts need `earlyTime j ≤ b₀`, even if the gate
  is after the cut; `CleanInvariantClaim` alone has the stronger gate bound.
- M3, `CleanDisseminationPendingClaim`: StepPC's `pcsa_clean_N_root`,
  `CommonResolution`, `HeadPersistence`, and the planned N-score receipt
  transport supply next-label HEAD coverage. The planned StepGate batch
  lemma supplies result coverage. Keep the pending delivery boundary.
- M4, store items through `b₀`: the planned event induction for CI supplies
  PC chain/result compatibility, lock origin/keep/write, and S origin/order
  through the cut. `BodyPersistence` and `HeadPersistence` supply exact
  pool preservation. Do not derive the whole cut from a CI bound
  `t < voteTime (j + 1)` without a separate pending-store argument.

### Receipt continuation after `a3f0e4f`

`HeadReceipt` closes step 2 for HEAD timestamps. The six public facts are
`pcsa_head_stamp_keys`, `pcsa_head_stamp_lookup`,
`pcsa_head_stamp_stateBefore_eq`, `pcsa_process_head_stamp_origin`,
`pcsa_head_stamp_source`, and `pcsa_head_accepted_before`.
The last fact uses a public cutoff and the existing schedule/clock laws.

The next admission step is checked in scratch: a direct or proposal-carried
HEAD handled from the slot start to its gate leaves either the exact HEAD
or equivocation evidence. Lift this outcome to the later indexed state,
and retain both cap witnesses with their strict late stamps. For a faulty
HEAD accepted before the vote duty, derive that its acceptance is at or
after its slot start from the actual admission guard. Do not assume that
all early support HEADs were emitted honestly at the vote duty.

Then prove the body stamp bound for early resolved HEADs. `BodyReceipt`
already provides exact body relay and preservation; its earlier body
origin alone does not identify the first receipt stamp's time.

Ownership check for HeadReceipt: the first compiled version generated six
foreign `admitBlock` matcher exports. Use explicit Boolean constructor
cases for the key invariant and a native parent-match hypothesis for stamp
origin. This removes all six exports. The explicit equation check passes with
zero unaccepted exports. Owner modules and the baseline are unchanged.

### Local denominator transport (2026-10-07)

`HeadTransport` supplies `pcsa_handled_head_late_or_cap`: a direct or
accepted proposal-carried HEAD handled within its receipt window enters
the later late denominator, or both copies of its capped seat do.
`pcsa_head_before_cut_mem_late` and `pcsa_cap_before_cut_mem_late` retain
the exact copies with their first stamps. `pcsa_head_receipt_window`
derives the admissible store slots from the actual delivery event.
All eight facts are exported. They do not establish cross-node delivery.

Next for C6: derive the slot-start lower bound for an actual accepting
HEAD handler, including faulty HEADs accepted before the vote duty.
Use `pcsa_head_accepted_before`, strict relay, and the local denominator
transport to prove forward and backward count membership. Prove the
corresponding body stamp bound and exact resolution after body relay.
Then supply retained paths, proposal/voter view equality, CL1–CL4 run
inputs, and the four record steps. No run-level claim is closed by these
local transport facts alone.

### Cross-node HEAD relay (2026-10-07)

`HeadRelay` closes the missing slot-start lower bound.
`pcsa_head_acceptance_after_slot_start` applies to direct and carried
HEADs, including faulty HEADs accepted before the vote duty.
`pcsa_head_relay_late_or_cap` handles old receipt, permanent cap evidence,
and strict relay. `pcsa_head_before_public_cut_relay_late` takes an actual
pooled HEAD with a first stamp before a public cutoff. Its relay deadline
must precede the healthy cut and the label's gate. This is the common
receipt interface for early support and for frozen or proposer read sets.
All five facts are exported, without changing a claim statement.

Next: prove body first-stamp origin and preservation, then exact body
resolution at the receiving post-clock read. Apply the public-cutoff
receipt interface to the concrete frozen and carried walk inputs.
The joint CI record and its corollaries remain unproved.

### Body receipt data (2026-10-07)

`BodyStamps` supplies exact clock preservation of the cumulative body
list and stamp list, delivery/indexed stamp-prefix preservation, stamp
keys including genesis, first lookup, and unchanged first body receipt
time. All eight facts are exported. The insertion-origin and earlier
passed-admission facts compile in scratch. Check and commit them next.
Then connect the earlier admission to the exact `BodyReceipt` relay and
prove receiver stamp bounds and resolution for the counted HEAD body.

For pending M3, `HeadRelay.pcsa_head_before_public_cut_relay_late` will
supply the HEAD/cap receipt part of the N-score transport. `BodyStamps`
and the next body-origin module will supply its exact body/timestamp part.
These are support facts. Pending-label claims are still deferred.

### Body cutoff relay (2026-10-07)

`BodyRelayTime` identifies the first non-genesis body-stamp insertion,
its indexed passed admission, and its actual fresh acceptance.
`pcsa_body_before_public_cut_relay` gives exact body membership and a
strict first-stamp bound at every later honest receiving read. It uses
the existing unconditional `BodyReceipt` admission and relay facts.
All seven facts are exported. No new premise was added to a claim.

The exact receiver root-domain and held-body resolution facts also
compile in scratch (`ResolutionLookup.lean`). Check and commit those
next. Then put concrete early, frozen, and carried walk inputs into the
CL1–CL4 count interfaces and prove the four joint CI record steps.

### Exact receiving resolution (2026-10-07)

`ResolutionDomain` proves that clocks preserve the cumulative resolution
field and that it is `none` at every indexed run state.
`pcsa_resolved_head_of_held_body` resolves the exact signed root HEAD at
an honest stage-1 clocked read once its body is held. It uses scoped root
uniqueness and `Block.findByRoot?_of_unique`, not a first-copy lookup.
All three facts are exported.

Next: apply the HEAD and body cutoff-relay interfaces to `headVotes`,
`headSupport`, `proposerVotes`, and `proposerSupport`. The carried arms
need indexed accepted-proposal provenance. Frozen arms use the first
stamp below the freeze. Then derive CL1–CL4 run count inputs, retained
paths, equal honest proposal/voter walks, and the joint CI record.
No new unconditional run claim is exported by this resolution module.

## Count-input plan after the receipt modules (2026-10-07)

The generic public-cutoff interfaces are proved. They do not yet supply
the lists in CL1–CL4. Use the actual definitions in Model/Frame.lean.

1. Prove indexed provenance of every wire in `st.proposals`: it was
   appended by an earlier accepted direct proposal delivery. Keep the
   named proposal and the exact handler tests. Lift the wire's well-formed
   raw/support subset rule from that delivery.
2. For `headVotes p st s`, split the deduplicated union into its frozen
   arm and carried arm. The frozen arm has first HEAD stamp below
   `freezeTime (s - 1)`. Apply HEAD cutoff relay to that arm.
   A carried raw HEAD has an actual handler at the proposal's earlier
   accepting delivery. The local handler theorem supplies its exact
   copy or two cap witnesses. Relay those witnesses before the source
   gate. Do not treat carried metadata as automatic pool admission.
3. For `headSupport p st s`, add exact body resolution and the body
   stamp bound. Its frozen arm uses current active resolution and the
   same freeze cutoff. Its carried arm is the declared support, filtered
   by label and current resolution; recover membership in the raw arm
   from the delivered proposal's well-formedness.
4. For `proposerVotes` and `proposerSupport`, use the actual slot-start
   indexed read. Prove every pooled HEAD has first stamp before the
   read's public cutoff. Relay it into the preceding label's gate pool.
   This is the backward denominator input.
5. Instantiate CL1 with actual support-seat sets and their union in both
   late denominators. A shared clean seat has one exact signed HEAD;
   `CommonResolution` gives one body. Instantiate CL2/CL3 transfer with
   both receipt directions and retained path membership. Instantiate
   CL4 with the early N-seats and these same read interfaces.
6. Prove equal honest proposer/voter PC views and walks, then the
   Vote/Ack/Gate/PC record steps. The composing induction must contain
   no new store case split.

Exact open facts: proposal-pool provenance; raw/support carried-input
membership; concrete forward/backward walk-list transport; retained
path membership; common honest proposal/voter views; CI label zero and
the four record steps. These are proof tasks, not counterexample blockers.
C5 and the clean dissemination/safety/inclusion claims still depend on
the completed run invariant. No new statement change is proposed.

## Continuation 6: model integration (2026-10-07)

Rebased onto `43733fe`. First update the relay proofs for the new PC
handler arm. Signed ack, HEAD, and proposal children cannot equal an
unsigned PC object. The generic handles-to-carries proof uses the stored
carriage premise. These steps do not inspect PC target equality.
Run the full pre-commit checks and commit this integration before C6.
The later `HeadReceipt` and `HeadRelay` modules also need the new outer
disjunction. The same constructor argument applies.

### Next modules

`ProposalReceipt`: preserve the proposal pool through clocks. Prove a
process predicate with the exact named-parent, parent lookup, and block
admission checks. Use event induction to find the earlier delivery.
Use its wire check for support membership and raw labels. Export the
earlier handler for each carried raw HEAD.

`WalkInputs`: split the concrete voter lists into frozen and carried
arms. Recover the stored named proposal behind each carried input.
Use `ProposalReceipt` to give its earlier handler. Then connect each
arm to the public-cutoff receipt lemmas and exact body resolution.

`InputTransport`: relay both witnesses of a capped source seat. Prove
backward denominator receipt for pooled proposer inputs and frozen voter
inputs at their actual public cutoffs. For carried inputs, use the earlier
handler and its receipt window, then relay its exact HEAD or cap witnesses.
Keep body-resolution transport separate from raw denominator receipt.

`BackwardInputs`: use the actual voter tick to read the strict prefix.
Split its raw list with `WalkInputs`. For the carried arm, recover the
earlier accepted proposal and the exact signed HEAD. Derive its receipt
window from the admitted proposal slot and the source tick. Relay the
handler outcome with `InputTransport`. Combine this with frozen relay.

`ForwardReceipt`: relay early source support into the strict pre-freeze
state. Preserve the exact HEAD and its first stamp to the voter read,
or preserve both cap witnesses. Relay the resolved body before the freeze
and keep its first stamp. Use stage-1 exact resolution to enter the
frozen support arm. Include genesis explicitly.

Integration validation passed: four PC-SA targets and default build,
zero warnings; full check-build, zero unaccepted equation exports; layers,
F-13/F-23, precheck, permitted axioms, prohibited scan, and diff check.
The slot-zero regression keeps its counterexample and excludes unsigned
PC children from the honest-signature obligation. No claim changed.

### Proposal provenance

`ProposalReceipt` proves the earlier indexed direct delivery and all
three admission tests for each stored proposal. The delivery wire check
gives raw HEAD labels and support membership in raw HEADs. Each carried
raw HEAD has an earlier handler. Clocks preserve the proposal pool.
These seven support facts are exported. C6 is still open.

`CountTransport`: instantiate CL2 with the actual gate support and late
denominator, and the actual voter raw/support lists. Prove source clean
seats are not capped in the source denominator. Use forward exact body
receipt and backward raw receipt. Leave only root compatibility and
retained-path premises for the joint CI step to supply. Then add the
proposer form and the CL1/CL4 support-seat instances.

`GateCounts`: identify the actual clean score-seat sets. Relay their
union into both same-label late denominators. A shared clean seat has
one exact signed HEAD; common resolution gives one body. Apply the
finite-set majority intersection to prove compatible actual gate results.

### Concrete voter lists

`WalkInputs` splits each concrete voter raw/support input into its
frozen or carried arm. It recovers the exact stored proposal and extracts
the frozen HEAD/body stamp bounds. It proves support is a subset of raw
input at every indexed post-clock read. These eight facts are exported.
They do not yet prove retained paths or the joint CI record.

`GateReads`: the claim reads `clockPre`, while the count lemmas use the
post-clock state. Prove that the gate preserves every confirmation input
field. Convert `gateResultAt` to its indexed clocked source. Lift the
same-label count result to the exact claim reader.

`BodyPaths`: prove prefix closure of reachable body pools from exact
parent admission. Stage 1 retains every block in any supplied frame
subset. A body held before the freeze retains all its prefixes in the
voter tree at a later read. Use first stamps, with genesis handled at 0.
`ResultPaths`: a genuine gate result has an early resolved support
witness above it. Relay that body before the freeze and retain its
prefixes. This discharges the path premises of both actual CL2 walks.

### Backward input receipt interfaces

`InputTransport` relays both witnesses of a capped source seat. It
instantiates the public cutoff for frozen inputs and proposer inputs.
The proposer form uses the actual proposer and gate tick indices.
The handler form relays an exact HEAD or a source cap. Six facts are
exported. The concrete carried voter arm is the next module.

`VoteTransport`: extract the actual indexed read of an honest HEAD.
Use the predecessor CI root-compatibility field, actual voter counts,
and retained result paths to prove that every next-label honest HEAD
extends each predecessor result. Keep this as a step from the previous
record; do not assume the invariant at the label being proved.

`HeadEvidence`: expose the existing handles-to-carries helper from
AckAdmit. Use the Generic single-duty signature theorem and HEAD stamp
origin to prove honest pooled HEAD uniqueness and the absence of honest
seat caps. Recover honest pool emissions and their duty reads.
`HonestBatch`: use those facts, strict broadcast, and body receipt to
put each awake honest HEAD into every early support list. Bound late
participants by awake honest HEADs plus faulty seats. Use the clean
participation bound to prove the gate batch and result extension.
These modules support C6; pending-label claim exports remain deferred.

### BackwardInputs

Every concrete frozen or carried voter raw input reaches the source late
denominator at the actual gate, as an exact HEAD or a capped seat.
These are support facts. C6 and its remaining joint record fields are open.

`HeadBody`: use the existing live-root origin and walk membership facts
to show an honest HEAD's exact body is held before its vote tick. Keep
its first body stamp strictly below that public time. Relay the body
before the early cutoff. This supplies the body part of HonestBatch.

`HonestReceipt`: recover the actual honest HEAD emission. Prove it is
not excluded before the early cutoff, using the store-slot bound and
honest-seat no-cap fact. Strict broadcast then gives exact HEAD receipt
and a strict early stamp at every later honest read.
`HonestSupport`: combine exact HEAD receipt with HeadBody resolution
and the HEAD slot bound. Exclude conflicting late copies with honest
signature uniqueness, so the HEAD belongs to clean early support.

`GateBatch`: use the honest batch majority and a held honest HEAD
witness to retain the path above genesis. Apply the existing FG-SA
confirmation walk theorem to prove nonempty clean results and extension
of any common honest HEAD prefix. Require the gate to be in the clean
cut; leave the pending-label result claim for after C6.
`ZeroResult`: admitted non-genesis bodies have positive slots. Combine
this fact with an early support witness to identify the label-zero
result as genesis. This is the result part of the CI base case.

`NCounts`: instantiate CL4 with actual N-seat sets and same-label gate
support. Relay each N HEAD into the gate denominator. A shared clean
seat gives the same signed HEAD and body. Then transfer the N quorum
into next-label walk scores; bound caps by faulty seats and apply the
strict N score gap. Use only geometric PC identities in later view work;
certificate ack lists can differ on equal ranks.

### ForwardReceipt

Early HEAD and body receipt gives strict freeze stamps and exact body
resolution in both proposer and voter support. Cap witnesses reach both
raw lists. Genesis is included.
These are support facts. C6 and its remaining joint record fields are open.

`NWalkCounts`: bound the intersection of conflicting score-seat sets
by capped seats. The fault bound gives the strict N score gap. Prove
honest seats cannot be capped in actual voter or proposer raw inputs;
use backward receipt for the voter case. This prepares N dissemination.

`NReadTransport`: extract a resolved HEAD witness from an N count.
Transport every counted seat into both next-label score sets, including
cap outcomes, and retain every N-target prefix. Then apply NWalkCounts
under an explicit N-target root-compatibility premise. The existing
StepPC root-bound helper must still receive its run premises.

### CountTransport

Actual gate-to-voter and gate-to-proposer counts discharge CL2. The only
geometric premises are root compatibility and retained paths. Clean late-
seat uniqueness and resolved support witnesses are exported.
These are support facts. C6 and its remaining joint record fields are open.

`NNextHead`: combine NReadTransport, the honest-cap bound, and the
strict N score gap at the actual next voter read. Prove next HEAD
coverage under the separate N-root compatibility premise.
`NHeads`: use the N-seat intersection bound and honest pool evidence
to identify actual honest HEAD decisions on N targets. Derive N-target
uniqueness from one common honest seat. These facts supply the PC
chain step without a dependency on the separate PC proof lane.

### GateCounts

Actual score-seat sets and cross-node late receipt prove compatibility of
two same-label honest gate results. Shared clean seats have one signed
HEAD and one resolved body.
These are support facts. C6 and its remaining joint record fields are open.

`PCPool`: keep the certificate provenance invariant local to the Clean
lane. Reuse the established PC/Certificates proof pattern in a separate
namespace. The lane import rules forbid a direct dependency on PC.
`PCScope`: each new installed PC target is in the completed body pool.
Lift this origin through the run to the existing collision scope.
`AckOrigins`: retain a strict public-time bound in each pooled/certified
ack origin. Use unforgeability and the actual ack duty to get an honest
ack decision on the held PC's exact target and its slot-time bound.
These supply the PC fields of C6 and the label-zero PC base case.

### GateReads

The clock preserves all raw confirmation inputs after clockPre. The same-
label compatibility theorem now applies to gateResultAt from the claim.
These are support facts. C6 and its remaining joint record fields are open.

`AckDecisions`: split the decision read from the timed-origin proof.
Identify the actual post-clock ack decision, resolve its full target in
the collision scope, and lift the result to `storeAt` below a cutoff.
Derive PC slot bounds and the empty-PC fact before the first gate.
`StoreOrigins`: deliveries preserve S or normalize it to F. They only
remove locks. The pre-gate clock only removes locks and keeps S. Use
these facts for the label-zero store base and the joint record origins.

GateReads hygiene: the first field-congruence proof generated three
foreign `resolvedBefore` matcher exports. Explicit receipt-field
equalities remove them. The direct equation audit now has zero
unaccepted exports; the full validation is being repeated.

GateReads passed the complete pre-commit list after the field proof
repair. The equation audit reports zero unaccepted exports.
The announced root-form relay commit is now main `861ca1f8`; integrate
it at this validated boundary before the PC-view proofs.

### BodyPaths

Reachable body pools are prefix closed. A vacuous frame retains any block
subset. Pre-freeze bodies retain all prefixes in later voter trees.
These are support facts. C6 and its remaining joint record fields are open.

`ZeroStores`: lift S preservation and lock removal through the event
prefix before the first gate. Combine them with the PC time bound at
`storeAt`. The draft proves genesis S and empty lock/PC lists there.
`SnapshotContents`: trace each frozen PC to the exact freeze tick and
the PC pool before that tick. Filtering can remove entries but cannot
create them. Derive empty snapshots in the label-zero store interval.
`CarriedPCs`: trace each proposal-carried PC to its earlier delivery.
Use well-formed ack witnesses and unforgeability to bound its slot.
This closes the remaining label-zero voter-view cases.

BodyPaths naming: F-20 rejects the `_closed` suffix even for prefix
closure. Rename the new helper to `pcsa_body_prefix_mem`; keep its
statement unchanged and rerun the full checks.

`ZeroViews`: show that no proposal duty emits at label zero. Use the
empty PC, snapshot, carried-PC, and lock facts at the slot-one vote to
identify its root as genesis. Show that the label-zero gate input has
no PC, so its lock-write predicate is true. Assemble CI(0) in Export.

Record composition: assemble the successor `headsAbove` and
`resultsChain` fields in Export from the predecessor CI, next-HEAD
transport, and the clean gate batch. For an old result at the predecessor
label, use the same node's result to get equality. Do not turn
same-label compatibility at different nodes into prefix order.

`RecordEvents`: a gate keeps S or writes its raw result. Under the
stage-1 frame, normalization keeps S. Trace a changed clock record to
the exact gate label and result, then lift origins through event
indices. This supplies recordOrigin; compatible result order supplies
recordMono and recordCompatible.

`ProposerInputs`: extract the exact raw/support lists, PC view, and
parent walk from an honest generated proposal. Prove that lifting
root HEAD wires and projecting them back keeps both source lists.
Use these exact payload facts for the common-view and retained-walk step.

`CommonInputs`: at the actual proposer tick, its full preceding-label
pool equals that label's late denominator at the same read. Relay
frozen voter inputs into this proposer pool. Use the generated proposal
input equations to compare the carried and frozen counts.

### ResultPaths

Each genuine gate result has an early resolved support witness above it.
Body relay and prefix closure retain all result prefixes in both next-
label walk trees.
These are support facts. C6 and its remaining joint record fields are open.

`ProposalEvidence`: use the unique proposer duty and unforgeability to
show that every stored proposal of an honest proposer's slot is its
exact emitted named body. Then all carried input metadata at that
slot comes from the one actual proposer read.

`ProposalStore`: prove exact proposal-wire insertion and pool
preservation. Use these facts after strict honest proposal broadcast
to keep the one emitted body's raw/support/PC metadata at voter reads.

### VoteTransport

The actual honest HEAD read, concrete counts, and retained paths turn the
predecessor CI root field into next-label HEAD extension. No invariant at
the new label is assumed.
These are support facts. C6 and its remaining joint record fields are open.

`ProposalDelivery`: strict broadcast and immutable-parent row validity
give a passed direct admission before the voter tick. Keep both the
exact proposal wire and its body at every later read. This supplies
the carried input arm for the honest-proposal common-view proof.

`LockEvents`: show that a gate retains an old lock row or writes a
row below its raw result, at the SA release level. Trace each reachable
row to an earlier honest gate. Use this origin for leaseBelowResult
and for the release-count bound in lockKeep.

`RecordBounds`: convert indexed record and lock origins to inclusive
store reads. Bound their gate labels by the next-vote cutoff. Use the
result-chain field to compare honest records across nodes and times.
Prove record monotonicity separately from the update event and its
earlier own result.

`ReleaseCount`: map every seat counted against a lock to its holder.
Use the exact pooled-HEAD source to exclude honest holders when their
HEADs are compatible with the lock. The resulting faulty-seat bound
is below the SA release threshold under FaultsBelowQA.

`ViewOrigins`: a vote tick preserves PC snapshots and proposal
metadata. Split the selected voter PC into frozen and carried sources.
Recover an exact honest ack before the vote for either source, using
scoped body-root equality for carried targets. This supplies the
separate N-root argument and the common-view comparison.

`CommonRaw`: use wire well-formedness to recover the signing slot of
stored metadata. At an honest proposer slot, all carried raw lists
come from the unique emitted proposal. That list is in every voter
read after receipt. Every extra raw voter input is frozen and relays
back to the proposer as an exact input or a capped seat.

### HeadEvidence

Every honest pooled HEAD has an exact prior emission. Unique HEAD duties
rule out honest caps and fix the emission time and awake status.
These are support facts. C6 and its remaining joint record fields are open.

`RootSources`: a vote tick creates no lock. Split each actual next-vote
root into genesis, a PC target with an earlier honest ack, or a lock
below an earlier result. Keep the result label strictly below the
current label. Use these alternatives for result and N-target root
compatibility in the joint induction.

`NRoot`: an honest ack target is an exact honest HEAD, and same-label
ack targets are equal. For its next-vote root, earlier PC targets lie
below that HEAD by prior dissemination; a same-label PC has the same
target. Earlier lock results also lie below the HEAD. This proves the
separate N-target root condition without the false old CI(vii) clause.

`PCChain`: bound the slot of each held PC by the next-vote cutoff.
Use exact honest ack origins, same-label uniqueness, and earlier ack
dissemination to prove PC prefix order. Compare a PC with a result by
splitting earlier, equal, and later labels. Keep these dependencies
explicit for the joint record construction.

`LockRetention`: track a retained row or a conflicting installed PC
through collection. If all resulting PCs are compatible with the row,
collection keeps it. Extend this argument through direct and carried
PC admission. Combine it with expiry and the faulty release-count
bound to prove lockKeep from the joint chain facts.

`NDissemination`: combine NRoot with the actual N-count transfer and
retained paths. Given prior ack dissemination and earlier-result HEAD
coverage, an ack of the current label is below every next-label HEAD.
Keep next-label results out of this step unless their gate is inside
the healthy prefix.

### HeadBody

Actual live roots and HEAD walks retain their bodies. Honest HEAD bodies
are held before the vote and reach honest early readers with strict
stamps.
These are support facts. C6 and its remaining joint record fields are open.

`CommonBodies`: a body held at an honest proposer tick is held at
every voter before the vote. Derive its strict source stamp from the
actual pre-tick index. Also relay frozen support bodies to the
proposer. Use these receipts only to establish common walk support.

`CommonSupport`: insert carried support using the exact stored
proposal and resolved body. Relay proposer support bodies to voters
and frozen support bodies to the proposer. Together with CommonRaw,
this gives equal support incidence for uncapped seats and equal walk
scores on the retained candidates.

`CommonScores`: use the actual common raw and support transfers to
instantiate Generic score_eq_on. Prove equal participant counts, cap
status, and scores at every candidate from resolved body witnesses.
The premises name the one generated proposal and its actual tick.

`CommonTree`: identify every current-slot held body with the unique
honest proposal. Split the voter domain into pre-freeze bodies and
ancestors of that proposal. Relay the first arm to the proposer and
retain the proposal-parent path in both trees.

### HonestReceipt

Honest HEADs pass slot and cap checks. Strict broadcast gives exact early
HEAD receipt and stamps.
These are support facts. C6 and its remaining joint record fields are open.

`ViewRank`: compare the maximum slot in the source and voter PC
lists. Same-slot honest ack uniqueness already fixes the full target,
so certificate ack-list equality is unnecessary. A carried source
maximum and relayed upper bounds on frozen sources give equal view
targets, including ties.

### HonestSupport

Honest HEADs are never capped in honest late pools. Their exact bodies
resolve in clean early support.
These are support facts. C6 and its remaining joint record fields are open.

`RelayCollect`: use Clean saturation to obtain complete assembly on
uniquely resolved stored targets. A new key after adding acks requires
a new matching ack; with one added ack, that ack is in the assembled
certificate. Adapt the outage Shared/CollectClosed proof pattern in
a separate Clean namespace; do not import Outage or PC lane proofs.
This identifies the carrier for strict whole-PC relay.

`RelayFrames` and `RelayStore`: supply the exact unchanged fields
and ack-pool growth used by RelayCollect. `RelayCarrier`: show that
the call installing a new key carries its installed PC under the
root-form slot/target-root rule. These are the store premises for
the strict PC relay used in common views.

### HonestBatch

Actual honest HEAD seats outnumber faulty seats. A common honest HEAD
prefix has strict majority in the actual clean gate counts.
These are support facts. C6 and its remaining joint record fields are open.

`RelayPersistence`: a stage-one delivery preserves held PC keys.
Lift this and clock preservation through run indices. `RelayOrigin`:
find the first delivery that installs a held key and prove that it
accepts the carried PC object. Use existing ack-pool monotonicity for
receipt; no new pending-label claim is exported.

`RelayReceipt`: use the existing C3 quorum assembly theorem after
receipt of a whole certificate and its exact target body. Relay an
accepted PC object before the public cutoff plus Delta, retain its
acks or installed key, then use saturation at the receiver. This
provides the PC source bound needed by common views.

### GateBatch

Every clean gate in the prefix has a nonempty result. Its raw result
covers each common prefix of honest HEADs.
These are support facts. C6 and its remaining joint record fields are open.

`FrozenPCTransport`: a held PC target is active in the stage-one
full tree. Recover each frozen voter PC at its exact freeze tick,
then apply whole-PC relay to the proposer tick. The receiver may
hold a different ack list; the slot and full scoped target agree.

`CarriedView`: at an honest proposer slot, every carried PC is the
PC in the unique emitted metadata. Receipt of that proposal includes
its valid carried PC. `CommonViews`: combine this with frozen-PC
relay, source maximality, and same-slot ack uniqueness to prove equal
view targets at the proposer and voter reads, including empty views.

### ZeroResult

All non-genesis reachable bodies have positive slots. The label-zero clean
gate result is genesis.
These are support facts. C6 and its remaining joint record fields are open.

`BodySlotBounds`: extract the handler slot bound and strict parent
slot increase from actual body admission. A read before proposal
slot s+1 contains only bodies of slots at most s. These bounds rule
out a child beyond the current honest proposal in the voter walk.

`ProposalPaths`: the generated parent is the actual proposer head
and is held at that read. Every proper prefix of the proposal is
therefore in the proposer tree. Together with CommonTree, the voter
tree adds at most the proposal itself.

### PCPool

C6 support: preserve certificate ack provenance through all handlers. The
module uses the concrete readers and preserves the joint-induction
premises.
These are support facts. C6 and its remaining joint record fields are open.

`RetainedProposal`: apply the Generic retained-suffix theorem when
the voter tree adds only the proposal. Retain the source parent path,
use equal scores and eligibility, and handle different roots with
coverage of the source root. The sole eligible new child then makes
the voter walk end at the proposal.

### PCScope

C6 support: keep held PC targets in the scoped body pool. The module uses
the concrete readers and preserves the joint-induction premises.
These are support facts. C6 and its remaining joint record fields are open.

`ProposerReads`: identify the actual pre-tick state with the inclusive
read one integer time unit earlier. A proposer tick creates no lock.
Use these facts to apply the predecessor CI PC/result field to the
proposer root, and to trace its locks to earlier results.

`ProposerStep` export: predecessor CI makes every proposer root
compatible with the preceding result. PCs use the exact pre-tick
inclusive reader; locks use their earlier gate origin. Apply actual
proposer counts and retained paths to show the generated parent
extends each preceding-label result.

`CommonEligibility`: reduce the low-parent arm using the zero
stage-one band floor. Compute the actual proposer and voter clock
slots. Equal counts and scores then give equal eligibility, and the
current proposal is eligible by its slot.

`RootAgreement`: common selected view targets give a common walk
base in stage one. The predecessor result bounds every pre-vote lock
and is covered by both walks. Thus the voter root lies below the
proposer parent, and the voter walk covers any deeper proposer root.
This supplies the remaining retained-walk root premises.

### AckOrigins

C6 support: trace held PCs to earlier honest ack emissions. The module
uses the concrete readers and preserves the joint-induction premises.
These are support facts. C6 and its remaining joint record fields are open.

`HonestProposal` and the `EqualHeads` export: recover the unique
named proposal from HonestProposalAt. Normalize the actual voter
read to its strict pre-vote index. Combine common counts, eligibility,
views, tree reflection, retained paths and root agreement. Body slot
bounds make the current proposal terminal. This proves the new
headsEqual field from the predecessor CI.

### AckDecisions

C6 support: recover exact honest ack decisions for held PCs. The module
uses the concrete readers and preserves the joint-induction premises.
These are support facts. C6 and its remaining joint record fields are open.

`ProcessLockRetention`: expose the small lock-field preservation
facts in LockOrigins. Under the stage-one finality value, a delivery
keeps a row if every resulting held or valid carried PC is compatible
with its target. The collection proof already keeps compatible rows;
check the proposal-carried deletion separately.

`ClockLockRetention`: compare release-count read fields before and
after the clock. A live row survives expiry; the strict faulty-seat
bound prevents release. Gate writes can renew rows but retain each
old target. Lift these store facts through actual tick events.

Joint C6 order: carry an auxiliary ack-to-later-HEAD/result prefix
property with CI. From predecessor CI, prove current headsAbove,
headsEqual and resultsChain. Old ack coverage gives current result
coverage. NRoot gives next-HEAD coverage for current acks. The
current result chain and ack/result compatibility give PC order,
record fields, lock fields and roots. Use those roots with CL2 to
extend older ack coverage to the next HEAD. Then construct CI and
the auxiliary record together. No current CI is assumed in a step.

`AckResults`: combine prior-result HEAD coverage, same-label CL4,
and ack-to-later-result coverage for all label orders. `StorePCInputs`:
recover bounded honest acks from indexed held/carried PCs and exact
gate inputs. `LockWrites`: ack/result compatibility makes each PC
compatible with every result prefix, so no gate lock write is vetoed.

### StoreOrigins

C6 support: preserve stage-one records outside gate advances. The module
uses the concrete readers and preserves the joint-induction premises.
These are support facts. C6 and its remaining joint record fields are open.

`RunLockKeep`: split each actual event. Deliveries preserve the row
using exact post-state PC/metadata ack origins and ack/result
compatibility. At a release tick, each old lock lies below an earlier
result and therefore every honest HEAD of the release label. Only
faulty seats can count, below the stored level. Expiry and renewal
then preserve the live target. Other-node events leave it unchanged.

`JointAux`: retain ack-to-later-HEAD/result coverage with CI. The
label-zero ack target is genesis. Convert adjacent HEAD coverage
and ordered results into coverage of every earlier result. These
are the auxiliary premises for the final joint successor step.

### LockOrigins

C6 support: trace lock rows through delivery and pre-gate filtering. The
module uses the concrete readers and preserves the joint-induction
premises.
These are support facts. C6 and its remaining joint record fields are open.

`JointStep` export: construct the current result/HEAD fields,
ack/result compatibility, store and lock fields, roots, and the
extended ack coverage in the recorded order. `CleanInvariantClaim`
then follows by induction from the checked label-zero record and
label-zero auxiliary coverage. The assembly adds no new premises.

### ZeroStores

C6 support: prove empty pre-gate PC and lock stores. The module uses the
concrete readers and preserves the joint-induction premises.
These are support facts. C6 and its remaining joint record fields are open.

### SnapshotContents

C6 support: trace frozen PCs to exact earlier pool reads. The module uses
the concrete readers and preserves the joint-induction premises.
These are support facts. C6 and its remaining joint record fields are open.

C6 kernel milestone: /tmp/Invariant.lean proves CleanInvariantClaim
and the joint ack-coverage theorem. Both axiom prints contain exactly
propext, Classical.choice and Quot.sound. Production module gates and
commits are still in progress.

C5 plan: generalize record event order to an indexed limit, so each
completed gate uses C6 at its own label. For a held PC of slot s, its
honest ack has earlyTime s within the prefix; CI(s-1) and its auxiliary
HEAD coverage order it after older PCs and results. PC persistence and
maximum-slot selection give selected-target monotonicity. Apply the
Generic pcFloor monotonicity theorem to S and the selected PC target.

`CutReads`: retain actual gate times for S origins, actual early
times for PC ack origins, PC persistence at inclusive reads, and
selected-PC source witnesses. `CutOrder` export: use C6 at completed
gates and at the gate equal to the later PC ack time. Derive record
monotonicity, PC target order and PC/S compatibility through the full
cut, then prove AvailableMonotoneClaim (C5) with pcFloor_mono.

`CleanOutputs` exports: clean dissemination is a projection of the
checked joint ack coverage. For safety, compare all completed S
origins and observed PC ack targets across nodes and times. The
available output is S or a selected PC target; strong is that target
or genesis. C5 and selected-target order give both monotonicity parts.

`GenuineKeys`: trace each saved raw-result label to its exact earlier
gate tick. Delivery preserves labels; only the matching clock gate
adds one. Nodup makes the actual gate input unsaved. `GateAdvance`:
with the clean lock guard clear, the gate result is below post-clock S.
Use the checked C5 event-order lemma to carry this lower bound to
every later read and then to the available output for clean inclusion.

### CarriedPCs

C6 support: trace carried PCs to exact honest ack targets. The module uses
the concrete readers and preserves the joint-induction premises.
These are support facts. C6 and its remaining joint record fields are open.

### ZeroViews

C6 support: identify label-zero views and the next genesis root. The
module uses the concrete readers and preserves the joint-induction
premises.
These are support facts. C6 and its remaining joint record fields are open.

### RecordEvents

C6 support: trace records to exact earlier gate results. The module uses
the concrete readers and preserves the joint-induction premises.
These are support facts. C6 and its remaining joint record fields are open.

### LockEvents

C6 support: trace lock targets and levels to earlier gate results. The
module uses the concrete readers and preserves the joint-induction
premises.
These are support facts. C6 and its remaining joint record fields are open.

### RecordBounds

C6 support: bound record and lock origins at inclusive reads. The module
uses the concrete readers and preserves the joint-induction premises.
These are support facts. C6 and its remaining joint record fields are open.

Pending cutoff audit: HealthyPrefixDeliveryBy covers a relay only
when its full deadline is at or before the cut. M3 assumes only the
next HEAD time is before the cut. Test n=6, Delta=2, cut=18, with a
faulty proposal delivered at 17 carrying one new off-branch HEAD.
Its relay deadline is 19; the source result is read at 20. The same
run tests CleanHeadsPastCutClaim. Verify all executable run and
clean-prefix checks before recording a counterexample.

`PendingGates`: the honest early batch gives a nonempty result and
covers any common honest HEAD prefix using only earlyTime <= cut.
Use this for M1 (CleanResultsNonemptyClaim) and M2
(CleanResultsChainPendingClaim). The fifth store fact used by the
Outage assembly is LeaseBelowRecordClaim (Claims/PC.lean); keep that
exact statement as the M5 target.

### RecordOrder

C6 support: derive record monotonicity from ordered own results. The
module uses the concrete readers and preserves the joint-induction
premises.
These are support facts. C6 and its remaining joint record fields are open.

### ProposerInputs

C6 support: recover actual inputs of emitted proposals. The module uses
the concrete readers and preserves the joint-induction premises.
These are support facts. C6 and its remaining joint record fields are open.

`StoreCutFacts`: preserve the exact gate event and time for every
lock at an inclusive read. The gate result is below post-gate S,
and full-cut record order carries this to the read. Observed PC ack
targets are compatible with that result. This proves the unchanged
LeaseBelowRecordClaim used as M5 by Assembly/Outage.

`BlockReceipt`: trace a held non-genesis body to its accepting event
at or before T. Strict relay places it before that event time plus
Delta, hence before every requested after-ticks read at T+Delta or
later. Genesis uses the initial body invariant.

### CommonInputs

C6 support: relay frozen voter inputs to actual proposer reads. The module
uses the concrete readers and preserves the joint-induction premises.
These are support facts. C6 and its remaining joint record fields are open.

### Confirmed cutoff counterexample: M3 and HeadsPastCut

The executable run in /tmp/PendingHeadCounterexampleChecked.lean passes
all finite execution and clean-prefix checks. The cached trace and
its HEAD/result readers are proved equal to the actual engine readers;
these identities use only propext, Classical.choice and Quot.sound.
The check is /tmp/pcsa-pending-head-counterexample5.log (exit 0).

Parameters: n=6, one faulty node, Delta=2, cut=18. Five honest label-1
HEADs split 3 on X and 2 on Y. At 17, only node 3 receives faulty
slot-2 proposal Z, a sibling of X, carrying one faulty label-1 HEAD
on Y. Its relay deadline 19 is outside the clean cut. At the vote
time 18, node 3 has 6 raw voters: X has score 3 and is ineligible.
Its current-slot child Z is eligible, so HEAD_3(2)=Z. At the gate
time 20, node 0 has 5 late voters and 3 early X supporters, so
R_0(1)=X. X is not a prefix of Z. Both disputed claim premises hold:
v_2=18 <= cut and e_1=12 <= cut.

M3 and CleanHeadsPastCutClaim cannot be proved as stated. No claim
was changed. A sufficient repair for the general result-to-HEAD
statement is d_(i-1) <= cut, which covers the backward carried-vote
relay deadline; that repair does not give the requested past-cut
conclusion. The outage boundary may need a weaker statement about
its stable prefix instead of every pending raw result.

The validation queue will stop after its current commit because this
new OPEN entry is intentionally unstaged. Add the counterexample as
a separate test commit, then resume the remaining module sequence.

The counterexample is now in Tests/PendingHeadCounterexample.lean.
The same run passes CLEAN at both cut 18 (M3 fails at the cut) and
cut 12 (HeadsPastCut fails strictly after the cut). Saved trace and
claim-reader identities are kernel checked. The pending declarations
were copied exactly from pcsa-w3-outage (f16292f5/a428844a); existing
claim statements were not edited. Full test validation is running.

`VoterAuthenticity`: trace each frozen or carried raw voter HEAD
to an authentic emission. One honest duty gives one signed root, so
an honest seat is never capped in any voter input list, without a
relay or gate-time premise. `PendingNHead`: use that bound with N
receipt and retained paths; only the next vote must be within the
clean prefix. This proves M4 without the false M3 premise.

### ProposalEvidence

C6 support: identify stored honest proposal metadata exactly. The module
uses the concrete readers and preserves the joint-induction premises.
These are support facts. C6 and its remaining joint record fields are open.

### ProposalStore

C6 support: preserve admitted proposal metadata through run events. The
module uses the concrete readers and preserves the joint-induction
premises.
These are support facts. C6 and its remaining joint record fields are open.

### ProposalDelivery

C6 support: deliver exact honest proposal metadata before votes. The
module uses the concrete readers and preserves the joint-induction
premises.
Validation and current claim status are recorded in log.md and state.md.

### CommonRaw

C6 support: compare concrete proposer and voter raw inputs. The module
uses the concrete readers and preserves the joint-induction premises.
Validation and current claim status are recorded in log.md and state.md.

### CommonBodies

C6 support: relay common walk support bodies between reads. The module
uses the concrete readers and preserves the joint-induction premises.
Validation and current claim status are recorded in log.md and state.md.

### CommonSupport

C6 support: transport exact proposer and voter support inputs. The module
uses the concrete readers and preserves the joint-induction premises.
Validation and current claim status are recorded in log.md and state.md.

### CommonScores

Actual raw and support transfers give equal participant counts, cap
status, and scores at every walk candidate.
Validation and current claim status are recorded in log.md and state.md.

### CommonTree

Each current-slot body is the exact honest proposal. Every voter-tree body
is in the proposer tree or on the proposal path, and every proposal prefix
remains in the voter tree.
Validation and current claim status are recorded in log.md and state.md.

### NCounts

C6 support: prove N targets compatible with same-label results. The module
uses the concrete readers and preserves the joint-induction premises.
Validation and current claim status are recorded in log.md and state.md.

### NWalkCounts

C6 support: derive strict N-target score dominance with caps. The module
uses the concrete readers and preserves the joint-induction premises.
Validation and current claim status are recorded in log.md and state.md.

### NReadTransport

C6 support: relay N counts and retain their target prefixes. The module
uses the concrete readers and preserves the joint-induction premises.
Validation and current claim status are recorded in log.md and state.md.

### NNextHead

C6 support: transfer N counts to next HEADs under compatible roots. The
module uses the concrete readers and preserves the joint-induction
premises.
Validation and current claim status are recorded in log.md and state.md.

### NHeads

C6 support: identify exact honest HEAD witnesses for N targets. The module
uses the concrete readers and preserves the joint-induction premises.
Validation and current claim status are recorded in log.md and state.md.

### ViewOrigins

C6 support: trace voter PC views to earlier honest ack targets. The module
uses the concrete readers and preserves the joint-induction premises.
Validation and current claim status are recorded in log.md and state.md.

### RootSources

C6 support: trace next-vote roots to PCs and earlier results. The module
uses the concrete readers and preserves the joint-induction premises.
Validation and current claim status are recorded in log.md and state.md.

### NRoot

C6 support: derive the separate N-target root condition. The module uses
the concrete readers and preserves the joint-induction premises.
Validation and current claim status are recorded in log.md and state.md.

### PCChain

C6 support: order PCs and compare them with results by label. The module
uses the concrete readers and preserves the joint-induction premises.
Validation and current claim status are recorded in log.md and state.md.

### NDissemination

C6 support: derive current ack dissemination from prior label facts. The
module uses the concrete readers and preserves the joint-induction
premises.
Validation and current claim status are recorded in log.md and state.md.

### ReleaseCount

C6 support: bound actual release counts by faulty seats. The module uses
the concrete readers and preserves the joint-induction premises.
Validation and current claim status are recorded in log.md and state.md.

ReleaseCount validation found two private theorem names shared with FGSA.
The helpers now use the pcsa_ prefix. Their statements and proofs are unchanged.
Rerun the full pre-commit list before committing this module.

### LockRetention

C6 support: retain locks through compatible collection and renewal. The
module uses the concrete readers and preserves the joint-induction
premises.
Validation and current claim status are recorded in log.md and state.md.

### ViewRank

The best PC has maximal source slot. A present slot maximum fixes the
selected target when same-slot targets are unique; ack-list equality is
not used.
Validation and current claim status are recorded in log.md and state.md.

### RelayFrames

Clean-local store field facts support new-key provenance and PC
preservation.
Validation and current claim status are recorded in log.md and state.md.

### RelayCollect

Clean saturation gives complete exact-target assembly. A new key requires
a matching added ack; a single completing ack belongs to the resulting
certificate.
Validation and current claim status are recorded in log.md and state.md.

### RelayStore

The admission tail preserves ack growth and traces a new PC key to the
delivered body or ack batch.
Validation and current claim status are recorded in log.md and state.md.

### RelayCarrier

The call installing a new PC key carries the installed whole-PC object
under the slot/root model rule.
Validation and current claim status are recorded in log.md and state.md.

### RelayPersistence

Stage-one reconciliation and all handlers preserve held PCs; clocks
preserve them exactly.
Validation and current claim status are recorded in log.md and state.md.

### RelayOrigin

Every held key has an earlier delivery that accepts its carried whole-PC
object.
Validation and current claim status are recorded in log.md and state.md.

### RelayReceipt

Strict whole-PC relay, exact target-body receipt, and C3 assembly give the
same slot and target at each later honest read.
Validation and current claim status are recorded in log.md and state.md.

### FrozenPCTransport

Each frozen voter PC has a matching slot and full target in the proposer
active PC list. The certificate ack list may differ.
Validation and current claim status are recorded in log.md and state.md.

### CarriedView

Every valid carried PC at an honest proposer slot is the one in the
emitted metadata; receipt includes that PC when it is valid.
Validation and current claim status are recorded in log.md and state.md.

### CommonViews

Frozen PC relay, exact carried metadata, slot maxima, and same-slot ack
uniqueness give equal view targets. Empty views and different certificate
ack lists are covered.
Validation and current claim status are recorded in log.md and state.md.

### BodySlotBounds

Actual admitted bodies have strictly earlier parents and cannot exceed the
current slot before the next proposal.
Validation and current claim status are recorded in log.md and state.md.

### ProposalPaths

The actual proposer head is held, and all proper proposal prefixes lie in
its full tree.
Validation and current claim status are recorded in log.md and state.md.

### CommonEligibility

Zero band floors and equal counts reduce eligibility to the same majority
and duty-slot tests.
Validation and current claim status are recorded in log.md and state.md.

### RetainedProposal

Retained paths and equal inputs transport the parent walk between roots;
the unique eligible new child is the proposal.
Validation and current claim status are recorded in log.md and state.md.

### ProposerReads

Exact pre-tick reads let predecessor CI compare proposer roots with
results. Concrete proposer counts then give parent coverage.
Validation and current claim status are recorded in log.md and state.md.

### RootAgreement

Common view targets and predecessor-result lock bounds give the retained-
walk root conditions.
Validation and current claim status are recorded in log.md and state.md.

### HonestProposal

Actual proposal receipt, common views and counts, retained trees, root
bounds and slot bounds prove the successor headsEqual field.
Validation and current claim status are recorded in log.md and state.md.

### AckResults

Earlier, equal and later label arguments give the full ack/result
compatibility used by the joint record.
Validation and current claim status are recorded in log.md and state.md.

### StorePCInputs

Indexed held PCs, valid carried PCs and exact gate inputs have honest ack
witnesses with the required label bounds.
Validation and current claim status are recorded in log.md and state.md.

### LockWrites

Bounded ack/result compatibility prevents every PC veto of a result-prefix
lock write.
Validation and current claim status are recorded in log.md and state.md.

### ProcessLockRetention

Every delivery preserves a row if all resulting held and valid carried PCs
are compatible with its target.
Validation and current claim status are recorded in log.md and state.md.

### ClockLockRetention

Exact read-field congruence connects clock release counts to the current
clean counts; live rows survive when the count is below their level.
Validation and current claim status are recorded in log.md and state.md.

### GateLockRetention

Gate writes can renew rows but retain every existing target; combine this
with live-row pre-clock retention.
Validation and current claim status are recorded in log.md and state.md.

### RunLockKeep

Deliveries preserve compatible rows; release counts contain only faulty
seats; expiry and gate renewal preserve every live target.
Validation and current claim status are recorded in log.md and state.md.

### JointAux

The successor record and earlier-ack coverage are constructed together.
Label-zero initialization closes the full CleanInvariantClaim with only
standard permitted axioms.
Validation and current claim status are recorded in log.md and state.md.

### CutReads

Actual gate and ack times give full-cut S and selected-PC order. Generic
floor monotonicity proves AvailableMonotoneClaim.
Validation and current claim status are recorded in log.md and state.md.

C6 is committed as 4a92c9e1. All 14 fields and the joint ack coverage
passed the full pre-commit list with only the three permitted axioms.

C5 layer check: Clean/Export cannot import Claims/PC. Keep the concrete
available-output proof in Clean/Export. Put the C5 claim adapter in
Assembly/Small beside C3. Put the later M5 adapter there for the same
reason. Clean safety uses the concrete monotonicity theorem. No claim,
checker, or allow list changes. Recheck the remaining export boundaries.

### CleanOutputs

Joint ack coverage gives dissemination. Completed result origins and
observed ack targets give cross-node safety and both monotonicity
conclusions.
Validation and current claim status are recorded in log.md and state.md.

### GenuineKeys

Only the matching gate clock adds a saved label. Event uniqueness makes
each actual gate input unsaved.
Validation and current claim status are recorded in log.md and state.md.

### GateAdvance

The C6 result chain clears the lock guard. Each fresh gate covers its
result in S, and later available reads retain the honest proposal.
Validation and current claim status are recorded in log.md and state.md.

### PendingGates

An early-cut honest batch gives M1 nonempty results and M2 coverage of
every earlier result, even when the gate follows the cut.
Validation and current claim status are recorded in log.md and state.md.

### StoreCutFacts

Exact lock gate origins and full-cut S order prove LeaseBelowRecordClaim,
the M5 store fact used by the outage assembly.
Validation and current claim status are recorded in log.md and state.md.

### BlockReceipt

Exact acceptance times and strict relay prove CleanBlockReceiptClaim
without changing its inclusive source or after-ticks target readers.
Validation and current claim status are recorded in log.md and state.md.

### VoterAuthenticity

Every raw voter HEAD has an authentic emission. The unique honest duty
prevents caps without a healthy-cut or gate-time premise.
Validation and current claim status are recorded in log.md and state.md.

### PendingNHead

Unconditional honest-seat cap bounds and N-quorum receipt prove M4
independently of the false pending result-to-HEAD claim.
Validation and current claim status are recorded in log.md and state.md.

### HeadCone

`pcsa_clean_heads_cone_past_cut` proves that each honest HEAD covers every
common prefix of the honest predecessor HEADs when `earlyTime (i - 1) ≤ cut`.
`pcsa_clean_heads_cone_at_vote` is its vote-time corollary. The voter and input
helpers stay in `HeadCone.lean`. Root compatibility and both cone theorems
are in `Export.lean`, which imports `HeadCone.lean`. Frozen support uses early receipt,
and the count step uses `Gen.AC.Root.transfer_n2`.
