# SA-PC status

## Derived roots (I9) — 2026-09-29

Plan I9 makes block roots derived. See the dated I9 note in
`CONTRACT.md`. A block has a body, not a root, and `Block.root`
computes the root from the content. Honest `propose` uses body 0
(`Model/Choice.lean:87`). `Block.root_injective` holds for every block,
so the `RootInjective` premise of each regime is a theorem
(`rootInjective_all`). The regime field stays; its removal is a later
plan (plan I9 D6). The parent check is the dependency lookup by root
(`blockKnown_parent_slot_iff_root`, `Proofs/BaseViews.lean`). The block
of a proposal with an unknown parent does not enter the store
(`proposalEnters_missingParent`), and the handler returns the state
unchanged (`admitProposal_missingParent`). A direct PC with a missing
path also leaves the state unchanged (`process_pc_missingPaths`,
`Proofs/CertificateValidity.lean`). One statement changed (a named
exception of the plan): `honest_proposal_views`
(`Proofs/Proposals.lean:55`) now states `b = .node parent s 0`.
`sapcContract_from_engine`, `sapcStrong_from_engine` and `excludes` did
not change. The test file `Tests/CleanInvariantCounterexample.lean`
proves `y_root_lt_x_root` and fills `rootInjective` with
`rootInjective_all`; its four private root helpers are deleted
(I9-A01, see `docs/I9-REPORT.md`).

## Receipt relay — 2026-09-28

The contract now uses DC receipt relay. The previous accepted-object
regime fields are removed. The earlier round notes below describe the
old premise. See the dated relay note in `CONTRACT.md`.

`Proofs/ReceiptRelay.lean` derives `AcceptedObjectRelay` and its healthy
prefix form from execution validity and receipt delivery. It covers
complete HEADs, proposals, and PC envelopes, including duplicate carried
HEAD calls. Existing archive consumers use these derived facts. The
quorum recovery regime also drops its accepted-relay field.

Validation: `lake build` passes all 3,558 default jobs with no errors or
warnings. The public bundle, fast P1, and new receipt/score bridge
`#print axioms` checks use only `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, `admit`, or new axiom was added. All requested
conclusions are proved under receipt relay. No task remains open.

_2026-09-28. Round 22. Base contract frozen at Draft 4.3. All requested claims are proved._

`AvailableChain.SAPC.sapcContract_from_engine` in
[`Proofs/Contract.lean`](../AvailableChainSAPC/Proofs/Contract.lean) proves
`SAPCContract p G E`. It includes every base claim and both P1 fields.
`AvailableChain.SAPC.sapcStrong_from_engine` in
[`Proofs/StrongContract.lean`](../AvailableChainSAPC/Proofs/StrongContract.lean)
proves the full additive strong companion. Both require `G > 0` and
`E.Δ = p.Δ`. No requested proof remains pending.

The base clean and outage claims retain their original fault scopes for
all `a < h`. Recovery uses the unchanged regime with `θrec = 2/3` and
`recoveryFull = true`; this derives `a ≤ f`. Recovery and both recovered
strong fields hold by `2L + G + 8Δ`. All other constants remain those of SA.
The existing SA-PC `fastP1_from_engine` supplies the bundle's fast P1 field.

The recovery proof tracks each finite lease to its actual raw gate,
admission test, and exact deadline, including writes under a vetoed S tip.
It does not assume that every live lease is below S. Fast sources clear
conflicting threshold-τ rows. Fully synchronous slow windows exclude
recent conflicting writes and expire older rows at equality. The shared
SA source induction then gives permanent honest HEAD support.

After the common expiry bound, finite roots lie below the common F4
floor. A shared adoption theorem with an arbitrary source anchor handles
an old PC outside the ordinary genesis walk. Fresh honest proposals get
exact HEADs, extending acks, and a common PC before the same 6Δ gate.
That gate repairs both public outputs and strong. Ordered raw history
proves base safety after repair. Timely-N transfer and authenticated
preparation witnesses order later PC targets, including late reveals.
Rank retention proves recovered strong monotonicity.

No base or companion contract definition, executable rule, or existing
invariant field changed. The shared engine remains unchanged. Shared
proof helpers retain the Grid CO and SA theorem interfaces.

## Quorum participation (r95 rank 1)

_2026-09-28. Additional SA-PC theorems; Draft 4.3 stays frozen._

[`Statements/QuorumRecovery.lean`](../AvailableChainSAPC/Statements/QuorumRecovery.lean)
adds `QuorumRecoveryRegime p G E rho`. It requires `a ≤ f` and
`q ≤ (awakeAt E rho.honest t).card` for `GST ≤ t ≤ rho.horizon`.
Execution validity, root injectivity, synchrony, accepted relay, proposer
recurrence, and the recovery horizon keep their original meaning.
The awake set may change at each duty. The relative two-thirds condition
follows from these count premises; it is not an extra assumption.

The proof uses `awake_batch_late_count` and
`quorum_support_above_floor`: `|D| ≥ h_t ≥ q > 2f`, so a raw strict
majority has support above `f`. The `_quorum` recovery lemmas then carry
this fact through finite-source support, the two-lease boundary, proposal
choice, gate repair, and the ordered recovered history.

The added public results are:

- `sapc_recovered_quorum_from_engine` in
  [`RecoverySafety.lean`](../AvailableChainSAPC/Proofs/RecoverySafety.lean):
  the same `RecoveredAt` conclusion at `GST + 2L + G + 8Δ`.
- `sapc_strongRecovered_quorum_from_engine` in
  [`RecoveryStrong.lean`](../AvailableChainSAPC/Proofs/RecoveryStrong.lean):
  recovered strong agreement, monotonicity, and `6Δ` inclusion.
- `strong_included_quorum_from_engine` in
  [`StrongClean.lean`](../AvailableChainSAPC/Proofs/StrongClean.lean):
  clean `6Δ` strong inclusion under Sleepy, the cap, and an awake quorum.
- `quorum_preparation_ack_service` in
  [`CertificateService.lean`](../AvailableChainSAPC/Proofs/CertificateService.lean):
  per-proposal PC service with an awake quorum at each of the two duties.
  The two seat sets are independent. All honest readers save the timely
  preparation evidence, including readers that are asleep.

`recovery_to_quorum` derives the new regime from the original full
regime. The original public recovery and clean inclusion theorems use
the new results. All existing theorem signatures are retained. The
executable rule, contract definitions, constants, and engine are unchanged.
The source argument is `sapc-improve.md` §§3 and 7.1 and
`sapc-base-recovery.md` §9 in the research `tip-stability/codex` directory.

Validation: targeted checks pass with `--wfail`, and the full
`lake build --wfail` passes all 3,535 jobs without warnings. The 41 new
public theorems all have `#print axioms` checks in the default audit
(912 SA-PC entries). They use only `propext`, `Classical.choice`, and
`Quot.sound`. `git diff --check` passes. No `sorry`, `admit`, project
axiom, or default import of `Pending/` was added.

Pending: none for r95 rank 1. This result retains the fault cap and the
absolute quorum premise. Recovery below that count and protocol changes
from other paper ranks are outside this task.

No Git commit or `lake update` was made. `state.md` and `log.md` were not
changed. Validation used the installed throttle; the first blocked build
was stopped after an elapsed-time and CPU check, then retried with lock
access. No throttle setting changed. All session scratch files were kept
inside this repository and removed after validation.

## Sources and scope

The source directory is
`/Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/`:
`sa-pc.md` §2 supplies the rules and §§4–6 supply the paper proofs;
`sapc-redteam.md` supplies the source-based lease argument and boundary
clarifications; `pc-spec.md` supplies the objects, receipt rules, and
companion shapes; `slow-arming.md` supplies SA.

The base clean and outage statements have no added fault cap. Only the
strong fields explicitly require the cap. The base Recovery regime
derives it from the selected constants. The companion is documented in
`CONTRACT.md`, “Strong companion (additive)”. Round 3 applies the
one-time authorized Draft 4.3 change below. No later contract change
is made.

## Constants and statements

`Statements/Contract.lean` declares `SAPCContract` and `SAPCStrong`.
Fast P1 is now a field of `SAPCContract`, with the requested constants:

- `τ = (n+1)/2`, `f = (n−1)/3`, `q = (2n+2)/3`, integer division.
- `θ = 1/2`, `θrec = 2/3`, `recoveryFull = true`.
- `D_c = D_s = D_f = strongDelay = 6Δ`.
- `L = (4k−1)Δ`, `A_slow = 4(k−1)Δ`, `A_fast = 4Δ`.
- `Π = min(η,L)`, `ρ = 2L + G + 8Δ`.

`StrongInterface` extends `Interface`. `StrongConstants` holds the fault
cap and delay. `StrongArmedRegime` requires healthy genesis delivery and
accepted relay, the cap, `h_t>a` before `b₀`, and `T+Δ≤b₀`. It has no
η-sleepy, budget, certificate-possession, or post-`b₀` field.
`StrongClaims` states clean safety, full-participation inclusion,
unbounded armed persistence, and recovered safety and inclusion.
It does not impose an order between strong and S.

## Model and reuse

`AvailableChainSAPC/Model/` contains five modules:

- `Objects`: signed HEAD data with the original ack, PCs, wire objects,
  raw archive and stamps, immutable-save fields, PC rank state, and the
  base projection. `State.base` is the existing `GridCO.State`.
- `Certificates`: raw exact-target N, distinct-seat PC assembly, admitted
  paths, rank with old-on-tie selection, one-label cap evidence, timely
  saves, and the head-extension ack predicate.
- `Handlers`: non-future raw admission without an age limit; ordinary
  two-target admission through `GridCO.admitVote`; block admission through
  `GridCO.admitProposal`; carried original signatures; PC completion after
  HEAD and path receipt; and structural/actual-handler delivery hooks.
- `Choice`: live cap test, frozen/carried PC selection for HEADs, live PC
  selection for proposals, active path domain, F4 floor, mandatory finite
  root, and original signatures recovered from the archive for proposals.
- `Protocol`: the separate S and prefix-lease PC guards, shared clock
  phases, and the `sapc` inhabitant of the fixed `ProtocolSpec`.

The ordinary base cache contains internal target-only keys. It does not
forge or emit new signatures. Complete payloads stay in the archive and
proposal store; outgoing views select original archived signatures.
Ack-only variants therefore neither equivocate nor consume another base
copy slot. Old raw evidence can complete a PC without replaying a base
vote or a past save.

The model calls shared views, GHOST, eligibility, release, expiry, raw
confirmation, admission levels, and obligation writes. `gateWithPC none`
calls `SA.gate` directly. The model is unchanged in round 2. The shared
schedule proofs now also apply to an arbitrary `ProtocolSpec`; their Grid CO and SA theorem names
and types are retained. Two existing shared lemmas are now public:
`fold_heads_mem_or_equivocates` and `stamp_eq_of_prefix`.
There is no claim that the entire active protocol is a plain-SA run.

## Draft 4.3 applied in round 3

The main `Constants` record now has `fastArmingLag`, with validity bounds
`0 ≤ fastArmingLag ≤ armingLag`. `AvailableChain.stableResilientFast`
uses `FastOutageRegime`: the fast lag replaces the general lag, with
`(n+1)/2` honest awake seats required at every `0 ≤ t < b₀`. The other
outage fields, budget, and persistence conclusion are retained.

SA and SA-PC use `4Δ`. SA's existing `fastP1_from_engine` now takes
this main regime and supplies the new bundle field. Grid CO uses its
general lag and derives fast P1 from general P1. L* uses its general lag
and has a conditional `fastP1_of_general`; its general claims remain
pending. Redundant extra-claim statements and fast constants copies are
removed. The witness `fastOutage` satisfies the fast regime with a fault
and a sleeper; `fastOutage_not_general` proves that its protected read
does not satisfy the general lag test.

The principle is documented in `CONTRACT.md`: tradeoffs go into
constants, not claims; every design must be able to meet every claim
trivially with some constant. The base contract is now frozen at 4.3.
The additive strong companion and SA-PC model rules are unchanged.

## Proved through round 2

- `Proofs/Basic`: all constant validity facts, unconditional nesting,
  quorum/cap inequalities, and the capped recovery support inequality.
- `Proofs/Projection`: exact SA gate projection when disabled or with no
  PC; exact disabled choice and HEAD target; ack-independent base keys;
  no base write on PC installation; retained equal-rank PCs; independence
  of frozen/carried selection from live PC installation; sound ack
  extension; save latching; and mandatory-root coverage.
- `Proofs/Archive`: assembly preserves source fields; receipts retain the
  archive and add only direct or carried inputs; clocks retain it.
- `Proofs/Authentication`: generic engine seat-duty payload uniqueness;
  archived-signature origins at `Run.readAt`; honest archived HEADs were
  emitted and have equal complete payloads at the same seat and label.
- `Proofs/Cap`: archive equivocation counts are bounded by the actual
  fault count at every `Run.readAt`, without synchrony; the capped switch
  is false at every such read; evidence and the switch are monotone under
  receipts and unchanged by the clock.
- `Proofs/GateSources`: raw history is saved despite either veto; the S
  veto does not suppress the loop; the finite veto blocks all lease
  writes; every new exact row has a raw-result prefix, its own admission
  test and PC guard, the passing whole-tip finite guard, and the exact
  gate-plus-lifetime deadline. This reuses `GridCO.writeKeys_row_origin`.
- `Proofs/RecoveryPremise`: the unchanged Recovery regime with the
  selected constants implies `FaultBound (sapc p) (pcFaultCap p) rho`.

Round 2 adds 108 public SA-PC theorems in these interfaces:

- `Proofs/ReceiptState`: PC gates and clocks retain receipt data; receipts
  retain paths; every non-future complete HEAD enters the raw archive;
  member loops preserve these facts. `fold_invariant` applies local
  invariants to actual engine folds.
- `Proofs/Authentication` and `Proofs/Cap`: authentic complete HEADs at
  event inputs, strict-time inputs, and reads; equality of honest HEADs
  across readers; the exact duty-time lower bound; and cap-test soundness
  at all these inputs. No synchrony premise is used.
- `Proofs/Handling`: each raw HEAD call projects exactly to the existing
  `GridCO.admitVote`. Actual direct, proposal, and envelope member calls
  archive the original signature. In the base window they leave the base
  key or two-target equivocation evidence, using the shared SA proof.
  This covers ack variants and third copies at the handler level.
- `Proofs/Acceptance`: each archived signature has a first accepted call,
  including carried signatures; later inputs retain it. Both accepted
  relay premises transfer it to a strict read before the relevant
  deadline. Structural containment alone is not used as acceptance.
- `Proofs/CertificateValidity`: every installed PC is valid in the local
  archive and admitted paths at event inputs, strict-time inputs, and
  reads. Direct ready envelopes archive all witnesses, including those
  of a lower-ranked PC. Later equivocation cannot invalidate a PC.
- `Proofs/FrozenCertificates`: receipts retain the frozen list; a clock
  retains it or appends its current PC. Frozen PCs remain valid. Every
  PC selected for a HEAD is valid, whether frozen or proposal-carried.
  This does not identify a selected PC with a later live PC.
- `Proofs/Quorum`: q-seat sets have an honest witness when `q>a`; two
  such sets intersect honestly under the cap. Raw N targets and PC
  targets are unique at the same label across authentic readers under
  the cap. An installed PC cannot precede its honest ack duty. These
  are same-label facts, not safety across different target slots.
- `Proofs/Rank`: a stored certificate is retained or replaced at a
  strictly higher slot. This holds across public reads without a cap.
  Rank retention alone is not strong prefix preservation.
- `Proofs/Paths`: each stored non-genesis block has an accepted proposal
  source. It is in the unchanged contract root scope. The shared
  `RootInjectiveBelow` premise follows at event and strict-time inputs.
- `Proofs/HeadStamps`: every archived HEAD has a stamp; stamp lists grow
  by append; the first stamp is unchanged at later inputs and reads.
  This does not yet supply the clock and cutoff bounds for timely N.

The source lemma deliberately does not assert that a lease is below S.
The local execution-M gate regression obtains a live X lease while S=Y
conflicts with X. It uses a constructed gate input, not a proved
`ExecutionValid` execution. It is not a contract counterexample.

## Proved in round 3

- Shared `GridCO/Proofs/EngineClock` abstracts the existing clock-order
  proofs over a clock accessor and its three laws. Grid CO keeps its
  previous theorem names and types as wrappers. The module also proves
  local invariant lifting, chronological clock-field origins, and
  append-only field retention. The engine model is unchanged.
- `Proofs/ClockBounds`: the PC gate retains the clock; every clock sets
  its time; every receipt retains it. Local clocks are monotone under
  the valid schedule and bounded by the next event. Required public
  ticks give a lower bound at delivery, including for sleeping readers.
  A HEAD handled in its early window enters the raw archive.
- `Proofs/ReceiptTimes`: all raw HEAD stamps are at most the local
  clock. A signature handled before an early cutoff retains its first
  stamp below that cutoff at every later strict input.
- `Proofs/Handling.process_base_invariant` lifts shared receipt
  invariants through all direct and carried calls. `Proofs/Paths`
  uses it to prove admitted ancestor closure and increasing parent
  slots. Every stored block has a complete admitted path. This uses
  the shared admission proofs, not a separate SA-PC admission model.
- `Proofs/Timely`: saves, including empty saves, have exact prior early
  tick origins and are immutable at later inputs. No save exists before
  its own scheduled early tick. A successful save has an honest exact
  preparation when `q>a`. Under the cap, saved targets at different
  readers agree. A qualifying candidate is saved at its scheduled tick
  under the cap; this is conditional on the local candidate test, not
  a proof of receipt or quorum completeness by that time.
- Every emitted ack names the preceding label and an actual successful
  save at a strictly earlier event index. Its emitted HEAD extends the
  saved target. Every PC in an authentic archive has an honest exact
  preparation source when `q>a`, obtained through its honest ack source.
- `Proofs/FreezeOrigins`: each frozen row, including an empty row,
  names the live PC at its own freeze tick. Frozen lists grow by append;
  later live receipts and clocks retain an existing nonempty selection.
  This does not identify a boundary HEAD's selection with a later PC.

These are intermediate proofs. They do not prove a joint clean
invariant, timely-N transfer, sound strong arming, or recovery.

## Proved in round 4

No model rule, base contract definition, or companion statement changed.
This round continues the receipt and projection work required by step 3.

- `Proofs/BaseReceipts` lifts the shared SA base-stamp invariants through
  SA-PC handlers. Base receipt lists grow by append. Every stored base
  vote and block has a first stamp, and all stamps are bounded by the
  local clock. A tip accepted before a cutoff has its complete admitted
  path before that cutoff; later receipts and clocks retain that fact.
- `Proofs/BaseArchive` proves that every cached base key has an original
  complete signature in the archive. Honest base keys cannot equivocate.
  Early honest handler calls therefore store the exact base key, with
  a stamp before the early cutoff. Outgoing original-signature views
  project to the same base-key lists, in order, and preserve the declared
  support subset. This does not prove the full proposal-merge interface.
- `Proofs/TimelyDelivery` connects a delivered exact-target seat quorum
  and an accepted target path to the local N test. Under the cap, that N
  is saved at the actual early tick. A synchronous-emission corollary
  derives the required HEAD calls from `PartialSynchrony`. It still
  requires the exact honest preparation quorum and accepted path.
- `Proofs/Assembly` proves that first-per-seat selection retains all
  seats and uses only original signatures. A sufficient usable ack
  quorum always assembles a valid PC. The archive scan considers every
  complete candidate. At every reachable state, valid local PC evidence
  implies a stored certificate of at least that target rank. This is a
  rank statement; it does not prove target compatibility.
- `Proofs/CertificateRelay` uses the first accepted calls for HEADs and
  proposal paths. A PC present at a healthy honest read T is valid at
  every honest reader strictly before T+Δ, with a stored PC of at least
  its rank. The post-GST version uses `max(T,GST)+Δ` and the horizon test.
  Sleeping readers are included. The same source argument relays a
  detected `capBroken` proof by those deadlines, including old-label
  and unresolved evidence. No gossip tick or cap is needed for relay.
- `Proofs/AckDelivery` proves PC completion strictly before the genuine
  gate from a delivered ack quorum and admitted paths. The synchronous
  version uses the contract broadcast premise. The deadline is the
  existing 6Δ gate. Exact preparations, covering HEAD choices, and path
  delivery for an honest proposal remain separate obligations.
- `Proofs/ActiveCounts` proves that each detected equivocation in a
  same-label base-cache subview has its target evidence in the archive.
  Active mode bounds this detected count by f, even above the actual
  fault cap. The theorem applies to reachable proposer views. Extension
  to frozen and proposal-merged effective views remains pending.

Shared receipt and uniqueness lemmas in `GridCO/Proofs/Stamps`,
`Receipts`, and `Votes` are exposed or factored for reuse. Existing
Grid CO and SA theorem names and types are retained. No engine definition
changed. All seven new modules contain completed proofs and are imported
by the default SA-PC target. No pending declaration is imported.

## Proved in round 5

No model rule, base contract definition, or companion statement changed.
This round proves the next view and score interfaces for step 3.

- `Proofs/BaseViews` proves that ordinary frozen raw keys remain in
  the base cache, retain their label, and contain their saved support
  subset. Each preceding-label key in an admitted proposal has an
  original complete signature in the raw archive. This includes keys
  omitted by the two-target base cache. The full merged HEAD view has
  those archive sources and the correct label at every engine fold.
- `Proofs/DeclaredSupport` derives the declared support subset from
  actual well-formed delivery events. Frozen and carried support remain
  subsets of merged raw views at event and strict-time inputs. Later
  resolution does not promote undeclared proposal members into support.
- `Proofs/ActiveCounts` now bounds detected equivocators in the full
  frozen/proposal merge by f when the live archive test is active.
  The proof uses archive sources directly, with no actual fault cap and
  no false requirement that all carried keys be in the base cache.
- `Proofs/Floor` proves that a score above the detected count has a
  resolved, non-equivocating declared supporter. The supporter is not
  asserted to be honest. An above-f prefix in an active merged view
  belongs to its declared support path in the active duty tree. The
  deepest floor covers every qualifying prefix of the ordinary walk.
  `choice_covers_of_ordinary_floor` proves local F4 transfer for any
  selected PC, provided that the ordinary walk covers the prefix, its
  score exceeds f, and the finite root is compatible with that prefix.
  These are explicit local premises, not new contract premises.
- `Proofs/EffectiveScores` proves that conflicting scores overlap only
  at detected equivocators when declared support is a raw subset.
  Their sum is at most n+e. Therefore a q-score strictly beats every
  conflicting score in active mode, without assuming the actual cap.
  The valid engine supplies the archive and support premises for the
  merged-view corollary. It does not yet supply the q-score by its
  deadline; timely-N transfer still needs that receipt proof.
- `Proofs/FrozenViews` proves exact ordinary freeze origins through the
  generic engine clock-source theorem. Frozen rows grow by append.
  At an honest reader, including a sleeping reader, the saved view
  after its scheduled freeze is the view of that tick's strict input.
  Later PC receipt, saves, release, and gates cannot replace it.

Three existing pure lemmas in `GridCO/Proofs/Map` are now public for
reuse: `fold_deeper_depth`, `fold_deeper_origin`, and
`preceq_of_compatible_depth_le`. Their proofs and types are unchanged.
The five new modules contain completed proofs and are imported by the
SA-PC default target. No new claim inhabitant is asserted.

## Proved in round 6

No model rule, engine definition, base contract definition, or companion
statement changed. This round adds 42 completed public theorems in six
modules. The modules are imported by the default SA-PC target.

- `Proofs/Proposals` identifies the exact proposer action in the generic
  engine, including its clock. An honest SA-PC proposal carries its
  original raw and support signatures and live PC. Positive slots with
  an awake honest proposer have an actual proposal emission. The block
  is non-genesis and has that slot. No common-choice premise is used.
- `Proofs/ProposalDelivery` proves direct proposal acceptance before
  HEAD, both after GST and on a healthy outage prefix. The execution
  supplies the parent, freshness, and authentication guards. Admission
  stores both the original envelope and its base projection before the
  carried-signature loop. The proposal's entire path has first stamps
  before HEAD, and retains that bound at later inputs. Sleeping readers
  are included. None of these results assumes the fault cap.
- `Proofs/HeadTargets` proves that finite lease targets remain stored,
  using their raw-result sources and shared path closure. It does not
  require a lease to be below S. Both active and disabled choices end
  at an admitted block. Active HEADs use the validity of their selected
  frozen/carried PC. A stored block before HEAD has no future slot.
- `Proofs/HeadEmission` defines the actual duty state and complete
  target-and-ack payload. Every awake honest seat emits that payload.
  Its target was stored strictly before HEAD and its slot is at most
  the duty label. Accepted-object relay puts the target path at each
  honest reader before the early deadline, without a separate gossip
  tick or an explicit path-delivery assumption.
- `Proofs/CertificateService` constructs the honest seat quorum from
  the cap. `full_preparations_saved` proves actual saves and their
  retention at later inputs if all honest preparation choices name the
  honest proposal and all those seats are awake. The engine supplies
  their signatures, handler calls, paths, and early ticks.
  `full_preparation_ack_service` then proves a valid PC before the 6Δ
  gate if all next honest HEADs extend that proposal and are awake.
  It also proves that the stored PC has at least the proposal's rank.
  These are conditional service theorems: they do not prove the two
  choice premises, compatibility of a higher PC, or strong inclusion.
- `Proofs/ProposalViews` proves retention of complete and base proposal
  envelopes through clocks and receipts. The actual honest proposal is
  present at each reader's HEAD. Projecting its original signatures gives
  exactly the ordinary SA payload shape. The shared SA merge lemmas then
  put every proposer raw key and declared support key in the effective
  HEAD views. Proposal-source blocks relay separately to resolve that
  support. These are subset results, not equality of cross-reader counts.

All shared SA proof calls use local base states and the proved delivery
interfaces. No SA-PC run is asserted to be a plain-SA run. No shared proof
module needed a change in this round.

## Proved in round 7

No model rule, shared proof module, base contract definition, or companion
statement changed. This round adds 33 completed public theorems in four
new modules and `Proofs/EffectiveScores`. All are default imports.

- `Proofs/RecentArchive` proves the missing archive-to-base direction
  for recent labels. An archived signature has its base key or two-target
  equivocation evidence. The invariant is preserved by every receipt and
  every chronological clock. Old archive entries need no base receipt.
  The strict-input result applies before proposal time `r+2`, including
  the freeze and gate for `r`. It covers third copies, ack variants,
  carried signatures, and the relay case where the reader already has
  the signature. Strict-input clocks and stamps also give exact raw
  freeze and late-pool identities.
- `Proofs/TimelyTransfer` proves that a timely N supplies score at least
  q in every next frozen/merged HEAD view under accepted-object relay.
  It relays the raw preparations and their target path. A dropped third
  copy contributes through the retained equivocation evidence. Saves
  identify the actual strict early input, rather than later receipts.
- `Proofs/EffectiveScores` uses the shared GHOST path-dominance theorem
  to turn q support into ordinary-walk coverage and then F4 coverage.
  It uses the active detected-count bound, not an actual fault cap.
  `active_voter_quorum_covers` needs only compatible finite roots in
  addition to the active quorum; path and ordinary-walk premises are
  derived from the execution.
- `timely_active_head_covers` and `savedTimely_active_head_covers` connect
  those results to the actual HEAD target. The synchronous and healthy
  wrappers derive their relay interface from the contract premises.
  They retain the finite-root compatibility premise. No choice premise
  is assumed in their conclusions.
- `timely_departure_disables_by_gate` proves the mixed-mode implication:
  if a next HEAD with a compatible finite root leaves the timely target,
  it must have `capBroken = true`. Relay makes that evidence common
  strictly before the same-label gate. This does not prove compatible
  finite roots or the joint induction through the mode change.
- `Proofs/MergedReceipts` proves reverse relay from the entire merged
  HEAD raw view to another reader's same-label late pool, with the exact
  base-key-or-equivocation alternative. It includes proposal-carried
  keys. It does not assert equality of proposal and voter views.
- `Proofs/QuorumGenuine` reuses shared `TransferReceipts` on the local
  late pool. A raw exact quorum and a raw genuine result at the same
  label cannot conflict. `timely_compatible_confirmation` supplies the
  quorum receipts and target path by relay from the strict early input.
  It has no active-mode or fault-cap premise and applies before either
  gate guard. It does not compare targets at different labels.

These results close the timely-N receipt and score gap from round 6.
The finite-root invariant, forward genuine-support transfer, honest
proposal choice, and the requested bundle proofs are still pending.

## Proved in round 8

No model rule, shared proof module, base contract definition, or companion
statement changed. This round adds 25 completed public theorems in three
modules. All three modules are default imports.

- `Proofs/EarlyReceipts` proves that new base stamps use the receipt
  clock and name stored receipts. A stamp below a public cutoff implies
  that the receipt was present at the strict cutoff input. This applies
  to carried signatures, target blocks, and sleeping readers. It does
  not infer an early receipt from later archive membership alone.
- `Proofs/GenuineTransfer` constructs the shared SA `TransferReceipts`
  interface for actual SA-PC gate and next-HEAD states. Early signatures
  and paths reach the freeze. If the two-target cache omits a key, it
  retains equivocation evidence. Reverse relay of the full merged view
  excludes that alternative for a surviving genuine supporter. Thus each
  such supporter is in the actual declared support view and has no
  conflicting copy in the merged raw view. The proof has no fault-cap
  or active-mode premise and includes proposal-carried keys.
- Genuine prefixes have complete paths in the ordinary frozen domain.
  The shared SA walk proof gives ordinary coverage from a compatible
  finite root. The actual SA-PC HEAD covers the prefix if either its
  genuine support exceeds f (any selected PC), or the selected PC is
  compatible with the prefix (no minimum F4 score). Both conclusions
  still require finite-root compatibility. These are local transfer
  interfaces, not proofs that a contract regime supplies the roots.
- `sameLabel_from_engine` proves compatibility of raw genuine results
  at the same healthy label. Both source majorities transfer into one
  actual merged view. Conflicting results would each strictly dominate
  the other. This applies before both gate guards and in mixed modes.
- `Proofs/TransferRegimes` derives the forward and reverse relay
  premises from the fixed contract conditions. Synchronous wrappers
  require GST no later than the early cutoff and a horizon through the
  gate. Healthy wrappers require the healthy prefix through that gate.
  They do not handle a pending gate after outage onset.

This closes the forward genuine-support transfer gap from round 7.
Common honest-proposal view comparison, the joint clean induction,
pending outage transfer, strong claims, and recovery remain open.
No complete contract inhabitant is asserted.

## Round 9: joint invariant and event steps

`Statements/CleanInvariant.lean` defines `JointCleanInvariant` as one
predicate on a run prefix and a common path. It contains ancestry closure,
comparability, honest admitted-path witnesses, actual HEAD continuation
of genuine results, finite lease sources, saved genuine results, S and G,
honest timely-N sources for valid PCs, capped timely/PC path membership,
the false mode flag under the cap, and signature authentication.

Outside the cap, PC path membership is required at its actual authority
uses: gate, HEAD, and proposal ticks. It is not required merely because
an archive holds a valid PC while the local mode is still active. The
paper's failed-N argument disables authority before its first effect;
it does not require storage and disablement to occur at the same instant.
The definition retains historical finite records across mode changes.
It does not assert that every live lease is below S.

Completed proofs:

- `CleanSteps` proves finite-path preservation by every delivery kind,
  expiry, freeze, release, and all clock phases. At a gate it requires
  the raw result to be on the path. It proves that S does not retreat
  under that premise. New lease targets use `gateWithPC_row_origin`.
- `gateWithPC_eq_sa_of_path` proves equality with the complete SA gate
  when the raw result and active PC are on the path. This includes every
  prefix guard and the lease loop. `gate_clean_includes` proves that
  the raw result enters S without any lease-admission premise.
- `CleanConsequences` proves the full invariant at genesis and derives
  finite-root membership, event-by-event record order, record order
  between any two event prefixes, and both output safety statements
  **from the joint invariant**. It does not derive that invariant from
  Sleepy.
- `CleanDelivery` proves that the whole joint invariant survives delivery
  of **any object under plain Sleepy, without the cap**. `q > a` supplies
  an honest ack. Its exact saved value gives an actual timely save
  strictly before the current input, without quorum uniqueness. Under
  the cap that save is also on the path. Outside the cap, delivery stores
  evidence and does not exercise authority. This covers HEADs, carried
  proposal evidence, direct PC envelopes, late assembly, and sleeping
  readers. `jointClean_delivery_of_sleepy` uses the fixed regime directly.
- `CleanTicks` proves the full freeze step without a cap. It proves the
  full proposal tick under the cap, including its live-PC authority.
  Its general between-duty step requires the new proposal authority
  clause when the tick is a proposal time. It does not prove common
  exact HEADs for an emitted proposal.
- `CleanInclusion` proves the actual gate write from the joint invariant
  and reduces both `6Δ` inclusion fields to honest raw proposal service.
  It handles the remainder of the deadline's event prefix by the proved
  record order. The raw proposal-service premise is still unproved.

`Pending/CleanInduction.lean` states the remaining steps as Lean
propositions, with exactly the Sleepy regime and no cap. It is not
imported by a default target. It has no placeholder proof or axiom.
The remaining obligations cover early, HEAD/release, gate, and proposal
ticks and raw honest-proposal service. All three delivery kinds are proved. Early tick
`r+1` and gate `r` are one actual clock call; they are not separate
state changes. The same applies to HEAD and release.

No checked counterexample to a step or contract claim was established.
The open steps below are proof gaps, not claims of false statements.

## Round 10: checked failure of the early-cutoff obligation

`Tests/CleanInvariantCounterexample.lean` constructs a complete run of
`sapc p` from the engine initial state. It proves `ExecutionValid`, the
exact `SleepyRegime`, `FaultBound`, the full round-9 invariant before the
cutoff, and the impossibility of extending its path after that event.
The module is a default import. The checks use kernel reduction; they
use no `native_decide`, placeholder proof, or project axiom.

The parameters are Δ=1, n=4, k=2, η=0, f=1, q=3. Nodes 0, 1, and 2 are
honest and always awake. Node 3 is faulty and is the proposer at every
slot. Thus h=3>a=1 and a≤f. The horizon is 6. The run has all public
ticks at times 0 through 6 and all required self-deliveries.

- At time 1, all three honest HEADs name genesis. Every honest node
  receives them at time 1.
- At time 4, the faulty slot-1 proposer supplies two genesis children:
  X with root 2 and Y with root 1. Every honest node receives both.
- At time 5, all honest HEADs choose X, using the ordinary root tie
  rule. Every honest node receives all three X HEADs at time 5.
- Prefix 42 is immediately before node 0's time-6 tick. The full
  `JointCleanInvariant` holds with `path B := B=genesis ∨ B=Y`.
  The records still equal genesis, finite rows and genuine history are
  empty, no successful N or valid PC exists yet, and Y is accessible
  in an actual honest state. HEAD and proposal PC authorities are empty.
- Event 42 is the actual early tick for label 1, together with gate 0.
  At prefix 43, node 0 has saved `N(1,X)`. The capped `timely` field
  requires X on the next path. Any extension of the old path also
  contains Y. Since X and Y conflict, no such clean path exists.

`before_cutoff` proves the entire input invariant, not only its finite
state fields. `next_save` proves the event and save. `no_extension`
refutes exactly the existential path extension used by `JointEventStep`.
The witness's `sleepy` theorem checks root injectivity, the complete
schedule, wire/dependency/freshness checks, signature provenance,
broadcast, accepted-object relay, and participation. The blocks have
distinct roots. All required deliveries have delay zero, strictly below Δ.

`Pending/CleanInductionCounterexample.lean` then proves
`cleanEventObligations_false`, the negation of the existing
`CleanEventObligations p env`. This module stays outside default imports
because it refers to the pending statement module. It is checked
separately. The pending definitions are unchanged.

The exact defect is the universal quantification over every path that
satisfies the round-9 invariant. `accessible` permits stored proposals;
it does not require that a path member has a genuine or timely source.
The other fields do not restrict extra path members before those sources
exist. This run therefore satisfies the invariant on the losing branch.
It does not show that a suitable path cannot be chosen for the run.

No workaround, weakened premise, protocol change, or contract change is
applied. Preservation as stated cannot be completed. HEAD/release, gate,
uncapped proposal authority, and proposal service remain pending. The
conditional safety, monotonicity, and 6Δ inclusion reductions remain
valid, but this induction cannot discharge their premises as written.
No new unconditional contract claim is asserted.

## Round 11: run sources and shared genuine-history induction

No contract or model rule changes. The proof state is no longer a free
path that can choose a stored losing branch.

- `Statements/CleanInvariant` renames the round-9 predicate to
  `CleanPathFacts`. The new `cleanRunPath p rho index` is genesis plus
  ancestors of actual raw gate results, capped honest timely saves, and
  PC targets used at active gate, HEAD, or proposal duties. It contains
  no source from mere block storage and no uncapped N storage source.
  `JointCleanInvariant p E rho index` has no path argument. It combines
  facts about this set with `OrderedGenuine`; its continuation clause
  refers to actual honest HEAD ticks. Comparability is still a proof
  obligation, not a property built into the path definition.
- Shared `Proofs/HistoryInduction` extracts `GenuineExtends`,
  `GenuineContinues`, and `genuine_history_induction` from the proved
  Grid CO/SA label induction. The existing `clean_genuine_history`
  theorem now uses this common proof. Its statement is unchanged.
  No whole-run SA projection is assumed.
- `RunCleanPath` proves source retention, ancestry closure, the genesis
  path, and inclusion in any old conditional path. Deliveries add no
  path source, including receipts that complete a PC or prove capBroken.
  It proves the new invariant initially and after every Sleepy delivery.
  `RunCleanTicks` reuses the existing local clock proofs for freezes,
  between-duty ticks, and capped proposal ticks. The latter uses the
  installed PC's earlier honest timely save as a canonical source.
- `GenuineHistory` proves unconditional source-closure membership for
  both records, saved raw results, and finite targets. Every reachable
  finite row has an earlier raw gate source at the same reader. A row
  at HEAD r+1 has source label strictly below r, even though gate r is
  still pending. Ordered genuine history therefore supplies finite-root
  compatibility for genuine transfer. There is no lease-below-S premise.
  `clean_genuine_history_of_steps` uses the common induction. Disabled
  transfer uses SA directly; only active transfer needs PC compatibility.
- `Preservation` proves the actual receipt/count bridge for SA-PC:
  honest early base keys survive the late filter; the raw denominator
  is at most the awake honest count plus the faulty count; actual honest
  HEADs and paths reach the strict early input. `preserve_from_heads`
  then invokes the shared SA confirmation theorem.
  `sleepy_preserve_from_heads` derives delivery and counts from the
  unchanged regime. `clean_genuine_history_of_pc` discharges the batch
  step and leaves only active selected-PC compatibility as its input.
- `CleanService` proves that successful N saves and valid PCs inherit
  any prefix covered by the actual honest HEADs at their preparation
  label. The proof extracts an emitted honest exact HEAD. It has no cap
  premise beyond q exceeding the actual fault count. Exact honest HEADs
  at the proposal label give the exact raw gate result by shared slot
  order. Both 6Δ inclusion reductions now need common exact proposal
  HEADs and the corrected invariant, rather than an unproved raw-service
  premise. The safety reduction also consumes the corrected invariant.
- The existing counterexample remains as documentation of the rejected
  free-path statement. Three new kernel-checked tests prove that the
  canonical path at prefix 42 is exactly genesis, excludes Y, and
  includes the actual saved X at prefix 43. The old refutation now names
  `Pending.Rejected.CleanEventObligations`, not the new definition.

The new pending definitions are `CleanEventObligations`,
`CleanPCTransferObligation`, and `CleanProposalChoicesObligation` in
`Pending/CleanInduction`. The old definitions are in
`Pending/RejectedCleanInduction`. None is imported by a default target.
These are proof obligations, not new premises of the contract.

The round-10 counterexample does not refute the new statement. This
round does not prove all its event steps. In particular, source-set
membership alone does not prove comparability, PC first-use authority,
or exact proposal choices. No unconditional clean contract field is
claimed from the conditional reductions.

## Round 12: capped PC sources and HEAD transfer

No contract, protocol rule, or invariant field changes.

- `CleanPCPath` proves that every valid PC at an event input has its
  target on `cleanRunPath` under the cap and execution validity. This
  includes live PCs, frozen PCs selected by a HEAD, and carried PCs.
  It needs neither Sleepy nor an assumed clean invariant. The source is
  the earlier honest timely save supplied by an original ack.
- Under the cap, the canonical path has exactly two source kinds: raw
  honest gate results and honest timely saves, with ancestry closure.
  Gate, HEAD, and proposal PC authority adds no extra branch. A capped
  HEAD/release tick therefore leaves this source set unchanged.
- A selected PC at HEAD `r+1` has target label strictly below `r`.
  This uses `q>a` and the strict input cutoff, so it also holds without
  the cap under plain Sleepy. A current-label PC cannot control that HEAD.
- `RunCleanHeads` derives the finite-root premise from actual rows on
  the input path. Timely-N transfer to the next HEAD now uses the joint
  invariant and the cap, with no extra finite-root assumption. This
  theorem permits a final HEAD with no later gate in the run.
- `CleanTicks` factors its existing proof into a clock step with no
  early save or gate. `RunCleanHeads` uses this step to prove the full
  capped HEAD/release event preservation when the following gate is
  within the horizon. It derives genuine continuation by the existing
  SA batch-preservation and genuine-transfer proofs. The old freeze,
  between-duty, and proposal proofs keep their statements.
- `RunCleanTransfer` derives continued coverage of a timely save through
  earlier HEADs from one current invariant. Its first step uses quorum
  transfer; subsequent steps reuse SA preservation and genuine transfer.
  Finite and PC roots come from the current path's earlier state fields.
  No new timely-continuation field is assumed.
- `selectedPC_prefix_pending_genuine` proves more than compatibility:
  under the cap and the joint invariant at HEAD `r+1`, the selected PC
  target is a prefix of every honest pending raw result at label `r`.
  Its proof uses the strict PC label bound and timely continuation.
  It does not assume that the pending gate is already a path source.
  The gate deadline must be within the horizon.
- `clean_genuine_history_capped_of_head_invariants` supplies this PC
  input to the existing shared SA/Grid CO induction. It still requires
  the chronological invariants at the relevant HEAD inputs. This is an
  explicit proof dependency, not an unconditional clean-history theorem.

The remaining chronological step must add the new timely save and the
preceding raw gate result at the same early/gate tick. It must prove
comparability of these sources, continuation of the new raw result at
the already executed next HEAD, and ordered history. The current
source-membership results alone do not prove any of those three facts.

The full capped HEAD step still has a horizon boundary: its backward
relay uses `gateTime s ≤ horizon` for HEAD `s+1`. A last incomplete
label needs a proof from the available honest batch, or another proved
argument that does not extend the run. No run extension is assumed.
The separate timely-N transfer theorem does not have this restriction.

Above the cap, a stored timely target need not enter the canonical path.
First-use disablement and the mixed-mode steps remain pending. No cap
has been added to a base contract claim. Common proposal choices and
all unconditional clean-field conclusions remain pending. No new checked
counterexample or contract issue was found in this round.

## Round 13: complete capped chronological induction

No contract, protocol rule, or invariant field changes.

- `MergedReceipts` defines the exact reverse receipt condition
  `BackReceipts`. `local_back_receipts` proves it from the reader's own
  archive and the two-copy cache alternative. It includes carried raw
  keys. It needs no future gate tick, relay deadline, or run extension.
- `GenuineTransfer` factors five existing proofs through that receipt
  condition. Their old relay-based theorem statements remain available.
  `synchronous_local_genuine_head_covers` uses the same proof for the
  reader's own pending raw result. Its only relay deadline is the freeze.
  It needs no cap, but retains finite-root and selected-PC compatibility.
- `RunCleanHeads` now proves capped HEAD/release preservation with no
  following-gate horizon premise. `RunCleanTransfer` removes that premise
  from timely continuation and selected-PC/pending-result comparison.
- `RunCleanFacts` proves source accessibility from actual capped raw
  gates and timely saves. It reconstructs all receipt and source fields
  from a comparable source path and genuine continuation. It then proves
  `JointCleanInvariant.restrict_capped`: an earlier prefix has its own
  canonical path and full invariant. It does not reuse the later path.
- `RunCleanGates` uses those earlier HEAD invariants in the shared
  genuine-history induction. It compares raw/raw, timely/timely, and
  raw/timely sources. Equal-label timely saves use quorum uniqueness;
  equal-label raw/timely pairs use preparation relay. Other label pairs
  use actual HEAD continuation. This proves the whole capped early/gate
  step, including the new save, preceding raw gate result, ordered
  history, and continuation through the HEAD already executed.
- `RunCleanCapped` proves every capped event step and then
  `clean_run_invariant_capped` by event induction. The derived
  `clean_safety_capped_from_engine` proves cross-reader safety and local
  monotonicity of both base outputs from Sleepy and the cap alone.
  It has no assumed invariant, path order, or HEAD-coverage premise.

The cap in this helper is explicit. It is not added to any base contract
claim. This closes the capped chronological branch; it does not prove
uncapped clean safety or common proposal choices. No new counterexample
or contract issue was found. Strong claims, both P1 fields, recovery,
and both requested bundle inhabitants remain pending.

## Round 14: uncapped mode changes and first-use transfer

No contract, protocol rule, or invariant field changes. The new helpers
use the existing `JointCleanInvariant` as an input. They do not assume
that every live lease is below S or that an uncapped timely save belongs
to the canonical path.

- `GenuineTransfer` and `TransferRegimes` now require selected-PC
  compatibility only in active mode. The disabled branch uses the shared
  SA transfer proof on the retained base state. The old public theorem
  interfaces remain as wrappers.
- `RunCleanHeads` proves genuine continuation and the HEAD/release step
  when active selected PCs already belong to the input path. Its disabled
  corollary has no PC-compatibility or cap premise. It includes the final
  incomplete HEAD. The capped HEAD proof reuses this step.
- `RunCleanFacts` proves accessibility of all five canonical source kinds
  without a cap. With `q>a`, it reconstructs the source and receipt facts
  from chain comparison and genuine continuation, and restricts an
  invariant to the actual canonical path of an earlier prefix. Sleepy
  supplies `q>a`. The old capped interfaces remain available.
- `Disabled` proves permanent local disablement at later event inputs,
  equality of the complete disabled clock with the SA clock on the
  current base state, preservation at a mode-changing receipt, and the
  disabled between-duty step. This includes proposal ticks. It retains
  raw history and finite sources; it does not reset the state. It is not
  a whole-run SA projection because receipts still contain SA-PC objects.
- `RunCleanUncapped.nextHead_root_prefix_timely_of_run_invariant` proves
  that each finite root at HEAD `r+1` is a prefix of an actual timely save
  at `r`. Each live row has a raw source strictly before `r`; genuine
  continuation puts that source below the save's exact honest HEAD.
- `timely_nextHead_active_of_run_invariant` and
  `timely_departure_disables_of_run_invariant` discharge the finite-root
  premise of the existing transfer and relay proofs. They have no fault
  cap or path-membership premise for the timely target.
- `timely_next_heads_of_active_input` proves that an active honest input
  at or after gate `r` excludes any failed timely transfer at HEAD `r+1`.
  It restricts the current invariant to each earlier HEAD and uses
  permanent disablement. `installedPC_slot_le_at_gate` supplies the ack
  time bound. `gatePC_next_heads_of_run_invariant` applies this result to
  an actual active gate PC.

This closes first-use transfer for an active gate PC, conditional on the
current invariant. It does not yet prove continuation of that PC target
through all later HEADs, comparison of new authority sources with all old
sources, or the uncapped early/gate step. These are the next tasks, before
common proposal choices and inclusion. The combined early/gate tick is
still pending even when its reader is disabled: the chronological proof
must include pending results from the preceding mixed HEAD and retain
old authority sources. Local clock equality alone does not prove that step.

No new checked counterexample or contract issue was found. No uncapped
base safety or monotonicity field is claimed.

## Round 15: complete uncapped safety and monotonicity

- `RunCleanActiveTransfer` proves continuation of every eligible timely
  target before an honest active input. Strong induction on the HEAD
  label uses the first-use disablement result. Finite roots come from
  actual earlier raw sources. Selected PCs have strictly earlier labels
  and honest preparation witnesses. No cap or canonical-path membership
  of the timely target is assumed.
- `selectedPC_prefix_pending_genuine_of_active` puts an active selected
  PC below the pending raw result. The shared SA/Grid CO history induction
  then applies without a cap, from earlier HEAD invariants. Restriction
  supplies those invariants at any current public tick.
- `RunCleanAuthority` proves the first-gate time bound from an honest ack
  and the public tick grid. Above the cap, it classifies actual canonical
  sources as raw results or timely targets with successful first transfer.
  `timely_continues_on_run_path` retains their continuation through later
  active and disabled HEADs. Storage alone is still not authority.
- `RunCleanDisabledGates` compares the pending raw result with every old
  source. It proves the full disabled early/gate step, including pending
  results from a mixed HEAD and retained old PC authority. The common
  early/gate reconstruction is factored through source comparability.
- `RunCleanActivePath` compares all actual sources at an active tick.
  Equal-label timely targets are compared through their common next
  HEAD, without assuming capped quorum uniqueness. This permits new
  active gate, HEAD, and proposal authority to extend the canonical path.
- `RunCleanHeads` factors genuine continuation through PC compatibility.
  Its old theorem interfaces remain. `RunClean` reconstructs the HEAD and
  between-duty steps on the extended path, proves `jointClean_event`, and
  derives `clean_run_invariant` by event induction. The final
  `clean_safety_from_engine` has only the unchanged plain Sleepy premises
  and `E.Δ = p.Δ`. Its two `SafeFrom` conclusions include monotonicity.

This closes the first task in this round's focus. The inclusion review
confirms that proposal delivery and one-way raw/support inclusion are
proved, but common merged-view counts and exact choices are not. The
new invariant does not establish them by itself. In particular, the
shared SA theorem `ProposalViewTransport.of_sets` requires raw-set
identity; the SA-PC two-target cache does not supply that identity.
No new checked counterexample or contract issue was found.

## Round 16: common proposal counts and active F4 floors

No contract definition, executable rule, or invariant field changes.
This round continues step 3. It does not claim exact proposal HEADs or
unconditional inclusion.

- `ProposalOrigins` proves that every stored base proposal has an
  original direct receipt. Proposer authentication fixes the complete
  payload, including the ack-bearing raw signatures, declared support,
  and carried PC. Every current-slot base envelope from an honest
  proposer has that proposal's exact projected metadata.
- `ProposalCounts` proves participant, equivocation, and score equality
  when a raw key can be replaced by two-target evidence at the same
  seat. Score equality needs matching declared support only at
  non-equivocating seats. It does not require equal raw key sets.
- `ProposalMerge` connects these facts to actual engine inputs. Frozen
  raw signatures and their admitted paths relay before proposal time.
  A frozen support key is either in the proposer's declared support or
  belongs to a seat that the proposer knows to equivocate. The carried
  part comes from the unique authenticated proposal. Together with the
  existing forward inclusion proofs, `honest_proposal_counts` gives
  common participant counts, equivocation tests, and scores on every
  block. It works in either mode, with no fault cap or clean invariant.
- `ProposalTransport` proves that the ordinary merged tree contains
  only source blocks and the fresh proposal. It constructs the existing
  `GridCO.ProposalViewTransport` interface for SA-PC. It also proves
  `honest_proposal_active_score_path`: any active HEAD score above f
  has a declared non-equivocating source witness, so the proposer already
  knows its path. That witness need not be honest above the cap.
- Shared `WalkTransport.ghost_prefix_of_score_transport` transports a
  high-score path when extra target-tree candidates score below it. It
  reuses the existing GHOST step and path proofs, including root ties.
  `ProposalFloors.honest_proposal_floor_eq` uses this lemma in both
  directions. The honest proposer and an active HEAD have the same F4
  floor for any selected PC, including in above-cap executions.

The run theorems use the existing synchrony and accepted-object relay
premises, with GST at or before the preceding freeze and a horizon
through the proposal's HEAD. Clean regimes supply these bounds. The
floor theorem also uses the unchanged root-injectivity premise.
Common floors do not identify frozen/carried PCs with a later live PC,
and do not place the finite root on the proposal-parent path.

## Round 17: PC selection and finite-root placement

No contract definition, executable rule, or invariant field changes.
This round continues step 3 and adds 20 public theorems.

- `ProposalCertificates` tracks original stored proposal envelopes.
  Authentication fixes the carried PC as well as both signature views.
  A frozen PC comes from the exact preceding freeze input; accepted
  relay and archive completeness bound its rank by the proposer's live
  PC. The carried PC is valid before HEAD. The selection fold compares
  only these two options and retains the frozen encoding at equal rank.
  The selected rank equals the source rank, including empty options,
  without a cap or clean-path premise.
- `ProposalAuthority` proves that an active HEAD has an active proposer
  source: any prior cap proof relays before the HEAD deadline. Under
  plain Sleepy, the two actual PC authorities belong to the proved clean
  source path. Equal rank therefore gives equal targets even above the
  cap. Together with the common F4 floor, this gives equal preliminary
  anchors. It does not assert equal certificate encodings or equal final
  mandatory roots.
- `ProposerTransfer` constructs the shared SA `TransferReceipts` for the
  actual proposer state. Genuine supporters reflect from the merged
  HEAD view; reverse receipts exclude their equivocation alternative.
  The existing SA support-count and GHOST theorem then puts each raw
  genuine prefix on the ordinary proposer walk.
- `ProposalRoots` proves the proposal-state source-label bound and uses
  the proved clean history to put the source root and every post-release
  reader root below the ordinary proposer result. An active proposer's
  PC has already transferred to the preceding honest HEADs, so its
  target is on that walk too. Shared GHOST reanchoring proves
  `clean_proposal_parent_ordinary` in both modes. All lease arguments
  use raw gate sources, with no assertion that every live lease is below S.
- `ProposalHeads` proves `clean_disabled_honest_proposal_head`. The
  actual target equals the honest proposal; this includes a still-active
  proposer and a disabled reader. It reuses the shared SA proposal
  adoption theorem and the existing slot bound.

The root and ordinary-parent statements require the preceding raw gate
within the horizon. The pending proposal-choice statement already has
the stronger horizon through the proposal's own gate. No regime field
is added. No new checked counterexample or contract issue was found.

## Round 18: exact active HEADs and clean inclusion

No contract definition, executable rule, or invariant field changes.
This round completes the clean inclusion part of step 3 and starts the
local gate part of P1. It adds 13 public SA-PC theorems and one shared
theorem. The historical pending interface also has a proof.

- `ProposalEligibility` uses the existing SA `TransferReceipts` interface
  to show that detected equivocators form less than half of the raw
  proposer view. A previous genuine majority supplies this bound without
  a fault cap. Common scores then give a declared source witness for each
  eligible old block. Authentication identifies every stored block at the
  honest proposal's slot with that proposal. Thus each eligible HEAD
  candidate is either the proposal or a source-tree block. This works
  for all admitted paths, including the enlarged active tree.
- Shared `ProposalAdoption.ghost_adopts_of_eligible_proposal_transport`
  extracts the existing adoption proof with an arbitrary target tree and
  an anchor below the ordinary parent. Only eligible candidates need
  reflection. The original SA/Grid CO theorem is a wrapper with its
  unchanged type; the walk proof is not duplicated.
- `ProposalHeads.clean_active_honest_proposal_head` places the common
  preliminary anchor and mandatory finite root below the ordinary parent.
  It transports the walk through the active tree to the fresh proposal.
  The stored-slot bound gives exact equality. `clean_honest_proposal_head`
  combines active and disabled choices, including mixed modes.
- `Clean.clean_proposal_choices_from_engine` discharges the last clean
  proposal obligation. `included_from_engine` combines these choices with
  the proved run invariant and raw service to give both base outputs in
  `6Δ`. `stable_included_from_engine` and `fast_included_from_engine`
  prove the remaining inclusion fields with the declared constants.
  `Pending/CleanInduction` retains its historical statement and now proves
  it; no default target imports that file.
- `GateAdmission.gateWithPC_writes_admitted_prefix` proves lease acquisition
  from the whole-tip finite guard and the prefix's own PC guard and SA
  admission test. `gateWithPC_arms_vetoed_prefix` allows a PC-vetoed raw
  descendant and needs no earlier lease. It retains S and writes the prefix
  deadline. These exact-deadline statements use the shared map's deadline
  bound as a local proof premise. `gateWithPC_preserves_protected_prefix`
  proves that an existing finite row protects S through an arbitrary gate.
  These are local gate lemmas, not either run-level P1 theorem.

No new contract issue or checked counterexample was found. In particular,
no proof assumes that every live lease is below S, that raw key sets are
equal, or that an above-cap declared witness must be honest.

## Round 19: pending-gate protection and local transfer

No contract definition, executable rule, or clean-invariant field changes.
This round adds 43 SA-PC theorems, two generic engine theorems, and public
access to two existing shared map lemmas. Both contract P1 claims remain
pending. The new `pending_prefix_protection` is a proved internal interface;
it is not a replacement contract claim or an added regime premise.

- `LeaseProtection` proves unique keys, comparable finite targets, lease
  retention through either PC guard, and clock preservation below the
  release threshold. These facts hold during arbitrary delivery and mode
  changes. Comparable targets follow from actual raw sources and the
  whole-tip finite guard. No proof relates every live target to S.
- Shared `ProtectionInduction` extracts the event-interval induction from
  SA/Grid CO's protection proof and the public-read field bridge from
  `Coverage`. The original shared theorem names and types are retained as
  wrappers. SA-PC and SA now use the same first-loss induction. The two
  existing map-fold lemmas are public so the PC loop uses their proofs.
- `OutageProtection` proves that protected honest HEADs respect the finite
  root in both modes. Original archived signatures give a release-count
  bound of at most the static fault count. `protection_from_armed_read`
  retains the row and record prefix until its deadline, with no synchrony,
  participation, or cap premise inside the interval. It includes the
  in-flight HEAD seed and transfer of that seed across a later renewal.
- `GateRead` derives the deadline bound from actual execution. It proves
  first-prefix acquisition at the public gate read, through equal-time
  receipts, even if the PC vetoes the raw descendant. It requires the
  prefix's own PC guard and the whole-tip finite guard. It does not require
  an earlier lease. The old record prefix is an explicit local premise.
- `Preservation` extracts the existing early-receipt and honest-batch
  arguments without changing the synchronous wrappers. `HealthyBatch`
  applies them when only the early cutoff is before the outage. It proves
  a covering pending raw result, its honest support lower bound, and fast
  admission from the high honest count. Later gate delivery is unrestricted.
- `SlowHistory` uses the common clock-source and append-prefix proofs to
  identify and retain every exact raw save, including empty and vetoed
  results. Completed local covering results satisfy the actual slow test.
  The public clock rule includes sleeping readers; missing labels cannot
  be replaced by other results.
- `GenuineTransfer` extracts frozen-receipt and path interfaces from the
  existing cross-reader transfer proof. Its old theorem types remain.
  `LocalTransfer` supplies those interfaces from one reader's history,
  without forward or reverse network relay. The shared SA transfer object
  and walk prove pending HEAD coverage in both modes, given compatible
  finite and selected active-PC roots. No prior covering lease is assumed.
- `PendingProtection.pending_prefix_protection` combines the healthy batch,
  actual prefix admission, local transfer, and first-loss induction. It
  derives `a < τ` from the awake honest majority, without a cap. Its result
  retains the prefix at every read from the pending gate up to its deadline.
  Fast and slow admission have separate proved suppliers. The interface
  still requires healthy-prefix HEAD coverage, the old record prefix,
  the pending finite guard, and active PC compatibility at gate and HEAD.

No new checked counterexample or contract issue was found. These proofs
close the finite-lease and local-transfer parts of P1. They do not establish
the healthy-prefix induction or the pending PC-authority comparison.

## Round 20: both P1 claims and strong clean claims

- Shared `RunPrefix` restricts the event list and horizon while retaining
  indices, states, emissions, handling, acceptance, and authentication.
  `HealthyPrefix` derives Sleepy for a closed finite prefix in a proof
  environment with GST zero and all nodes awake at the final instant.
  State transitions are unchanged. Added boundary emissions have no
  delivery deadline in the prefix. A proved no-proposal boundary condition
  preserves the original root scope. No participation condition at the
  outage boundary is added to the original run.
- `HealthyRun` transports the existing uncapped chronological induction
  back to the original run. It reconstructs authentication in the original
  environment and proves the invariant through an early cutoff, including
  all receipts and the preceding gate at that exact time. This reuses the
  existing capped, above-cap, disabled, and mixed-mode proofs.
- `HealthyHistory` proves continuation of raw sources, pending raw coverage,
  the whole-tip finite guard, and next-HEAD finite-root compatibility.
  Every lease is traced to its actual raw source. No lease-below-S claim
  is used.
- `PendingAuthority` proves that an old timely target continues through
  the healthy batch whenever PC control is active at a later input. It
  reuses the proof that a failed transfer causes common disablement.
  Same-label PCs use honest exact preparations. Honest ack times exclude
  later PCs at the pending gate and bound frozen/carried HEAD selection.
  The resulting prefix guards cover late disclosure and mixed modes
  without a fault cap. They do not promise that a PC accepts the raw tip.
- `RecordHistory` and `HealthyCoverage` derive exact stable-record sources,
  covering HEADs, raw service, and public record coverage. The shared
  record interval proof in `History` now accepts any engine field; the
  original SA/Grid CO wrapper retains its name and type.
- `Outage` closes general and fast P1 with the exact regimes. The last
  completed gate makes the protected prefix common. Records stay fixed
  until the pending gate. The full raw window or the high honest count
  supplies admission there. The proved finite/PC guards and pending HEAD
  seed supply lease retention through the required budget. No interface
  premise is added to either regime.
- `StrongClean` proves PC target order from preparation-label order under
  capped Sleepy. Canonical source comparability gives strong agreement;
  target order and retained certificate rank give strong monotonicity.
  Exact honest proposal HEADs and their continuation supply the existing
  PC service theorem. At the `6Δ` gate, the selected PC has the proposal's
  exact label and target: its rank cannot be lower, and a later label
  would need an honest ack beyond the gate. Strong monotonicity covers
  equal-time receipts. These are the actual companion clean fields.

## Round 21: sound strong arming and unbounded persistence

The exact companion field is now proved:
`strong_resilient_from_engine` in `Proofs/StrongPersistence.lean` gives
`PersistsFrom` for every run with `StrongArmedRegime`. It has no extra
certificate, finite-root, participation, delivery, or duration premise.

- Shared `HealthyInterior` makes any closed prefix strictly before the
  healthy boundary a Sleepy run. It changes only GST in the proof
  environment and retains the original awake schedule. Thus the cutoff
  can contain proposals without adding blocks to the root scope. The
  existing helper for a boundary with no proposal duty is unchanged.
- `StrongArming` reuses the clean induction and PC target order through
  the strict input at `b₀`. Healthy accepted relay gives each honest
  reader a PC that extends the protected target. Every finite entry is
  compatible with that target by its raw source, without a lease-below-S
  premise or a completed slow window.
- `StrongBoundary` transfers the protected PC's timely source through
  the last healthy HEAD batch. Local SA genuine transfer then covers the
  pending HEAD, including an older frozen PC and a carried PC first
  revealed after the healthy cutoff. No outage delivery is used. The
  honest ack time places the protected preparation before that batch.
- `StrongSteps` proves that the prefix lease loop cannot write a
  conflicting entry when the live PC contains the protected target.
  This includes writes made while the whole raw tip is PC-vetoed.
  Release and expiry only remove entries. The F4 score proof counts
  every conflicting score seat as faulty, including the equivocator
  contribution. Under the cap, a conflicting floor cannot pass F4.
- `StrongSelection` proves exact freeze retention, including `none`,
  and rank retention across arbitrary frozen/carried selection. Common
  receipt supplies the rank floor for later freezes without further
  delivery. A late live PC is not substituted for the frozen PC.
- `StrongHistory` uses earlier honest preparation HEADs to exclude
  higher conflicting PCs at the current input. Equal labels use quorum
  uniqueness. An event induction then retains finite compatibility
  from arming through the current HEAD, with no deadline budget.
- `StrongPersistence` closes the induction on HEAD labels. A HEAD uses
  the healthy batch if needed, or an extending frozen/carried PC with a
  compatible floor and finite root. There is no first departure for any
  run horizon. `strongArmed_late_pc_prefix` uses authenticated historical
  preparations to cover all later valid PCs of at least the armed rank,
  including old evidence first assembled or disclosed during the outage.
  Stored rank retention and target containment give the exact public
  strong persistence claim.
- `RecoveryTransfer` starts the next work item. Full participation puts
  every honest seat in the actual late denominator. The raw majority
  test and the derived cap then give support above `f` for every genuine
  prefix. `recovery_genuine_head_covers` reuses the existing F4 transfer
  for any selected PC. Its finite-root compatibility premise is still
  explicit. Its synchronous HEAD boundary does not replace SA's
  proposal-time `SynchronousLabel` boundary.

All new Lean declarations have complete proofs. No unfinished declaration
or new assumption was added to a default target. The shared engine and
both contracts are unchanged.

## Exact remaining work

None for the requested base bundle, fast P1, or additive strong bundle.
Both public inhabitants exist and are included in the default axiom audit.
The files in `Pending/` retain historical obligations and counterexamples;
none is a current missing claim or a default import.

No contract issue or counterexample to a requested claim was found.
The checked round-9 counterexample concerns the rejected auxiliary
free-path obligation, not a contract claim. No premise or conclusion was
weakened to complete recovery.

## Validation through round 9

The 18 kernel-checked Boolean regressions cover old and future HEADs,
ack variants, the two-target cache, per-label unresolved cap evidence,
invalid witnesses, PC retention after equivocation/disablement, late path
completion, first stamps, timely saves and actual-head acks, frozen/carried
selection and rank ties, the repaired prefix loop, the finite guard, F4
and mandatory leases, expiry, equality release, carried cap evidence, and
a complete proposal/preparation/ack/gate replay from the initial state.

`Tests/Axioms.lean` now audits 491 entries: 458 SA-PC theorems and
33 shared theorems. Round 9 adds 37 public-theorem audits.

Targeted checks pass for all new proof modules. The separate pending
statement module also passes (963 jobs). The final `lake build --wfail`
passes all 3,461 jobs with no warnings. Default targets include
`gridContract_from_engine`, `saContract_from_engine`, SA
`fastP1_from_engine`, the unchanged smoke tests, and all public-theorem
audits. Every audited theorem uses at most `propext`, `Classical.choice`,
and `Quot.sound`. `git diff --check` passes.

Round 9 checked the Lean processes before validation. Builds use the
installed throttle with its required lock access. No throttle setting
was changed.

No `sorry`, `admit`, project axiom, or `native_decide` was introduced.
No `lake update` or Git commit was made. `state.md` and `log.md` were not
changed. The temporary validation logs were removed. No session scratch
file remains.

## Round 10 validation

The targeted `lake build --wfail` passes for the default counterexample
module and `Pending/CleanInductionCounterexample` (965 jobs). The latter
prints the axioms of `cleanEventObligations_false`.

The final `lake build --wfail` passes all 3,462 jobs with no warnings.
The default audit now has 497 entries, including all six new public
witness theorems. These six and the separate refutation use only
`propext`, `Classical.choice`, and `Quot.sound`. The default targets still
build `gridContract_from_engine`, `saContract_from_engine`, and SA
`fastP1_from_engine`. `git diff --check` passes.

No `sorry`, `admit`, project axiom, or `native_decide` is introduced.
No contract, protocol rule, or invariant definition is changed. No Git
commit or `lake update` is made. `state.md` and `log.md` are unchanged.
No session scratch file was created or remains. Validation used the
installed Lean throttle; process CPU/time checks were made.


## Round 11 validation

All five new SA-PC proof modules and shared `HistoryInduction` pass
targeted checks. The default audit has 535 entries. It includes every
new public theorem, the extracted shared induction, the refactored
shared `clean_genuine_history`, and the three canonical-path regression
results. All dependencies are limited to `propext`, `Classical.choice`,
and `Quot.sound`; the extracted induction uses only `propext`.

The final `lake build --wfail` passes all 3,468 jobs with no warnings.
The full build retains `gridContract_from_engine`,
`saContract_from_engine`, and SA `fastP1_from_engine`. No base contract,
companion contract, or executable rule changed. `git diff --check`
passes. The corrected pending statement and historical refutation are
also checked separately, outside the default targets.

No `sorry`, `admit`, project axiom, or `native_decide` was introduced.
No Git commit or `lake update` was made. `state.md` and `log.md` were
not changed. Validation used the installed Lean throttle; CPU and
elapsed-time checks were made. Session build logs were kept inside the
repository and removed after validation.

## Round 12 validation

The three new proof modules and the shared clock-step refactor pass
`lake build --wfail`. The separate pending statement and historical
refutation modules also pass. The default audit has 554 entries,
including all 19 new public theorems. Their dependencies are limited to
`propext`, `Classical.choice`, and `Quot.sound`.

The final full `lake build --wfail` passes all 3,471 jobs with no
warnings. The default targets retain `gridContract_from_engine`,
`saContract_from_engine`, and SA `fastP1_from_engine`. The existing smoke
checks and canonical-path counterexample checks pass. `git diff --check`
passes.

No `sorry`, `admit`, project axiom, or `native_decide` was introduced.
No contract definition, protocol rule, or invariant field was changed.
No Git commit or `lake update` was made. `state.md` and `log.md` were
not changed. Lean process checks used elapsed time and CPU use; the
installed throttle was retained. Session validation logs were kept
inside the repository and removed after validation.

## Round 13 validation

Targeted `lake build --wfail` checks pass for the receipt refactor,
HEAD and timely transfer changes, and all three new proof modules.
The separate pending statements and historical refutation also pass
(993 jobs). No pending module is imported by a default target.

The final full `lake build --wfail` passes all 3,474 jobs with no
warnings. Default targets retain `gridContract_from_engine`,
`saContract_from_engine`, SA `fastP1_from_engine`, smoke checks, and
canonical-path counterexample checks. The default audit has 573 entries,
including all 19 new public theorems and the strengthened existing
HEAD/transfer theorems. Their dependencies are limited to `propext`,
`Classical.choice`, and `Quot.sound`. `git diff --check` passes.

No `sorry`, `admit`, project axiom, or `native_decide` was introduced.
No contract, protocol rule, or invariant field changed. No Git commit
or `lake update` was made. `state.md` and `log.md` were not changed.
Lean process checks used elapsed time and CPU use. The first sandboxed
build could not acquire the installed throttle lock; it was stopped and
validation used the same throttle with lock access. No throttle setting
was changed. All session scratch logs were inside the repository and
were removed after validation.


## Round 14 validation

Targeted `lake build --wfail` checks pass for the transfer refactor,
uncapped source facts, HEAD steps, disabled clock and receipt proofs,
and first-use transfer module. The full `lake build --wfail` passes all
3,476 jobs with no warnings. It retains `gridContract_from_engine`,
`saContract_from_engine`, SA `fastP1_from_engine`, the smoke checks,
and the canonical-path regression checks.

The default audit has 594 entries, including all 21 new public theorems.
Their dependencies are limited to `propext`, `Classical.choice`, and
`Quot.sound`. Existing capped theorem interfaces reuse the new proofs.
The separate pending statements and historical refutation are checked
outside the default targets. No pending module is imported by default.

No `sorry`, `admit`, project axiom, or `native_decide` was introduced.
No contract, protocol rule, or invariant field changed. No Git commit
or `lake update` was made. `state.md` and `log.md` were not changed.
Lean process checks used elapsed time and CPU use. The sandboxed build
waited for the installed throttle lock; it was stopped and validation
used the same throttle with lock access. No throttle setting changed.
All session validation logs were inside the repository and were removed.
`git diff --check` passes.


## Round 15 validation

Targeted `lake build --wfail` checks pass for all five new modules and
the factored HEAD continuation proof. The separate pending proposal
statement and historical counterexample pass (1,015 jobs with the audit).
No pending module is imported by a default target.

The full `lake build --wfail` passes all 3,481 jobs with no warnings.
Default targets retain `gridContract_from_engine`, `saContract_from_engine`,
SA `fastP1_from_engine`, and the existing smoke and counterexample tests.
The default audit has 614 entries, including all 20 new public theorems.
Their dependencies are limited to `propext`, `Classical.choice`, and
`Quot.sound`, including `clean_run_invariant` and
`clean_safety_from_engine`. `git diff --check` passes.

No `sorry`, `admit`, project axiom, or `native_decide` was introduced.
No contract definition, protocol rule, or invariant field changed.
No Git commit or `lake update` was made. `state.md` and `log.md` were
not changed. Lean process checks used elapsed time and CPU use. The
sandboxed build could not start Lean; it was stopped, and validation
used the installed throttle with lock access. No throttle setting was
changed. All session validation logs were inside the repository and
were removed after the final check.

## Round 16 validation

All five new proposal proof modules and the shared GHOST transport lemma
pass targeted checks with `--wfail`. The default audit has 636 entries,
including all 22 new public theorems. All dependencies are limited to
`propext`, `Classical.choice`, and `Quot.sound`; six existing entries use
no axioms. The separate pending proposal statement and historical
counterexample also pass (993 jobs). No pending module is imported by
a default target.

The full `lake build --wfail` passes all 3,486 jobs with no warnings.
It retains `gridContract_from_engine`, `saContract_from_engine`, SA
`fastP1_from_engine`, and the existing smoke and counterexample checks.
`git diff --check` passes. No new contract issue or checked counterexample
was found. The exact remaining work is listed above.

No `sorry`, `admit`, project axiom, or `native_decide` was introduced.
No contract definition, protocol rule, or invariant field changed.
No Git commit or `lake update` was made. `state.md` and `log.md` were
not changed. The initial sandboxed build could not start Lean through
the installed throttle; its processes were stopped after CPU/time
inspection. Validation then used the same throttle with lock access.
No throttle setting changed. All session scratch logs were inside the
repository and were removed after validation.

## Round 17 validation

All five new proof modules pass targeted `lake build --wfail` checks.
The default audit has 655 `#print axioms` entries, including all 20 new
public theorems. Each new theorem depends only on `propext`,
`Classical.choice`, and `Quot.sound`. The separate pending proposal
statement and historical refutation also pass (1,034 jobs with the audit).
No pending module is imported by a default target.

The full `lake build --wfail` passes all 3,491 jobs with no warnings.
It retains `gridContract_from_engine`, `saContract_from_engine`, SA
`fastP1_from_engine`, and the existing smoke and counterexample checks.
`git diff --check` passes. No new contract issue or checked counterexample
was found. Active exact HEAD choices and the later claims remain pending
as listed above.

No `sorry`, `admit`, project axiom, or `native_decide` was introduced.
No contract definition, protocol rule, or invariant field changed.
No Git commit or `lake update` was made. `state.md` and `log.md` were
not changed. Validation used the installed Lean throttle with lock
access. Lean process checks included elapsed time and CPU use; no
throttle setting changed. The two session build logs were kept inside
the repository and removed after validation.


## Round 18 validation

Targeted `lake build --wfail` checks pass for the shared adoption
refactor, eligible-path reflection, exact active HEADs, inclusion, and
prefix gate admission. The full `lake build --wfail` passes all 3,494
jobs with no warnings. It retains `gridContract_from_engine`,
`saContract_from_engine`, SA `fastP1_from_engine`, and all existing smoke
and counterexample checks.

The default SA-PC audit has 671 `#print axioms` entries. All 14 new
public theorems and the unchanged shared adoption wrapper are audited.
Each uses only `propext`, `Classical.choice`, and `Quot.sound`. The
separate pending check passes all 1,031 jobs. It checks and audits the
now-discharged proposal-choice obligation and the historical free-path
refutation. No pending file is imported by a default target.

`git diff --check` passes. No `sorry`, `admit`, project axiom, or
`native_decide` was introduced. No contract definition, executable rule,
or invariant field changed. No Git commit or `lake update` was made;
`state.md` and `log.md` were not changed. The initial sandboxed build
could not start Lean through the installed throttle. Its elapsed time
and CPU use were checked, and it was stopped. Validation then used the
same throttle with lock access. No throttle setting changed. All session
logs were inside the repository and were removed after validation.

## Round 19 validation

Targeted `lake build --wfail` checks pass for all seven new SA-PC
modules, the generic induction and read bridge, and the batch and
transfer refactors. The final full `lake build --wfail` passes all
3,502 jobs with no warnings. The default targets retain
`gridContract_from_engine`, `saContract_from_engine`, SA
`fastP1_from_engine`, and all existing smoke and counterexample checks.

The default SA-PC audit has 721 `#print axioms` entries. The 50 added
entries cover all 43 new SA-PC theorems, two generic engine theorems,
two newly public shared fold lemmas, and three refactored shared wrappers.
The full build prints 792 audit results across the libraries. All use at
most `propext`, `Classical.choice`, and `Quot.sound`; both shared fold
lemmas use no axioms. No default target imports a pending module.

`git diff --check` passes. No `sorry`, `admit`, project axiom, or
`native_decide` was introduced. No contract definition, executable rule,
or clean-invariant field changed. No Git commit or `lake update` was
made. `state.md` and `log.md` are unchanged. Validation used the installed
Lean throttle with lock access; process checks included elapsed time and
CPU use. No throttle setting changed. All session logs and the refactor
script were inside the repository and were removed after validation.


## Round 20 validation

All nine new modules pass targeted checks with `--wfail`. The shared
`History` field refactor and the exported schedule filter lemma also
pass. The final full `lake build --wfail` passes all 3,511 jobs with no
warnings. Default targets retain `gridContract_from_engine`,
`saContract_from_engine`, SA `fastP1_from_engine`, and all existing smoke
and counterexample checks. They now also build SA-PC's two P1 theorems
and both capped strong clean theorems.

The SA-PC audit has 777 `#print axioms` entries. The 56 new entries cover
all 52 theorems in the nine new modules, the three new shared public
helpers, and the retained shared interval wrapper. The full build prints
848 audit results. Every dependency is one of `propext`,
`Classical.choice`, and `Quot.sound`, or the theorem uses no axioms.
No default module imports `Pending/`.

`git diff --check` passes. No `sorry`, `admit`, project axiom, or
`native_decide` was introduced. No contract definition, executable rule,
or clean-invariant field changed. No new checked counterexample or
contract issue was found. Strong arming and persistence, Recovery, and
the two bundle inhabitants remain pending as listed above.

No Git commit or `lake update` was made. `state.md` and `log.md` were
not changed. Validation used the installed Lean throttle with lock
access. Process checks included elapsed time and CPU use; the initial
sandbox denied `ps`, so the checks used approved access. No throttle
setting changed. All seven session logs were inside the repository and
were removed after validation. No session scratch file remains.

## Round 21 validation

All eight new modules pass targeted `lake build --wfail` checks. The
final full `lake build --wfail` passes all 3,519 jobs with no warnings.
Default targets retain `gridContract_from_engine`, `saContract_from_engine`,
SA and SA-PC `fastP1_from_engine`, and the existing smoke and
counterexample checks. They now also build the exact SA-PC
`strong_resilient_from_engine` and armed late-PC prefix theorem.

The SA-PC audit has 809 `#print axioms` entries. All 32 new public
theorems are included. The full build prints 880 audit results. Each
dependency is `propext`, `Classical.choice`, or `Quot.sound`, or the
theorem uses no axioms. No default module imports `Pending/`.

`git diff --check` passes. No `sorry`, `admit`, project axiom, or
`native_decide` was introduced. No contract definition, executable rule,
or existing invariant field changed. No new checked counterexample or
contract issue was found. Recovery and both bundle inhabitants remain
pending as listed above.

No Git commit or `lake update` was made. `state.md` and `log.md` were
not changed. The initial sandboxed build could not start Lean through
the installed throttle. Process checks included elapsed time and CPU
use; that build was stopped, and validation used approved lock access.
No throttle setting changed. All nine session logs were inside the
repository and were removed after validation. No session scratch file
remains.

## Round 22: complete recovery and both bundles

- `RecoveryRows` and `RecoveryRelease` connect exact lease sources to the
  actual release snapshots. The shared SA counting theorem handles
  faulty supporters and reverse relay of equivocation evidence.
- `RecoverySupport` reuses the extracted SA source-support induction.
  `RecoveryBoundary` proves the common two-lease boundary, supported rows,
  ordered raw results, and the exact remaining repair interval. It uses
  SA's proposal-time start; it does not substitute a HEAD boundary into
  `SynchronousLabel`.
- `RecoveryRoots` places live finite roots below the proposal floor.
  `RecoveryProposal` proves common selected-PC targets, common anchors,
  eligible-path reflection, and exact honest proposal HEADs. The shared
  rooted adoption theorem retains its original genesis-walk interface.
- `RecoveryService` proves full preparation and ack service and the
  exact current-label PC before the 6Δ gate. `RecoveryGate` proves both
  gate guards and fresh record replacement. `RecoveryRepair` proves a
  common repair within `2L+G+8Δ` and all three recovered inclusion fields.
- `RecoverySafety` uses the shared repaired-record induction to prove
  base safety for all reads after repair and the complete `RecoveredAt`.
  `RecoveryStrong` proves timely-N continuation at the final HEAD, PC
  target order from historical honest preparations, recovered strong
  safety, and the exact recovered strong inclusion field.
- `Contract` and `StrongContract` assemble `sapcContract_from_engine` and
  `sapcStrong_from_engine`. The former includes the existing SA-PC
  `fastP1_from_engine` with its exact Draft 4.3 regime.

All declarations have complete proofs. Default modules import no pending
file. No new run premise, project axiom, or placeholder proof was added.

## Round 22 validation

All new and changed proof modules pass targeted checks with `--wfail`.
The final full `lake build --wfail` passes all 3,534 jobs with no warnings.
Default targets build `gridContract_from_engine`, `saContract_from_engine`,
SA and SA-PC `fastP1_from_engine`, `sapcContract_from_engine`, and
`sapcStrong_from_engine`, plus the existing smoke and counterexample tests.

The SA-PC audit has 872 `#print axioms` entries. The 63 added entries cover
all new public theorems and the changed shared interfaces not already in
the audit. The full build reports 943 audit results across the libraries.
All dependencies are limited to `propext`, `Classical.choice`, and
`Quot.sound`; nine entries use no axioms. Both completed SA-PC bundles
and fast P1 use only those three standard axioms.

`git diff --check` passes. No `sorry`, `admit`, project axiom, or
`native_decide` was introduced. No default target imports `Pending/`.
There is no remaining requested proof or checked contract issue.

No Git commit or `lake update` was made. `state.md` and `log.md` were
not changed. The first sandboxed build could not acquire the installed
Lean throttle lock. It was stopped after process inspection; subsequent
builds used approved lock access. CPU and elapsed-time checks were made.
No throttle setting changed. All session scratch files were inside the
repository and were removed after validation.
