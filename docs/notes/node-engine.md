# Reference node engine

Scope: the current m = n instance only. Empty Kind/no committee actions, the four-delay runtime, proposer/poll policy and WireRunLaws.selected are existing-design choices,
not a general committee architecture or a frozen committee reinstatement target.
This untrusted instance-side component is outside Blocks/FG. Generic Wire, Engine, Family and
Stages leaves import no concrete supplier. Goldilocks uses the genuine protected codecs and
operations, head-only ordinary draining, then the pre-poll block and message forwarding queues.
The fieldwise view and external-data reshape require no nominal state equality or casts.

RestartSilent concerns only new emissions at nonnegative time. It neither empties nor discards
durable queues. Goldilocks supplies it from Simulation.restart_emits_nil; the restore lemmas
retain outbox, relay buffer, wrappers and both forwarding queues. Publication is same-time;
no future service or new scheduler is asserted. Selection, queue coverage and prefix readiness
are separate run obligations. Per-cut admission needs its own monotonicity/completeness laws.

Full AC Requirements is a separate projection supplier, not a codec or LocalRun consequence.
StoredClockTips takes an explicit node/clock domain and FrameOK; the genuine Goldilocks supplier
proves it on every domain. No collision or regime premise is introduced for output exports.
Lead tips, publication, genesis and authenticated carried-message suppliers remain obligations.

The A0b leaves define the canonical growing trace, LocalRun, collision and regression contracts
for this scoped full-set reference. No old simulation, endpoint or protected source imports them.
Acceptance requires carrier/publication read-back and a genuine consumer validation; compilation
of contracts alone is not proof that their run-law suppliers exist.

The boundary registration changes accepted import configurations: it registers the exposed
milestone definition/statement prefixes, the non-exposed supplier proofs and two Test edges.
Synthetic fixtures check the accepted edges and reject definition-to-proof/Blocks imports and
trusted-to-engine imports. This is not verdict-neutral or permission for future import edges.
A0b adds run/projection vocabulary edges and one exact Regression-to-old-growing-Defs exception;
fixtures accept that concrete regression and projection import, but reject a generic sibling.

## A0b census and supplier audit (full-set reference only)

This is an m = n reference contract, not committee certification or released A1 proof work.
No Domains/retention API, fixed-H corollary or change of reference semantics is introduced.
No committee=univ unfolding is used downstream; any future such rewrite belongs in dedicated
vocabulary lemmas. Params.n=pub.n fixes the identity carrier, not an independent committee size;
the four-delay grid is a timing choice, not a population assumption.

Trace builds every event from actual engine state, expands preorder delivery parts with state
threading, records every cut/post, and stutters after the horizon. It is not witness-selected.
Regression requires exact old canonical trace AND cut-map equality after fieldwise reshape;
StateRegression additionally retains all durable queues and the clock. These are obligations.

### Every inherited Growing.LocalRun field

Names below are in Goldilocks.Simulation; paths are under Lemmas/. M = structural transport,
R = reachable-state/AC supplier, W = wire/authenticity supplier. Classification is not a proof.

| Field | Existing owner/lemma | Class and generic burden |
|---|---|---|
| antitone | Growing/Simulation/Defs.honestKeysAt_antitone | M: permanent compromise |
| init | Simulation/RunSchedule.simTrace_init | M: genuine Node.init |
| grouped | Growing/Simulation/Groups.simTraceAt_grouped | M: event expansion |
| cutLaw | Growing/Simulation/Groups.simTraceAt_cutLaw | R: representation.handler, AC frames |
| wire | Growing/Simulation/Wire.simTraceAt_wire | W: received, own_payload, genesis |
| proposerCredential | Simulation/RunSchedule.simTrace_proposerCredential | W: received, proposer_policy |
| time_nonneg | Growing/Simulation/Schedule.simTraceAt_time_nonneg | M: ExecutionValid/horizon |
| time_mono | Growing/Simulation/Schedule.simTraceAt_time_mono | M: ordered events |
| finite | Simulation/RunSchedule.simTrace_finite | M: finite records, tail time |
| phase_order | Simulation/RunSchedule.simTrace_phase_order | M: event order and fixed tick order |
| tick_public | Simulation/RunSchedule.simTrace_tick_public | M: grid correspondence |
| tick_unique | Simulation/RunSchedule.simTrace_tick_unique | M: engine uniqueness |
| tick_of_awake | Growing/Simulation/Events.simTraceAt_tick_of_awake | M: grid and scheduled tick |
| awake_in_horizon | Growing/Simulation/Schedule.simTraceAt_awake_bounds | M: explicit awake domain |
| awake_of_call | Growing/Simulation/Schedule.simTraceAt_awake_of_call | M: event validity |
| restart_of_sleep | Growing/Simulation/Restart.simTraceAt_restart_of_sleep | M: wake/event order |
| restart_at_wake | Growing/Simulation/Restart.simTraceAt_restart_at_wake | M: wake/event order |
| sleep_of_restart | Growing/Simulation/Restart.simTraceAt_sleep_of_restart | M: wake/event order |
| block_unforgeable | Growing/Simulation/Blocks.simTraceAt_block_unforgeable | W/R: authentic block, own release |
| att_unforgeable | Growing/Simulation/Attestations.simTraceAt_att_unforgeable | W/R: nested provenance, protection |
| msg_unforgeable | Growing/Simulation/Votes.simTraceAt_msg_unforgeable | W/R: original candidates/queues, signer |

NodeRunAt adds genesis_root (Simulation/RunBlocks.simTrace_genesis_root_ok) and carried_message
(Growing/Simulation/Payload.simTraceAt_carried_vote_unforgeable). These are output obligations;
neither follows from codec round trips. Payload enumeration includes support messages.

### Every SimulatesAt field and collision field

| Field | Existing owner/lemma | Class and generic burden |
|---|---|---|
| run | Growing/Simulation/Run.simTraceAt_goldilocksRun | all 23 rows above |
| zero | Simulation/TraceDefs.cutMap_zero | M: canonical count |
| mono | Simulation/Trace.cutMap_mono | M: lengths nonnegative |
| covered | Simulation/RunSimulates.simTrace_covered | M: concatenated records |
| state | Growing/Simulation/State.simTraceAt_state_all | R: boundary/within closure |
| now | Simulation/EngineState.now_eq_lastClock | M: stored clock, restore |
| tick_public | Growing/Simulation/Events.simTraceAt_tick_public_group | R: schedule/order, representation |
| tick_other | Simulation/Trace.eventCuts_tick_other | M: no node cuts off public grid |
| deliver | Growing/Simulation/Events.simTraceAt_deliver | R/W: sequential handlers, per-cut admission |
| restart | Growing/Simulation/Events.simTraceAt_restart | R: actual AC operation, durable queues |
| awake_of | Growing/Simulation/Schedule.simTraceAt_awake_bounds | M: explicit domain |
| awake_to | Growing/Simulation/Schedule.simTraceAt_awake_to | M: horizon |
| block_released | Growing/Simulation/PublishedBlocks.simTraceAt_block_released | R: proposal release, candidate_ready |
| message_released | Growing/Simulation/PublishedVotes.simTraceAt_vote_released | R: queue_coverage, selected, signer |
| att_released | Growing/Simulation/PublishedAttestations.simTraceAt_att_released | R: signing history, candidate/readiness |
| block_relayed | Growing/Simulation/PublishedBlocks.simTraceAt_block_relayed | R: relayBuf, forwarding/gossip |
| message_forwarded | Growing/Simulation/VoteForward.simTraceAt_vote_forwarded | R: emitted_admitted, admission, first release |
| att_relayed | Growing/Simulation/PublishedAttestations.simTraceAt_att_relayed | R: relayBuf, gossip_ready |
| NoCollTransportAt | Growing/Simulation/NoColl.noCollRun_simTraceAt | W/R: CollisionLaws only; no static honesty |
| occurrence | Growing/Simulation/NoColl.occurring_observed_at | R: observed headers incl refused blocks |
| tag_injective/tag_ne_genesis | AsChainShape tagged-root laws | W: root algebra, separate from codec |
| header_digest/header_contents | AsChainShape header/parent/info laws | W: exact serialisation, no proposer equality needed |

### Premise ownership and supplier status

SimulationSuppliers lists codec laws, run policy, genuine RestartSilent, grid/order/proposer,
genesis, header shape and parent genesis/tag decoding (also needed without collisions),
received wire/credential checks, original-candidate/queue provenance, proposal payload view,
message/attestation body separation, per-cut admission,
emission signer/fresh holding, own payload, representation and publication. No final Simulates
witness is an input. Requirements is separate at ProjectionExports; genesis and NoColl are
additional projection inputs. IndependentExports contains no collision/regime/Requirements
premise. OutputValid/Nested alone take StoredClockTips on actual ReachClock; FinalMonotone,
LocalRun, FG reach and read do not. ReachClock is defined from honest bounded engine reads.

Represents names identity, reachable FG, root validity, held-block view and held-message origin.
Closure is explicitly an OBLIGATION at init, boundaries, every duty/candidate/gossip prefix and
handler AC frame, not a theorem. Publication's signing history covers attestations separately;
candidate_ready includes proposal/forward dependencies, and gossip_ready covers relay candidates.
Per-cut false→true holdsMsg is distinct from handler-wide dedup/filter; emitted messages also
need fresh post-holding, and forwarding needs the exact timestamp and first release.
queue_coverage still includes j=number-of-duties, hence empty ordinary outbox there. No delayed
release or restart queue erasure is substituted. Failure to supply this is a STOP, not a repair.

Goldilocks supplies restart/tips in A0a; codec, policy and all new run/representation/publication
suppliers remain unproved here. Existing concrete lemmas identify their source, not automatic
instances of these new records. Lead at dc b1d16519 supplies operation-level RestartSilent in
slowOnly k false, not a lead wire/shape, publication or growing simulation. No fake instance.
The honest-object, reachable-state, collision and first-release obligations remain substantive
A1 work only after a scoped fidelity PASS; compilation alone establishes no supplier existence.

### Committee design-input sites (not a proposed patch)

msgObj and queue_coverage construct original messages signed .poll; the outbox is List Body;
WireRunLaws.selected covers all actual sending actors. Empty Kind has no member actions.
Future SA originals need role/source-slot-bearing vote/ack publication (vote s and ack s−2 use
K_s), all-node processing versus member-only signing, and original-signature-preserving relay
without original-committee membership. FG stays population poll. Compile.kindAt's exact phase
and single optional act need a receipt-window/ordered-publication adapter, preserving interleaved
own admissions and all-node unlock/votedSlot rather than fictitious nonmember own admission.
LocalRun/canonical growing cuts must retain intermediate admissions, nonmember receipt, source
slots and counting cuts. Numeric m=n specialisation is not semantic read/release correspondence.
Committee-owner synthesis was read at revision 6 (the supplied rev5 URL had advanced).
D-POP direction is approved, not its API or sufficiency. Scalar D-KEEP/Params.keep is withdrawn;
D-HEAL is pending audit. No committee redesign is adopted; general committee freeze/A1 is unreleased.

### AMEND/HOLD repair frontier

No supplier assumes LocalRun.msg_unforgeable or NodeRunAt.carried_message. EmittedThrough is
membership in actual per-event operation emissions, without a consuming trace cut or before-cut
conclusion. original_candidates/gossip_originals and queued_messages connect original wire bodies
to that operation history; proposal_payload places proposal dependencies in the prior seen closure.
Generic proof must combine codec authenticity/payload_complete, engine unforgeability or
signed_seen_released, candidate/release provenance, then flatten event records and transport
event order to strict cut order. Growing/Simulation/Votes.released_vote_cut_at and
Payload.block_payload_source_at show the existing derivation frontier, not new supplied conclusions.

att_protected is removed: irrelevant, repeated or conflicting candidates may be refused.
signed_candidate connects an actual local signing to an actual duty candidate (not a release).
prefix_signatures recovers own-signer attestation history from each consumed seen prefix;
signing_conflicts and conflict_domain establish protection only for the relevant signing.
att_ready supplies its other guards; releaseAll then derives release. The concrete source is
Growing/Simulation/PublishedAttestations.tick_att_releases_at: hsign, hbase/hsig4/hsig5 and hprot,
using SigningPrefix.simTraceAt_signings_nonFraming_before. Non-framing/history is a separate
supplier frontier, not a codec fact or blanket candidate protection. These obligations remain
unproved; the repair does not certify their concrete supply or release A1 proofs.
