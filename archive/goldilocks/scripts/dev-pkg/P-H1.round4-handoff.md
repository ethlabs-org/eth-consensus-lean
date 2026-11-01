# P-H1 Round 4 H2 handoff

Status: PREPARED. Public Claims/Statements are unchanged. The sites below are
H2 consumers. No H2 file was edited. Producer status is recorded separately in
P-H1.round4-producers.md; a local receipt theorem is not a service producer.
Paths use Healing/ and Tests/ under AvailableChainFGSAProofs. Review coordinates
refer to e9536241 and still identify the unedited H2 calls on this base.

Required omitted sites from the closure review:

- Healing/AttemptRows:206, healing_attempt_settle_start. Pass RMonoAll before
  the selected-carrier service factory, then crossing and the existing inputs.
  Use RecoverySleep₂/HealingSet. The factory in AttemptSettle:15 now requires
  `(heightView p W).h = frontierAtIdx p c E rho (i + 1)` and compatibility with
  receiver finality at ev.time + Delta. It does not serve every durable block.
- Tests/HealingAttempt:284,312,340,368. Thread exactly the same RMonoAll and
  selected-carrier services through the four settlement adapters. The scopes
  remain inputs unless a named producer from the producer inventory supplies them.
- Healing/FrontierSearchGap:276, FrontierSearchTop:465,
  FrontierSearchRepair:216. Replace healing_settle_start with
  healing_settle_start_on. Pass RMonoAll, the selected frontier-height carrier
  services, and receiptIdealization. Keep the source event and strict read cut.
- Healing/Repair:87. The canonical repair_head_exact supplier is
  Healing/SupportRecovery:256. Pass the actual honest proposal emission, joined
  HEAD receivers, elementary H6 inputs, TargetReceiptService and
  RetainedServiceScope. Alternatively use RepairH6.repair_head_exact_legacy
  with its current RepairHeadServices input. Its prior field now takes N and
  the actual emission membership. No history comes from previous processing.
- Healing/Repair:91. Replace exactService_of_head_recovery by
  repair_exact_service_on (SupportRecovery:190) or the corresponding _on
  exact-service route. Supply joined HEAD/count facts, the true previous-slot
  cut, local gate scopes, receiptIdealization and ExactServiceGateGeometry.
- Healing/FrontierServiceGate:171. Replace the legacy frontier_head_relay call
  by frontier_head_relay_on (FrontierSupportFrame:201). Use receiptIdealization
  instead of idealization. Its service input is now
  `HeadCarrierServices E rho jz z s y`, for the actual receiver y. Pass hy
  before that service. The result gives Kfg membership only at this receiver.
- Healing/FrontierServiceGate:177. The old hrelay result also needs receiver
  awake at voteTime s + Delta. The _on route uses the selected per-receiver
  service and keeps content through fgsa_store_durable; it needs no global
  NoRestart. Keep the actual source HEAD identity and capped frame facts.

Additional Round 4 contracts for H2 consumers:

- FirstTransferScope.carriers, NextTransferScope.carriers,
  ProposalSupportScope.carriers, FastSupportScope.carriers,
  RepairGateScope.carriers and FrontierReadScope.carriers now return
  HeadCarrierServices for the receiver. Its relay field takes an actual
  HeadCarrierDemand (fullTree K, HEAD identity, W, ancestry, source floor,
  receiver-floor compatibility) before supplying HeadCarrierScope with service.
  Its direct field serves the selected stored K under HEAD identity and receiver
  floor guards. Phase and capped-read producers supply those geometry guards. Do not supply
  a service factory for all source TF blocks.
- healing_head_witness_relay_on takes the actual receiver's honest proof and
  HeadCarrierScope, and returns HoldsBefore only for that receiver. Its
  ancestor closure is obtained from the selected W receipt. The capped relay
  keeps one HEAD K identity and obtains its receipt per receiver.
- NextTransferScope and ProposalSupportScope have no universal joined field.
  Use healingJoinedSeats_mem at the selected seat to get its actual join.
  The record supplies the selected batch and the actual pool's rival bound.
  ProposalSupportScope also supplies the actual late pool's rival bound.
- healing_support_gate_cover and healing_output_gate_step take
  SupportGateScope. They no longer take a sufficient previous-slot GST cut.
  Gate factories take enabledGateAt as a guard. Suppressed actors produce no
  write/service demand. healing_support_gate_scope_of_cut is a partial
  producer only when the caller has its real source cut and receipt scope.
- FastSupportScope.first is guarded by source enabledness and the actual
  release-reader join. firstOn assembles those guards from source and
  firstReaders at this source label. It is a consumer, not a producer.
- FrontierReadScope.fast/slow require the actual written body or eligible
  slow source result. LossServiceScope.first requires its actual nonempty
  source result covering B; LossServiceScope.fast requires its actual
  postClock state and fastWriteAt membership.
- RawServiceScope.late/proposal use real source cutoffs. Its first factory
  requires an enabled source and the joined receiver release read. Its gates
  require the enabled actor, without the false GST <= previous-slot cut.
- healing_gate_result_supporter (PostResetRaw:189) now takes the real source
  cutoff immediately after hgst. Update PostResetRawStep:771 and the calls in
  PostResetLeaseStep:317,731,750,1419. Use the actual reset/read cut supplier;
  do not infer it from hgst alone.
- healing_first_transfer_raw_domain (PostResetRaw:327) now takes the actual
  release-reader join after hiy. Update PostResetRawStep:215 and its test
  adapter at Tests/HealingPostResetRawStep:85.
- healing_proposal_moving_domain (PostResetRaw:1636) and
  healing_proposal_moving_parent (PostResetRaw:1794) now take the real source
  cutoff after hgst. Update PostResetRawStep:685,
  PostResetLeaseStep:1214 and Tests/HealingPostResetRawStep:244.
- Tests/HealingPostResetRawStep:68 also needs the source cutoff for the
  supporter adapter. All changed RawServiceScope inputs from earlier rounds
  still have to be threaded; these extra guards do not replace those inputs.

The Round 3 handoff remains applicable for other H2 sites. The explicit rows
above close the inventory omission, not the consumer ports or scope producers.

Final additional contract: healing_output_moving_suffix now takes hBatches after
hgst. Its exact type is:

```lean
∀ l, s + 1 ≤ l → timeIdx rho (SA.voteTime p.toParams l) ≤ cut →
  Gen.Pure.Batch (joinedHonest p E rho (SA.voteTime p.toParams l)).card
    (Gen.V2.Duty.faulty rho).card
```

Thread this at PostResetRawStep:897, PostResetLeaseStep:1577 and
Tests/HealingPostResetRawStep:263. Use actual joined counts, or derive them with
a real reset/read cutoff through SupportRecovery:118. RawServiceScope.gates now
returns GateReceiptScope only after the enabled actor and actual
GateReceiptGeometry are supplied. It does not assert a batch for every enabled
gate. The bounded consumer constructs SupportGateScope using its local hBatches.

Monotonicity is an explicit P-Fd input at the direct selected-HEAD consumers.
Pass RMonoAll after hrec to healing_next_transfer_domain and the two unanimous
adapters. H2 sites: PostResetRawStep:552, PostResetLeaseStep:1094 and
PostResetH2Prime:268. Pass it after RawServiceScope to
healing_proposal_moving_domain and healing_proposal_moving_parent at
PostResetRawStep:685, PostResetLeaseStep:1214 and the test adapter at :244.
Use the actual fgsa_rMonoAll supplier at assembly; do not import Foundations
into the Healing lane. The consumer projects its F monotonicity field.
