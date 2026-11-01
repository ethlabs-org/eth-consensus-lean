# P-H1 Round 9 handoff

Status: PREPARED. The remaining critical path is P1/P2 HEAD relay, then P5
and the universal TPerm producer. See P-H1.round9-producers.md for exact inputs.

Commits:

- f37ec73e: selected object receipts, Shared history/service lemmas and
  ordinary/reset source delivery.
- 75f5bda1: selected gate, carrier, retained repair and prior-source scopes,
  with the 24-command production-only strict audit.
- cce7e233: the actual positive fixture extension to horizon 310.

Use healing_proposal_support_scope_recovery for the proposal factory.
Use healing_carriers_recovery for carriers.
Use healing_support_gate_scope_recovery for gates, retaining their selected
GateReceiptGeometry argument. Use healing_gate_receipt_scope_recovery for raw
synchronous gates, retaining enabledness and the actual geometry.
Use healing_repair_head_services_recovery for the actual ip/x/N repair service.
It constructs scopes at each actual honest reader and needs RMonoAll.
Use healing_source_before_receipt_recovery for LossServiceScope.receipts,
passing the named TSrc and RMonoAll producers.

healing_tDel_recovery needs only RecoverySleep₂, TSrc and RMonoAll.
healing_tDelReset_recovery also takes the release floor. P-As can pass
fun h0 _ => healing_low_finality_at_reset_reset E rho hrec.toRecovery₂
  xing cap source w h0.
This is a named proved floor, not an object-service obligation.

The universal TPerm wrapper remains conditional on its phase-service factory.
P-As must not fill that field from the positive fixture or strict audit output.
P-H2 owns its D3 ports and higher aggregates. P-Ou owns Outage failures.
No source in either lane was changed in Round 9.

The fixture extension preserves the old event prefix, proves ExecutionValid
and RecoverySleep₂ for the extended run, and includes the full joined-start
H-time horizon. End-to-end Assembly output still needs the real P5 producer
and the P-H2/P-As contracts. Four adversarial execution replays remain P-H1.
