# P-H1 Round 4 producer obligations

Status: PREPARED. Round 3's CLOSED statement is withdrawn. A compiled consumer
is not a regime producer. The lead has not accepted the obligations below as
assembly work. Each OPEN row remains owned by P-H1 until that decision.

Paths below are in AvailableChainFGSAProofs/Proofs/Healing unless stated otherwise.
The common context is p, c, E, rho, [DecidableEq V], [Fintype V], G, DeltaF,
and hrec : RecoverySleep₂ p c E rho G DeltaF. Index, actor, label, phase, reset,
and read arguments must be the ones used by the consumer. They are not arbitrary
post-GST ticks. The goal types below are the exact records, not their consumers.

```text
┌────────┬──────────────────────────┬──────────────────────────────┬────────┐
│ ID     │ Record site              │ Missing goal                 │ Owner  │
├────────┼──────────────────────────┼──────────────────────────────┼────────┤
│ H1e-P1 │ SupportTransfer:22       │ FirstTransferScope           │ P-H1   │
│ H1e-P2 │ SupportHeads:22          │ NextTransferScope            │ P-H1   │
│ H1e-P3 │ SupportLease:44          │ FastSupportScope             │ P-H1   │
│ H1e-P4 │ SupportSlow:18           │ SlowSupportScope             │ P-H1   │
│ H1e-P5 │ SupportPerm:16           │ SupportPermanenceServices    │ P-H1   │
│ H1e-P6 │ RepairH6:20              │ RepairHeadServices           │ P-H1   │
│ H1e-P7 │ RepairGate:17            │ RepairGateScope              │ P-H1   │
│ H1e-P8 │ FrontierRead:21          │ FrontierReadScope            │ P-H1   │
│ H1e-P9 │ DescentLossCause:43      │ LossServiceScope             │ P-H1   │
│ H1e-P10│ PostResetRaw:22          │ RawServiceScope              │ P-H1   │
└────────┴──────────────────────────┴──────────────────────────────┴────────┘
```

H1e-P1, OPEN: `FirstTransferScope E rho ix iy x y s`. The source must be enabled
at ix and the receiver must be joined at its release read iy. Construct the
forward/backward HeadRelayServiceScope fields for the actual clean/read votes,
the local epochs, targets with the receiver floor, and HeadCarrierServices for the selected receiver. Its relay field is guarded
by HeadCarrierDemand; its direct field serves only the actual HEAD identity
under the receiver floor. No unrelated HEAD creates a receipt obligation. SupportRelay:549 constructs one accepted proposal's
ReceiverService at the earlyTime anchor. It does not construct this record.

H1e-P2, OPEN: `NextTransferScope E rho iy y s`. Supply the selected joined-seat
batch and release count, the actual headVotes rival bound, fresh emitted HEAD
services, retained read provenance, the read epoch, and selected carrier service.
SupportRecovery:81 proves joinedness only with its real previous-slot cutoff.
It does not prove a batch or services at every post-GST vote. No `.joined` field
remains that asserts joinedness of every honest voter.

H1e-P3, OPEN: `FastSupportScope E rho s v x` for the active fast source x, s,
and bounded interval v. Supply source enabledness, firstReaders at the actual
s+1 read, the guarded first factory, next reads, enabled gates and their selected
batches, selected carriers, and same-label service. The firstReaders goal is
`joinedAtTime p (storeAt p c E rho iy y).restartTime (SA.releaseTime p.toParams s)
= true` at each demanded first receiver tick. GST <= voteTime s does not prove
it. The phase/read supplier must prove it from its actual join window or provide
an actual join fact. This is an OPEN producer obligation, not a harmless field
or an accepted H2 assembly item. firstOn and mono are consumers.

H1e-P4, OPEN: `SlowSupportScope E rho s v x` for the actual slow body. Construct
its FastSupportScope phase, the enabled source's late ProposalSupportScope, and
SameLabelServiceScope only on the saved window s+1-k .. s. mono is a consumer.

H1e-P5, OPEN: `SupportPermanenceServices E rho`. At the actual guarded phase
body, construct the fast or slow scope and the demanded proposal scopes. An
actual source body and a PhaseInterval do not by themselves prove firstReaders
or object receipt service. healing_phase_transfers and healing_tPerm consume
this record; neither is its producer. No public TPerm statement was weakened.

H1e-P6, OPEN: `RepairHeadServices E rho s`. Its prior factory is now guarded by
the actual proposal emission N at ip. Construct the prior ProposalSupportScope,
TargetReceiptService and RetainedServiceScope at each actual joined receiver.
SupportRecovery:256 consumes these inputs in repair_head_exact. RepairH6's
repair_h6_input derives elementary H6 geometry; it does not produce the retained
object-history or score-service fields.

H1e-P7, OPEN: `RepairGateScope E rho s`. At the repaired label, supply the true
cut, gate receipt scope, first-transfer service and selected carriers. The cut
is an explicit local hypothesis. Do not derive it from GST <= voteTime s.

H1e-P8, OPEN: `FrontierReadScope E rho q v`. Supply the actual confirmed seed
readers, seed scopes, fast scopes only for actual fastWriteAt members, slow
scopes only for actual eligible slow results, prior/next read scopes, and
selected carrier service. mono only restricts an existing scope.

H1e-P9, OPEN: `LossServiceScope p c E rho`. Its first factory now takes the
actual nonempty source result covering B. Its fast factory takes the actual
postClock state and fastWriteAt membership of B. Construct their local scopes,
next read scopes, same-label high-source service and floor-guarded receipts.
HighSrcN alone does not name a complete object-service producer.

H1e-P10, OPEN: `RawServiceScope p c E rho`. Construct late/proposal scopes only
at the stated real source cut, first scopes at enabled sources and joined
release readers, gate receipt scopes only at enabled actors with actual GateReceiptGeometry,
and same-label scopes. The selected batch is a separate input of the bounded
healing_output_moving_suffix consumer, not a global RawServiceScope field.
The unused universal next factory was removed. The reset consumer derives the
source and receiver cuts from H0Reset's shifted cut and its actual fresh row.
Generic raw adapters now expose the real source cutoff or actual reader join
as an input. They no longer infer either from a post-GST vote time.

Additional local inputs: ProposalSupportScope (SupportProposal:18) uses selected
joined seats and actual proposal/late rival bounds. HeadCarrierScope
(SupportFrame:178) selects one K/W witness per receiver, with fullTree, HEAD
identity, ancestry, source floor and receiver-finality compatibility facts.
SupportGateScope (SupportGate:17) contains a GateReceiptScope and a selected
joined-voter batch. Their full object-service assembly also remains OPEN.

Named partial producers, separate from consumers:

- Foundations/Store:35,39,46,153: fgsa_rStoreDurable, fgsa_rStoreEpoch,
  fgsa_rMonoAll, fgsa_rFrameNextEpoch. These supply kept storage, local epochs
  and monotonicity. They do not supply receipt history or carrier service.
- SupportRecovery:81: healing_recovery_joined, with its exact cutoff.
- SupportRecovery:146: healing_recovery_gate_scope, with a real actor cutoff
  and the explicit fresh HEAD/target services. This produces GateReceiptScope.
- SupportGate:36: healing_support_gate_scope_of_cut constructs SupportGateScope
  from RecoverySleep₂, a real source cutoff, horizon and GateReceiptScope.
  The direct joined-batch route needs no sufficient GST cutoff.
- SupportRelay:549: healing_transfer_proposal_service constructs one
  ReceiverService from an accepted named proposal, joined receiver, delivery
  law, aligned earlyTime anchor/deadline, and exact non-exclusion.
- Shared/CatchUp:416,421: fgsa_target_service_genesis and
  fgsa_target_service_of_proposal construct the corresponding TargetReceiptService.

healing_head_carrier_receipt, healing_head_witness_relay_on,
frontier_head_relay_on, healing_support_gate_cover, firstOn, and the permanence,
repair, loss, raw, and frontier theorems consume these services. They are not
named producers for an aggregate scope.

Settlement is also narrowed: PhaseSettle:376 healing_settle_start_on and the
AttemptSettle factory demand service only for W whose height is the actual
source frontier. They keep its receiver-finality compatibility guard. The
consumer proves that floor guard from RXing, the cap and durable W membership.
It does not produce the remaining TargetReceiptService. This local supplier is
OPEN for H2's assembly; it is not the old universal durable-TF requirement.

Final admissibility refinement: HeadCarrierServices (SupportFrame:190) is the
carrier-factory result. relay takes HeadCarrierDemand (SupportFrame:111) before
returning HeadCarrierScope. direct takes the selected stored K, its actual HEAD
identity and the receiver floor before returning TargetReceiptService. Thus no
factory must invent an admissible witness for an unrelated source or receiver.
healing_head_carrier_demand_phase (SupportFrame:122) produces geometry from the
actual PhaseInterval, RXing and valid read. The explicit P-Fd RMonoAll input supplies later
floor monotonicity in direct read consumers. These are named geometry suppliers,
not aggregate object-service producers.

SupportGate:23 healing_support_gate_scope_of_batch assembles a receipt scope
from an actual joined-voter batch. SupportGate:115 healing_support_gate_geometry
produces geometry from the actual covering HEADs and receiver floor. The raw
moving-output consumer takes hBatches only on its bounded source/read labels.
Enabled empty gates no longer force a global selected-batch obligation.
