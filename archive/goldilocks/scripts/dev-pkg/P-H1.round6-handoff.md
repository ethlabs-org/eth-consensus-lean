# P-H1 Round 6 H2 handoff

Status: PREPARED. This file supersedes the Round 4 H1 service interface notes.
All ten aggregate producers remain OPEN/P-H1. Their exact goals and the lower
carrier/proposal/gate, receiver-floor and local lease-cover obligations are in
P-H1.round6-producers.md. P-H2 aggregate files were not edited. No P-As or P-Ou
file, public Claim/Statement, model, checker or baseline was changed.

The contract is healing-contract-34d9aa77.md, sections A-F. SCOPE-NARROW rules
1-5 apply. The current notes also contain provisional TPERM-WINDOW at 16:02.
It refutes the expected joined-reader-only repair and proposes a source-batch
window. The ruling is provisional; public text remains unchanged in this job.

1. OpeningServiceScopes.transfers: keep the actual phase/source, LabelSyncOn or
   hSync, enabled source and actual joined release reader. P1's local route uses
   GST <= vote(s), not an invented all-honest source batch. An executed
   joinedAtTime guard is converted to the environment join by
   healing_joined_tick_of_guard. OpeningServiceGate:92,373 and
   OpeningServiceBody:229 must pass the actual phase-indexed P5 record, then
   HealingWindow 1, head/gate bounds and PhaseBody to healing_tPerm_at. The result
   is Transfers at that body/endpoint. No old global healing_tPerm exists.
   An early opening source does not acquire Window 1 from hSync. The provisional
   local FAST-only route at GST <= slotStart(s) remains an exact open producer
   obligation; do not request a slow current batch through that route.

2. RepairServiceScopes.heads (Repair:25) and FrontierServiceScopes.heads
   (FrontierService:28): return `RepairHeadServices E rho s ip x N` for the
   exact emitted signed proposal. Take `HealingWindow p E 2 s`. The existing
   integer slotStart(s-2) cutoff supplies this window through
   healing_window_of_cut; it is not interchangeable with the current-batch cut.
   Repair:119 and FrontierSeed's prior projection use `hHeads.prior` directly.
   There is no stored targets field. Supply the actual reader floor, then use
   `hHeads.target hy hi hJoin hFloor` and `hHeads.scopes y hy ih hi hJoin hFloor`.
   Repair:128 and FrontierSeed's repaired-head call need these two callbacks.
   Preserve the canonical SupportRecovery.repair_head_exact telescope, the exact
   seat/signed emission and all RetainedH6Input/ScoreRunGeometry facts.
   H1g-H6-FLOOR is the exact open floor proof, not a service input from emission.

3. RepairGateScope now returns GateReceiptScope after the enabled gate and its
   selected GateReceiptGeometry. Repair:135 onward and FrontierService:99 need
   this geometry before requesting the factory. Return the receipt scope
   directly; `.toGateReceiptScope` applies only to a SupportGateScope.
   FrontierServiceCover:106,378,390,406 must pass each existing hgeom or construct
   it with healing_support_gate_geometry from covering HEADs and F <= B.
   FrontierServiceGate:37,39 must preserve the actual tick, enabled gate,
   geometry, receiver join and bounded read when constructing RepairGateScope.
   Its first callback also takes enabledness and the actual next-label join.

4. FrontierServiceScopes.read: derive Window 1 at q from the actual qualified
   seed's prior-slot cutoff and prove gate(q) <= v <= horizon. P8.readers keeps
   the inclusive afterTicksIdx(gate(q)) confirmed read. RecoveryScope's proved
   healing_recovery_gate_reader is the named reader route on this base.
   P8.slow takes GST <= vote(w+1-k) immediately after its gate/end bound.
   FrontierRead's synchronous branch now passes hgw; the old-window branch uses
   the saved q result. It does not request retrospective pre-GST SameLabel.

5. All aggregate carriers have this exact receiver boundary:

```lean
∀ r, q + 1 ≤ r → ∀ iy y t, t ≤ v → HealingCarriersAt E rho r iy y t
```

   First/next/proposal records fix their own receiver and actual read time.
   FrontierServiceSupport:89,127 must select ip/x/proposal(r+1), derive the
   current r window and use healing_carriers_window_at for that fixed reader.
   frontier_pivot_held now takes services only for its actual receiver, not an
   additional all-honest receiver quantifier. FrontierServiceGate:225 must use
   its actual gate/read tick. Request service after hSync, HealingJoinedTick,
   early(r) <= t and t <= horizon, then the source's actual honest joined vote.
   A non-tick event index cannot be supplied as iy. Choose an earlier joined
   public-grid tick and retain the selected witness to the event durably.

6. FastSupportScope.firstReaders is removed. firstOn takes the endpoint bound
   and actual joined reader after the two tick arguments. Next callbacks also
   take that actual receiver join. Gate callbacks take enabledness, B and the
   actual geometry. SupportLease's two gate calls, SupportSlow's corresponding
   calls and SupportOutput were changed together. The bounded output consumer
   serves its selected witness at its actual earlier gate tick and keeps it to
   the later output. Its source TF is not a global receiver receipt factory.
   Head/proposal current-batch consumers expose their real source window.
   The fast lease and frontier fast transport consumers use only the source
   slot cut when that is sufficient for their actual next-label reads.

7. RawServiceScope.late/proposal use Window 1 and the actual read time. Raw.first
   uses the source-sync bound, enabled source and environmental receiver join.
   The old executed release guard adapter remains and proves that join locally.
   Raw.gates keeps enabledness and GateReceiptGeometry. No universal next or
   output-batch field was added. The actual reset/read cut supplies its window.
   Pass Window 1 after NextTransferScope in healing_next_transfer_domain and
   the unanimous adapters at PostResetRawStep:552, PostResetLeaseStep:1094 and
   PostResetH2Prime:268. Supply RecoverySleep₂ rather than its Recovery₂ projection.
   High-source consumers derive the window through healing_high_source_window;
   they do not change HighSrcN or assume that a name implies a cutoff.

8. RepairH6/RepairH6S: the one-lease/two-lease cover adapters consume an exact
   `RepairLeaseCover E rho s` at the actual repaired label. Their old route through
   a supposed recovery supplier of global TPerm is gone. The cover and the
   receiver-floor proof are separate OPEN/P-H1 obligations. The repaired-head
   adapters keep Window 2 at the exact proposal. The provisional ruling calls
   for a read-local one-lease k=2 proof; no window is asserted for every body.
   RiseOneAdvance uses the actual phase-indexed services and source Window 1,
   via the selected-parent `_on` promotion consumers. Early fast opening/rise
   callers still need the provisional local FAST-only producer or another
   checked early proof. Do not fill that gap with old TPerm.

9. heldServices/settlement: keep the selected frontier/top/contest witnesses,
   source event, post-GST anchor, receiver floor, epoch and finite deadline.
   The existing Round 4 settlement handoff still applies at AttemptRows:206,
   Tests/HealingAttempt's four adapters, FrontierSearchGap:276,
   FrontierSearchTop:465 and FrontierSearchRepair:216. A callback conversion
   remains a consumer. No all-TF field was restored in this job.

10. P-As passes P-Fd's durable/epoch/mono/frame/source/FAST results at the import
    boundary. None is an aggregate H1 service producer. The public TPerm/HealT
    reconnection remains open until the final lead ruling. The canonical audit
    integrator must replace Tests/Axioms:1069's healing_tPerm command with
    healing_tPerm_at and merge P-H1.coverage-fragment.txt into its existing key.
    Import production modules only; no test-to-test import or baseline change.

Lean elaboration details: event-index binders in the design were given explicit
Nat types. The merged base already exports the emitted-proposal/fresh-HEAD
helpers and the honest-emitted-HEAD environmental join bridge that were absent
at the source design pin. Generic.Env requires nonnegative GST, so the integer
cutoff proves back <= s through healing_window_of_cut on this base. No natural
subtraction replaced an integer cutoff, and no public timing bound was changed.
