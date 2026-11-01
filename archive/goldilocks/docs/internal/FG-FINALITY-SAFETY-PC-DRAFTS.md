# PC safety feasibility: S1P

Date: 2026-10-06. All contracts are PROVISIONAL.
Scope ends at S1P. S2 has not started.

The new reads use pcsaWith m p c for every FGMode. The old pcsaCoreReads
producer keeps its type. Its mode-general form is definitionally equal in
`.on`. State, Object, store processing, and durable data do not depend on m.
The FG seat equivalence is Equiv.refl. No cast or new premise is required.
The `.idle` enabled read is false. The `.on` read uses the actual FG duty time.
Both input reads are the actual protocol fgInputs.

The PC wire record proves all five fields. It keeps exact signed wires.
The record equations prove initial, clock, process, restore, and recordOwn.
The local tick_rows field is not proved here. It remains for S6.
process_F, erase_prefix, and output_eq are proved. The complete order
record holds for both .on and .idle. Its producer is pcsaSafetyOrderLaws.
The initial_tf and restart_tf facts need no Reachable assumption.
The store producer signatures use Good nd = Reachable p nd.st.
FG-SA uses its existing height and finality views. PC-SA uses the same height
view and pcsa_finalityView. The local finality-view equality and shared certificate producer are proved.
They use FG-SA model facts. They use no FG-SA run safety theorem.

Required owner equations were checked before the local calculations.
The existing Protocol supplies actWith_def, act_def, pcsa_def, pcsaAC_def,
and toWireEquiv. New raw proposal and decoder reads have home equations.
The new Proofs modules use rfl, change, and the existing home equations.
The two PC adapter records also have proved home equations. Their bodies
remain opaque outside their owner.
They do not unfold or simplify a foreign definition or matcher.
The duty fold, attest, and full tick_rows calculations are still open.
Before that calculation, add any missing home duties, actS, attest, and
recordRow? equations. Do not copy the old ClientTrace tactic proof.

## Invariant argument to prove in S5a

Induct on Reachable p st. Carry FGStoreInvariant and ViewRootInj st.fg.TF
as local induction data. ViewRootInj is not a new run premise.
The genesis store gives both facts. A clock keeps FG; recordOwn keeps the
whole core; restore uses the genesis store. These steps cover both modes.
An ack, a PC, a HEAD, or a row preserves the FG projection. Use the named
handler equations and the existing collection and pooling frame facts.

For a proposal, keep namedParentHeld, parentFG, and blockAccepted tests
against the original state. A refusal is the identity step.
At acceptance, parentFG selects P in the old TF and erases it to N's
geometric parent. blockAccepted excludes every old stored block with the
new root. It also checks the parent slot and the F-prefix condition.
The old ViewRootInj gives equality for two old roots. Root freshness rules
out equality between the new block root and an old root. The same new
block is equal to itself. Parent closure supplies every ancestor needed
by ViewRootInj on insert B TF. Thus the local StoreStepRoots premise is
proved from admission. Do not use NamedRootCollisionFree at this step.
Apply FGSA.Window.windowStoreInvariant_on_block with p.kWLarge.
Use the PC finality projection equality to convert its finality view.

The order is fixed by pcsa_admitBlock_fg_cases in
AvailableChainPCSAProofs/Proofs/Shared/FGStore.lean. It moved unchanged
from AcFrame/Store.lean:69–85. AcFrame.Store publicly imports the helper.
The handler first admits to base, then may delete conflicting leases from
a carried PC. It then updates FG, reconciles, collects PCs, and admits rows.
The carried pcValid test reads the old F. The base admission can change
base.blocks; it does not change FG. The deletion changes only
base.obligations. pcsa_safety_delete_core proves that it keeps FG,
proposals, and rowPool. Reconciliation writes no FG. Collection and row
admission also keep FG. No lease/finality commutation theorem is needed.

Open local proof work: parentFG membership and erasure specification;
accepted block root, parent, slot, and packed-body equations; local
ViewRootInj preservation; all non-FG metadata projection preservation;
and the induction that assembles the full invariant field.
The existing AcStoreSafe proof assumes fault-only chain rows. It cannot
supply the general invariant. Do not use that assumption here.
Add an accepted-proposal test that both removes a conflicting lease and
advances F when this full admission proof is implemented.

## process_new argument to prove in S5a

Start with Good nd and membership of B in the new TF, with B absent from
the old TF. For all identity-FG cases, these hypotheses contradict each
other. In the accepted proposal case, the shared window keeps TF equal
to either the old TF or insert C TF. The only possible new element is
C = fgBlock P N.erase N.rows. The new element is not genesis.
Use accepted namedContentOk to get the exact packed body and signed list.
Together with erase P = N.erase.parent, reconstruct erase C = N.erase.
The fgBlock row equation is exactly N.rows.filterMap RowWire.toRow?.
The raw proposal read returns N.erase and the raw signed list N.rows,
even for a rejected delivery. Acceptance is established separately.
No decoded set chosen apart from the delivered wire can replace N.rows.

Pre-update deletion, reconciliation, PC collection, and row admission must
preserve the projections used in this reconstruction. Keep their local
projection proofs. Do not call a future generic stored-delivery wrapper
to prove this producer. No proof of process_new is claimed in S1P.

## Named scope and emitted parents to prove in S5b

Use PCSA.Run.RootBlockInRun as the projected Q. Its named seeds are raw
proposal deliveries and named bodies held at an honest event prefix.
Keep the full NamedProposal, including the carried PC, signed HEAD lists,
rows, and recursive named parent. EraseFG equality alone is insufficient.
Existing PC/RunEvidence has delivered body scope and scoped root equality.
Its store evidence tracks base blocks and HEADs. It does not give the new
exact FG insertion metadata or the complete emitted-parent producer.

Named obligations:

- Honest genesis is a named seed, including the initial prefix.
- Every raw delivered proposal is a seed, even when refused.
- Named ancestry preserves projected geometric ancestry.
- A stored FG block has an exact named body with its original signed rows.
- NamedRootCollisionFree gives safetyScopedRoots on the projected scope.
  This is the lead-accepted Opus 10 projection. No F-3 line is added.

Emitted-parent obligations:

- Decode an emitted proposal as the actual namedProposal/withApp output.
- Show propose selects an exact named parent held at the post-clock store.
- Show the FG parent and named erasure agree.
- Transport that exact parent to a reachable event prefix or a delivery
  seed. Own row recording preserves its store and named metadata.
- Close the parent and its ancestors in Q, with a separate genesis case.
- For K below the emitted geometric tip, transport K.parent as an ancestor
  of the stored named parent. Do not place the emitted-only tip itself in Q.

These arguments must work for `.on` and `.idle`. A claim wrapper gains no
new premise. Leave the FG-SA claim path in place until S5a and S5b close.
The full core metadata growth and client tick_rows producers are also
open. No LAW is frozen by the early codec or order producer alone.

## S1P order completion — 2026-10-07

The lead chose lower-helper extraction. Five FG frame helpers moved to
Shared.FGStore with unchanged declaration bytes. AcFrame.Store keeps
its lane-specific proofs and publicly imports the new module.
No layer exception or checker code change was needed.

Shared.FGStore now proves pcsa_process_F_mono for every store and wire.
The proof splits the decoded wire cases through a change bridge.
The row singleton fold, collection frame, raw ACK fold, and a local
checked-pooling calculation prove the non-block cases.
The moved pcsa_admitBlock_fg_cases gives the proposal cases.
The window-model window_on_block_F_mono proves the accepted case.
The lease-deletion-before-FG-update order remains unchanged.

Foundations.FGSafetyStore lifts process_F for every FGMode. Its full
pcsaSafetyOrderLaws producer also supplies erase_prefix and output_eq.
Tests/FGSafety checks complete .on and .idle instances and their axioms.
The proof adds no Reachable, root-injectivity, or schedule premise.
The invariant and process_new arguments above remain prose drafts for S5a.
The named/emitted-parent obligations remain for S5b. Stop before S2 here.
