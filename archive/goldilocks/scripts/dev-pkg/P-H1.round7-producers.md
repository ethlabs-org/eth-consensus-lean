# P-H1 Round 7 producer obligations

Round 8 update: see P-H1.round8-producers.md. H6-FLOOR is now proved;
conditional aggregate assemblies do not close the remaining object services.

Status: PREPARED. These are production goals, not proved theorem declarations.
All aggregate goals stay OPEN/P-H1. No conversion or restriction closes a row.
The source contract is healing-contract-34d9aa77.md, sections A-F. This file
supersedes the Round 6 producer notes. Claims starts follow JOINED-START;
budgets and guarded record fields stay.

The common context for the types below is:

```lean
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
variable (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
variable [Fintype V] {G ΔF : Time}
```

The namespaces are AvailableChain.FGSA.Run and AvailableChain.SimplexFG.
Each `theorem` below states an OPEN goal; it is not a source declaration.
Each actor, event index, source label, signed object, phase and read is actual.
The window is a local factory domain. At a ready source it follows from
healing_ready_vote_cutoff. An arbitrary post-GST vote is still insufficient.
All deadlines are bounded by actual ticks or v.
The source/receiver floors and selected witness geometry remain in each record.

```text
┌─────────┬─────────────────────────┬───────────────────────────────────┬────────┐
│ ID      │ Record site             │ Exact output                      │ Owner  │
├─────────┼─────────────────────────┼───────────────────────────────────┼────────┤
│ H1g-P1  │ SupportTransfer:22      │ FirstTransferScope                │ P-H1   │
│ H1g-P2  │ SupportHeads:22         │ NextTransferScope                 │ P-H1   │
│ H1g-P3  │ SupportLease:44         │ FastSupportScope                  │ P-H1   │
│ H1g-P4  │ SupportSlow:18          │ SlowSupportScope                  │ P-H1   │
│ H1g-P5  │ SupportPerm:16          │ SupportPermanenceServices         │ P-H1   │
│ H1g-P6  │ RepairH6:20             │ RepairHeadServices                │ P-H1   │
│ H1g-P7  │ RepairGate:17           │ RepairGateScope                   │ P-H1   │
│ H1g-P8  │ FrontierRead:21         │ FrontierReadScope                 │ P-H1   │
│ H1g-P9  │ DescentLossCause:43     │ LossServiceScope                  │ P-H1   │
│ H1g-P10 │ PostResetRaw:22         │ RawServiceScope                   │ P-H1   │
└─────────┴─────────────────────────┴───────────────────────────────────┴────────┘
```

All sites are under AvailableChainFGSAProofs/Proofs/Healing. These locations
are the record definitions; the full factory types follow.

```lean
-- P1: the local route also serves Raw.first without a full batch cutoff.
theorem firstTransferScope_of_recovery
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (s : Slot) (ix iy : Nat) (x y : V)
    (hSync : E.t_GST ≤ SA.voteTime p.toParams s)
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hix : IsGateTick p c rho ix x s)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hxGate : enabledGateAt p c E rho ix x s)
    (hyJoin : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1))) :
    FirstTransferScope E rho ix iy x y s

-- P2
theorem nextTransferScope_of_recovery
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (s : Slot) (iy : Nat) (y : V)
    (hCut : HealingWindow p E 1 s) (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hyJoin : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1))) :
    NextTransferScope E rho iy y s

-- P3: services can be constructed before the body chooses its fast witness.
theorem fastSupportScope_of_recovery
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (s : Slot) (v : Time) (x : V)
    (hCut : HealingWindow p E 1 s) (hx : x ∈ rho.honest)
    (hGate : SA.gateTime p.toParams s ≤ v) (hHor : v ≤ rho.horizon) :
    FastSupportScope E rho s v x

-- P4
theorem slowSupportScope_of_recovery
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (s : Slot) (v : Time) (x : V)
    (hCut : HealingWindow p E 1 s)
    (hWindow : E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k))
    (hx : x ∈ rho.honest)
    (hGate : SA.gateTime p.toParams s ≤ v) (hHor : v ≤ rho.horizon) :
    SlowSupportScope E rho s v x

-- P5
theorem supportPermanenceServices_of_recovery
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (u v : Time) (m : Nat) (J : Option (FGBlock (Fin p.n))) (contested : Bool)
    (hReady : recoveryStart p E ≤ u)
    (hPhase : PhaseInterval p c E rho u v m J contested) :
    SupportPermanenceServices E rho u v m J contested

-- P6
theorem repairHeadServices_of_recovery
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (s : Slot) (ip : Nat) (x : V) (N : NamedProposal p.n)
    (hCut : HealingWindow p E 2 s) (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hEmit : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hHor : SA.voteTime p.toParams s ≤ rho.horizon) :
    RepairHeadServices E rho s ip x N

-- P7
theorem repairGateScope_of_recovery
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (s : Slot) (hCut : HealingWindow p E 1 s)
    (hHor : SA.gateTime p.toParams s ≤ rho.horizon) :
    RepairGateScope E rho s

-- P8: seed qualification is used by the caller to produce hCut.
theorem frontierReadScope_of_recovery
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (q : Slot) (v : Time) (hCut : HealingWindow p E 1 q)
    (hGate : SA.gateTime p.toParams q ≤ v) (hHor : v ≤ rho.horizon) :
    FrontierReadScope E rho q v

-- P9: the exact source-origin suppliers used by the existing high-source proof.
theorem lossServiceScope_of_recovery
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a →
      ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
        {e : Height × BlockId},
      HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C)) :
    LossServiceScope p c E rho

-- P10
theorem rawServiceScope_of_recovery
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) :
    RawServiceScope p c E rho
```

H1g-CARRIER, OPEN/P-H1, SupportFrame:208:
`HealingCarriersAt E rho s iy y t`, from hrec and RMonoAll. Its own guards
fix GST <= vote(s), the actual HealingJoinedTick, early(s) <= t and t <= horizon.
Its source guard is the actual honest joined HEAD tick. HeadCarrierDemand selects
K/W and keeps source ancestry, the source height floor and receiver compatibility.
The direct arm serves only the exact stored HEAD K under the receiver floor.
P-ShA's accepted/emitted named-object services are the shared route. An arbitrary
TF member is not a trigger. All retained raw HEAD histories remain P-H1 work.

H1g-PROP, OPEN/P-H1, SupportProposal:18. Exact goal:

```lean
(hrec : RecoverySleep₂ p c E rho G ΔF)
(mono : RMonoAll p c E rho)
(r : Slot) (ip : Nat) (x : V) (t : Time)
(hCut : HealingWindow p E 1 r)
(hRead : HealingJoinedTick E rho ip x t)
(hTime : t = SA.proposalTime p.toParams (r + 1) ∨ t = SA.gateTime p.toParams r)
⊢ ProposalSupportScope E rho ip x r t
```

The batch/rival fields have proved count suppliers. The fresh HEAD and carrier
object services remain open. The read time t is the actual tick, including a gate
read. The proposer and late rival fields only count seats; neither asserts that a
synthetic proposer operation ran at a gate tick.

H1g-GATE, OPEN/P-H1, SupportGate:17. Exact goal:

```lean
(hrec : RecoverySleep₂ p c E rho G ΔF)
(mono : RMonoAll p c E rho)
(s : Slot) (i : Nat) (x : V) (B : Block)
(hCut : HealingWindow p E 1 s)
(hx : x ∈ rho.honest) (hi : IsGateTick p c rho i x s)
(hGate : enabledGateAt p c E rho i x s)
(hHor : SA.gateTime p.toParams s ≤ rho.horizon)
(hGeom : GateReceiptGeometry E rho
  (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s B)
⊢ SupportGateScope E rho i x s
```

The remaining primitive is the fresh HEAD/target pair in
healing_recovery_gate_scope. The geometry supplies the target floor. The existing
healing_support_gate_scope_of_cut then supplies the current-batch count.

H1g-H6-FLOOR, OPEN/P-H1, RepairH6.repair_head_exact_legacy:
for its exact r+1 signed proposal N and phase, with RepairLeaseCover at r+1,
ProposalSupportScope at ip/x/r/proposal(r+1), Window 1 at r, and the existing
RetainedH6Input geometry, produce:

```lean
∀ y ∈ rho.honest, ∀ (ih : Nat),
  rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (r + 1))) →
  joinedAt p E rho y (r + 1) (SA.voteTime p.toParams (r + 1)) →
  Block.Preceq (eraseFG (rho.stateBeforeTime E
    (SA.voteTime p.toParams (r + 1)) y).st.fg.F) N.erase
```

Shared/RetainedConsumers computes the event-store floor from the same H6 geometry
before its receipt call. A P-ShA export or a local proof must also pull that floor
back to stateBeforeTime with RMonoAll. This is an exact selected-proposal geometry
obligation, not a proposal receipt assumption. RepairHeadServices.target is a
proved conversion from the retained proposal service after this floor is supplied.
It is not a record producer.

H1h-H6-COVER-ONE and H1h-H6-COVER-TWO, PROVED from ready TPerm:
repair_lease_cover_one/two construct RepairLeaseCover at the actual phase,
with threshold b+k < s or beta+2k-1 < s, vote(s) <= v, RecoverySleep₂,
RMonoAll, RXing, the exact last-write telescope and the same TPerm.
The last-write producers keep the old-expiry/new-Transfers split.
No hCover input remains. The production P5 factory still needs proof.

H1h-TPERM-LINK, PROVED adapter / OPEN P5 producer:
healing_tPerm_at derives Window 1 from hready <= u <= vote(s) and returns
Transfers after the actual phase record and source body. healing_tPerm
introduces the approved TPerm arguments and calls that same phase API.
Its explicit input is the uniform P5 factory over ready phases, not an old
GST-wide TPerm. The public start change is committed. H2/P-As must port
its aggregate and assembly callers as listed in round7-handoff.md.

Proved suppliers, separate from the OPEN aggregate goals:

- SupportRecovery: healing_recovery_restart_bound, healing_recovery_joined,
  healing_recovery_joined_window/next/vote_next/proposal_next and
  healing_recovery_next_vote_joined_of_cut. Every tick bounds its finite horizon.
- SupportTicks: healingJoinedSeats_card uses the HEAD-seat CStar bijection at the
  same vote. healing_recovery_seat_counts and healing_recovery_seat_rivals prove
  the release, Batch and selected-seat complement bounds in Window 1.
- DescentLoss: healing_high_source_recoveryStart uses oldRowHeights and mu;
  healing_high_source_window then proves Window 1. It proves no Window k or
  StrongHealingWindow. HighSrcN and oldRowHeights were not changed.
- SupportFrame: healing_joined_tick_of_guard proves the environmental join from
  the executed guard. healing_carriers_window_at/cut_at only apply an assumed
  guarded service; neither constructs object receipt.
- SupportTransfer: healing_support_honest_head_joined obtains the source join
  from actual honest emission. FirstTransferScope.carriersOn fixes the receiver.
- SupportGate: healing_recovery_gate_enabled, healing_gate_enabled_of_joined and
  healing_gate_enabled_of_result prove actual enabledness. The scheduled tick
  alone is not an enabled gate.
- SupportLease: healing_recovery_same_label is a complete SameLabel supplier
  from RecoverySleep₂ and GST <= vote(s). It splits on the finite gate horizon;
  the short-prefix arm has no enabled gate demand. This supplies P3.sameLabel,
  P4.window, P9.same and P10.same at their respective actual sync domains.
- Shared/CatchUp: fgsa_head_joined_of_joinedAt,
  fgsa_joinedAt_of_emitted_head and fgsa_target_service_of_proposal.
- Healing/RecoveryService: healing_emitted_proposal_service and
  healing_fresh_head_service exist on this merged base. Their handler/exclusion
  inputs must be proved at the actual anchor; they do not close any aggregate.
- P-Fd: fgsa_rStoreDurable, fgsa_rStoreEpoch, fgsa_rMonoAll,
  fgsa_rFrameNextEpoch and Foundations/Leases:642's FAST supplier. P-As passes
  these across the import boundary. P-H1 has no new Foundations import.
- Healing/RecoveryScope.healing_recovery_gate_reader supplies P8.readers from the
  qualified seed's gate cutoff and finite gate horizon. It is a reader supplier,
  not a complete FrontierReadScope producer.

The finite-run domains above allow normal sleep/restart runs. They require neither
whole-run NoRestart nor a new public participation premise. No global all-honest
joined-batch claim remains at a merely post-GST source vote. Field producers remain
OPEN where the selected object histories have not been proved; no CLOSED claim is
made from compilation, monotonicity, signature tests or a callback conversion.

## Round 7 changes to the remaining obligations

P5 has the ready phase domain shown above. Its uniform factory is the last
explicit input of healing_tPerm. P1-P10 and ProposalSupport producers remain
OPEN/P-H1. Their exact fields and result goals are stated above; the caller
keeps selected witnesses, receiver floors, actual reads, synchrony and epochs.
No aggregate constructor is claimed from a restriction or conversion lemma.

The two lease covers are now produced by repair_lease_cover_of_split and
healing_last_write_one_lease/two_lease, with the same ready TPerm. Their old
hCover obligations are discharged; their P5 permanence input remains open.
Readiness, actual HEAD/gate guards, seat counts, reset source readiness and
high-source readiness are proved. The CStar bridge uses HEAD seats, not an
unproved substitution of node counts.

Named Foundation producers supplied by P-As are fgsa_rMonoAll, fgsa_rXing,
fgsa_leaseOrigins_lastWrite, sourceDiscipline_tSrc,
sourceDiscipline_emittedNonempty and sourceDiscipline_emittedName. The exact
existing source-origin telescope is preserved at every permanence caller.
The H6 receiver-floor proof remains OPEN/P-H1 at repair_head_exact_legacy and
the one/two-lease repaired HEAD adapters; it is not inferred from emission.

SourceTiming/Delivery/reset delivery retain an exact OPEN/P-H1 receiver
service goal: for the supporter-selected W, actual honest vote tick j/z,
K <= W (or CStar <= eraseFG W), and F_receiver(early s) <= W, construct
TargetReceiptService E rho (eraseFG W) (early s) x. The bounded source and
receiver reads carry the original history, synchrony and epoch. This goal
has no arbitrary all-TF receiver demand. The selected factory is an input;
the floor-pullback proof is complete.

The positive HealingRun constructs RecoverySleep₂ and a nonempty actual
PhaseBody at ready source label 2. It does not construct P5 or TPerm.
The finite run's horizon is 304; the full top-level H-time horizon for those
parameters is 309. End-to-end healing fixture closure is OPEN/P-H1/P-As.
