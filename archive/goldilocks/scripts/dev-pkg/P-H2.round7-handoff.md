# P-H2 Round 7 handoff

Status: PREPARED / OPEN. Base b1469598; branch sleep-ph2h.
The core producer commit is d8157225. Consumer ports: 035d2672.
No public claim, statement, time constant, attempt sum or GST saved-window bound changed.

The selected receipt producers are complete:

- healing_selected_carriers_recovery consumes ReceiptProducers at the actual source tick.
- healing_head_witness_receipts_recovery selects K and W together and serves W only under
  the current receiver floor. It preserves original proposal history and the local epoch.
- healing_self_proposal_service supplies the promotion/search callback.
- healing_phase_witness_receipts_recovery supplies the attempt/search receipt callback.
- healing_rPhase_recovery produces all five clauses from RecoverySleep₂, RMonoAll and RXing.
  It uses durable phase order, strict sleep-safe spread and the receiver freeze epoch.
- repair_lease_cover_two_at and repair_lease_cover_one_at discharge the Round 6 local
  cover requests from the selected phase's SupportPermanenceServices.
- frontier_retained_reader_floor selects the actual proposer parent and proves its floor
  at the strict current receiver read under the capped frontier.

The producer evidence is the 23-command HealingH2PortsAxioms audit. Final DCK passes
with 43 strict sources, 3,400 results and all 24 controls. The map has 114 targets:
61 GREEN / 53 OPEN; 531 total GREEN roots. All open assigned targets retain P-H2.

H1 aggregate import blocker

RecoveryProducers does not compile on this base. Its P8 constructor at 528 supplies
confirmedReaderAtIdx where FrontierReadScope.seed requires FastSupportScope. The next
arm at 531 consequently receives a label bound where it expects an honest node.
The current seven fields are seed, first, fast, slow, prior, next and carriers.
Evidence: .lake/sleep-ph2h/core-probe3.log. No H1 source was changed.
P-H1 must repair that constructor and validate its producer module on these H2 types.
The named P6 producer healing_repair_head_services_recovery is in that same module.
H2 uses its indexed .target/.scopes interface with proved reader floors, but cannot
import the failed aggregate. Its heads factory remains an explicit P6 input.
P5 permanence and P1/P2 HEAD relay remain H1 production obligations. A conditional
assembly or a universal wrapper does not discharge them.

Remaining H2 source closure

- OpeningServiceScopes and RepairServiceScopes still need their complete bounded
  constructors from the named H1 primitive factories. Their exact types follow below.
  OpeningServiceScopes has no carrier field; the selected carrier is produced locally.
- FrontierServiceScopes.read needs P8 from the corrected H1 aggregate. Permanence
  needs P5. Heads need P6. Every capped read and carrier deadline stays within v.
- All-cut opening, retained cone, raw-transfer, reset lease and joint suppliers stay
  OPEN/P-H2. PostResetOpening still calls legacy global-epoch geometry. Replace that
  route with selected retained services and prove the actual receiver floor first.
  The all-cut inv argument is an H2 induction obligation, not an H1 factory.
- PostResetH2Prime's nextScopes is the actual joined next reader factory, with a
  HealingWindow. P-H1 P2 supplies its primitive; H2 owns the post-reset assembly.
- PostResetGate's gates argument is P-H1's geometry-guarded enabled gate receipt
  primitive. H2 proves its source cut, floor, count and guard. The raw guard now
  takes its actual GST bound and enabled tick. It does not cover a suppressed gate.
- PostResetTHigh's LossServiceScope is P-H1's high-source primitive. H2 owns the
  high-source all-cut assembly. Equal-label service has a proved wake-aware producer.

The changed ports have no global NoRestart input. The untouched legacy all-cut
consumers remain open and are not claimed as ordinary finite-sleep producers.
No run fixture proves the still-open primitive factories.

Exact remaining aggregate types

```lean
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

structure OpeningServiceScopes (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) :
    Prop where
  permanence : ∀ u v m J contested, recoveryStart p E ≤ u →
    PhaseInterval p c E rho u v m J contested →
    SupportPermanenceServices E rho u v m J contested
  gates : ∀ i x s, x ∈ rho.honest → IsGateTick p c rho i x s → enabledGateAt p c E rho i x s →
    E.t_GST ≤ slotStartZ p ((s : Int) - 1) →
    SA.gateTime p.toParams s ≤ rho.horizon → GateReceiptScope E rho i x s
  transfers : ∀ u v m J contested, recoveryStart p E ≤ u →
    PhaseInterval p c E rho u v m J contested → ∀ ix iy x s B,
    u ≤ SA.voteTime p.toParams s → SA.gateTime p.toParams s ≤ v →
    E.t_GST ≤ SA.voteTime p.toParams s →
    Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams s) (SA.gateTime p.toParams s) →
    B ∈ (fastWriteAt (clock p (storeAt p c E rho ix x)
      (SA.gateTime p.toParams s)) s).getD [] →
    x ∈ rho.honest → enabledGateAt p c E rho ix x s →
    rho.events[iy]? = some (.tick x (SA.voteTime p.toParams (s + 1))) →
    joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1)) →
    FirstTransferScope E rho ix iy x x s


structure RepairServiceScopes (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : Prop where
  permanence : ∀ u v m J contested, recoveryStart p E ≤ u →
    PhaseInterval p c E rho u v m J contested →
    SupportPermanenceServices E rho u v m J contested
  heads : ∀ (s : Slot) ip x N, E.t_GST ≤ slotStartZ p ((s : Int) - 2) → x ∈ rho.honest →
    rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
    (ofWire p ⟨.proposer s, .proposal N⟩) ∈ rho.emitsAt E ip →
    SA.voteTime p.toParams s ≤ rho.horizon → RepairHeadServices E rho s ip x N
  gates : ∀ (s : Slot), E.t_GST ≤ slotStartZ p ((s : Int) - 1) →
    SA.gateTime p.toParams s ≤ rho.horizon → RepairGateScope E rho s


structure FrontierServiceScopes (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (q : Slot) (v : Time) : Prop where
  read : recoveryStart p E ≤ SA.proposalTime p.toParams q →
    SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon → FrontierReadScope E rho q v
  permanence : ∀ u t m J contested, recoveryStart p E ≤ u →
    PhaseInterval p c E rho u t m J contested → t ≤ v →
    SupportPermanenceServices E rho u t m J contested
  heads : ∀ s ip x N, q + 1 ≤ s → SA.voteTime p.toParams s ≤ v →
    E.t_GST ≤ slotStartZ p ((s : Int) - 2) →
    x ∈ rho.honest → rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
    (ofWire p ⟨.proposer s, .proposal N⟩) ∈ rho.emitsAt E ip →
    RepairHeadServices E rho s ip x N


structure RepairGateScope (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (s : Slot) : Prop where
  cut : E.t_GST ≤ slotStartZ p ((s : Int) - 1)
  gates : ∀ i x, x ∈ rho.honest → IsGateTick p c rho i x s →
    enabledGateAt p c E rho i x s →
    ∀ B, GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s B →
    GateReceiptScope E rho i x s
  first : ∀ i iq x, x ∈ rho.honest → IsGateTick p c rho i x s →
    rho.events[iq]? = some (.tick x (SA.voteTime p.toParams (s + 1))) →
    enabledGateAt p c E rho i x s →
    joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1)) →
    FirstTransferScope E rho i iq x x s
  carriers : ∀ iy y t, SA.voteTime p.toParams s + p.Δ ≤ t →
    t ≤ rho.horizon → HealingCarriersAt E rho s iy y t


end AvailableChain.FGSA.Run
```

Exact post-reset next and gate primitives

```lean
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
variable (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- P-H1 P2 primitive; H2 proves the window and selects the actual reader.
variable (nextScopes : ∀ v iy x, HealingWindow p E 1 v → x ∈ rho.honest →
  rho.events[iy]? = some (.tick x (SA.voteTime p.toParams (v + 1))) →
  joinedAt p E rho x (v + 1) (SA.voteTime p.toParams (v + 1)) →
  NextTransferScope E rho iy x v)

-- P-H1 gate receipt primitive; H2 supplies the actual enabled gate geometry.
variable (gates : ∀ s j x, E.t_GST ≤ SA.voteTime p.toParams s → x ∈ rho.honest →
  IsGateTick p c rho j x s → enabledGateAt p c E rho j x s →
  ∀ B, GateReceiptGeometry E rho
    (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)) s B →
  GateReceiptScope E rho j x s)

end AvailableChain.FGSA.Run
```

Foundation inputs retain their named producers: fgsa_rMonoAll, fgsa_rXing,
fgsa_rCap_channel, sourceDiscipline_tSrc, sourceDiscipline_qcOrigin,
fgsa_leaseOrigins_lastWrite, sourceDiscipline_emittedNonempty,
sourceDiscipline_emittedName, and rowPermission_covered. These remain P-As
assembly inputs; H2 does not cross the Foundations import boundary.

Validation logs are under .lake/sleep-ph2h/. Use dck-final.log, exports-final.log,
ports-final-build.log, receipt-final-probe.log, layers-final.log and headers-final.log.
Manifest: shallow/deep FG-SA, legacy, V2, generic and compose snapshots pass.
The Claims snapshot stops at missing Healing.PostResetOpening.olean. Its source
still fails at the legacy global-epoch geometry calls; see service-probe.log.
P-Ou proof and legacy test probes both pass with --wfail. No separate P-Ou
legacy failure was reproduced on this base. Evidence: pou-legacy-all.log and
pou-legacy-tests.log. Full manifest PASS is not claimed.

Exact high-source primitive and all-cut induction obligation

```lean
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

structure LossServiceScope (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) : Prop where
  same : ∀ i K K' s, SourceBefore p c E rho i K s →
    SourceBefore p c E rho i K' s →
    muOf p c E rho + 1 ≤ (heightView p K).h →
    muOf p c E rho + 1 ≤ (heightView p K').h →
    SameLabelServiceScope E rho s
  first : ∀ B sB (iy : Nat) (y : V), HighSrcN p c E rho B sB → y ∈ rho.honest →
    rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (sB + 1))) →
    joinedAt p E rho y (sB + 1) (SA.voteTime p.toParams (sB + 1)) →
    ∀ ix xs, xs ∈ rho.honest → IsGateTick p c rho ix xs sB →
    (∃ C, gateResultAt p c E rho ix = some (some C) ∧
      Block.Preceq (eraseFG B) C) →
    FirstTransferScope E rho ix iy xs y sB
  next : ∀ B sB i (iy : Nat) (y : V), HighSrcN p c E rho B sB → sB + 1 ≤ i →
    y ∈ rho.honest →
    rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))) →
    joinedAt p E rho y (i + 1) (SA.voteTime p.toParams (i + 1)) →
    NextTransferScope E rho iy y i
  fast : ∀ B sB l (k : Nat) (x : V), HighSrcN p c E rho B sB → sB + 2 ≤ l →
    x ∈ rho.honest →
    rho.events[k]? = some (.tick x (SA.voteTime p.toParams l)) →
    ∀ y nd, y ∈ rho.honest →
    postClock E rho y (SA.gateTime p.toParams sB) = some nd →
    eraseFG B ∈ (fastWriteAt nd.st sB).getD [] →
    FastSupportScope E rho sB (SA.voteTime p.toParams l) y
  receipts : ∀ i K s u (k : Nat) (x : V), SourceBefore p c E rho i K s → s ≤ u →
    E.t_GST ≤ SA.voteTime p.toParams u → x ∈ rho.honest →
    rho.events[k]? = some (.tick x (SA.voteTime p.toParams (u + 1))) →
    joinedAt p E rho x (u + 1) (SA.voteTime p.toParams (u + 1)) →
    FGBlock.Preceq (storeAt p c E rho k x).fg.F K →
    TargetReceiptService E rho (eraseFG K) (SA.freezeTime p.toParams u) x

private theorem loss_freeze_epoch [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {x : V} (hx : x ∈ rho.honest) {u : Slot}
    (hgst : E.t_GST ≤ SA.voteTime p.toParams u) (k : Nat) :
    V2.D.restartFree rho x (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams u)) k := by
  have hTime : E.t_GST + 1 ≤ SA.freezeTime p.toParams u := by
    have hp : (0 : Int) < p.Δ := p.deltaPos
    have hd : (1 : Int) ≤ p.Δ := by omega
    change E.t_GST ≤ 4 * p.Δ * (u : Int) + p.Δ at hgst
    change E.t_GST + 1 ≤ 4 * p.Δ * (u : Int) + 3 * p.Δ
    linarith
  exact healing_recovery_epoch E rho hrec hx (fgsa_idxBefore_mono rho hTime)


variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
variable (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (w : HealingWitness)

-- OPEN/P-H2: joint induction from H0Reset and the exact bounded source services.
variable (inv : ∀ i, PostResetInv p c E rho w i)

end AvailableChain.FGSA.Run
```

The open primitives must be produced for their stated guarded domains in finite
sleep runs. Their ordinary-run validity is not established by DCK, a record
conversion, or the four numeric source replays. Keep their ownership and source
factory obligations explicit until the producers are validated.
