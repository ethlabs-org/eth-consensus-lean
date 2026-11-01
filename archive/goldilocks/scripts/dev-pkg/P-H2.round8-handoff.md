# P-H2 Round 8 handoff

Status: PREPARED / OPEN. Branch sleep-ph2i; base 2a0f12f8.
Source commits: db0590e8 and 86b8ec4a.
The assigned map has 114 targets: 105 GREEN and 9 OPEN, all owned by P-H2.
GREEN means that the source and its registered audits compile. It does not
close a result whose proof still takes an unproduced induction step.
No public Claims/Statements, protocol, run source, time constant or budget changes.

## Returned producers

- healing_repair_service_scopes_recovery: P5, P6 and P7 from RecoverySleep₂ and RMonoAll.
- healing_opening_service_scopes_recovery: P5, selected gate geometry and P1.
- healing_frontier_service_scopes_recovery: bounded P8, P5 and selected P6.
- healing_retained_cone_reader_floor: current receiver floor from the actual
  proposal parent and RetainedConeInput, before receipt service is requested.
- healing_frontierSearch_recovery: HG.5 under HealingSet. It constructs repair,
  common, permanence and frontier services. The remaining inputs are the named
  Foundations: RMonoAll, RXing, RCap, RQCOrigin, last-write origins, row coverage,
  row receipt, progress coverage, fold, FaultQ and honest quorum. Both independent
  finite rise and row horizon guards in FrontierSearchStatement stay unchanged.
- healing_resetTransferCore_recovery: the reset transfer core under its release
  horizon. It requests no service beyond that horizon.
- healing_postReset_coneStep: guarded cone successor from the prior cut and the
  successor reset-lease, lease and raw fields. Its receipt factories are produced.
- healing_postReset_openingDomainStep / healing_postReset_openingDomainStep₂:
  RecoverySleep₂ and RMonoAll; produced retained services and current floors.
- healing_postReset_serviceStep / healing_postReset_serviceStep₂: RecoverySleep₂,
  RMonoAll and joined last writes. Gates use proved enabled guards.

PostReset, H6, H2-prime and THigh construct their former aggregate, gate, next
and loss-service inputs from the named recovery producers. Their inv input is
still the H2 joint-induction obligation below. It is not an H1 factory request.

The exact current producer telescopes are kernel-printed in
.lake/sleep-ph2i/producer-types.log. No universal service record is an Assembly
request for the returned HG.5 producer. The per-run Foundation inputs keep their
existing producers at the P-As boundary. No Healing-to-Foundations import is added.

## H1 base repair and promotion route

The exact base RecoveryProducers source fails at 568/571. Its first constructor
arm supplies confirmedReaderAtIdx where FrontierReadScope.seed requires
FastSupportScope. Its next arm is then shifted into the first-transfer field.
The current record has seven fields: seed, first, fast, slow, prior, next,
carriers. db0590e8 fixes the body only, supplies first from its leaf factory and
keeps the theorem statement byte-identical. Evidence: h1-source-base.log and
source-audit.log. No closed H1 theorem statement changes.

RepairCover now imports RepairLeaseRecovery. The two duplicate H2 adapter
proofs are removed; callers consume the H1 repair_lease_cover_two_at and
repair_lease_cover_one_at. Their names and phase-local types stay available.

Healing.Export imports RecoveryPerm. healing_renewedPromotion already has the
Jst conclusion on this base. Promotion.lean:194 compiles in the direct source
check. The Export hperm telescope now takes RecoverySleep₂ and receives h.set.
The exact wrapper body passes its kernel and axiom probe. The complete Export
module remains OPEN because it imports the unfinished lease/raw chain.
P-As must use the returned Jst producer signature and remove its old GST adapter.

## Exact remaining H2 obligations

These are H2 proof obligations. P-As must not add them as assumed service records.
They retain the ordinary finite sleep regime and the actual selected witness.

```lean
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
variable (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
variable (hset : HealingSet p c E rho G ΔF) (hbound : LivenessBoundW p ΔF)
variable (w : HealingWitness) (hreset : H0Reset p c E rho w)

-- Guarded induction steps; definitions are in PostResetJoint.
variable (resetLease : ∀ i, PostResetResetLeaseStep p c E rho w i)
variable (lease : ∀ i, PostResetLeaseStep p c E rho w i)
variable (raw : ∀ i, PostResetRawStep p c E rho w i)

-- Produce this through postReset_joint₂_all and the three steps above.
variable (inv : ∀ i, PostResetInv p c E rho w i)

-- Full-H0 extension: only u and QStar change.
variable (extension : p.δt = 2 * p.R →
  ∀ w, H0Reset p c E rho w →
    p.actionTime w.rStar + Γ p G + 4 * p.Δ ≤ rho.horizon →
    ∃ u Q, H0 p c E rho {w with u := u, QStar := Q})

-- Local input uses the selected witness's own finite horizon.
variable (localInput : p.δt = 2 * p.R →
  ∀ w, H0 p c E rho w → tstar p w ≤ rho.horizon → HealingInput p c E rho w ΔF)

-- Full input retains the complete Jst horizon.
variable (fullInput : p.δt = 2 * p.R →
  recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
  ∀ w, H0 p c E rho w →
    HealingInput p c E rho w ΔF ∧
      tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ)
end AvailableChain.FGSA.Run
```

The Foundation inputs of the joint induction have their existing producers:
fgsa_rMonoAll, sourceDiscipline_emittedNonempty, emittedName_window,
fgsa_leaseOrigins_lastWrite, fgsa_rXing, sourceDiscipline_qcOrigin,
fgsa_rCap_channel, sourceDiscipline_tSrc, held_chain_row_origin_before,
fgsa_finalityCap and cap_finality_head. Cone and opening also use
rowPermission_covered. These are not new H1 production requests.

The source ports still needed are postReset_resetLease_succ',
postReset_leaseSafe_succ and postReset_rawTransfer_succ. The first compile blocker
is PostResetLeaseMove:77/102/134/277. It still has the old block-receipt API and
removed base.noRestart calls. The later LeaseStep/RawStep bodies still need their
P1/P2/P10 scopes and local frozen epochs. Do not recover NoRestart from sleep.

The smallest useful earlier-read adapter has this exact bounded type. H2 can
produce it from the H1 source-supporter and stored-target service proofs. It must
use the actual read t; it must not request a future vote beyond the run horizon.

```lean
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
variable (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
variable (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
variable (source : TSrc p c E rho)
variable (earlierRead : ∀ i k K s u x t,
  SourceBefore p c E rho i K s → s ≤ u → E.t_GST ≤ SA.voteTime p.toParams u →
  x ∈ rho.honest → rho.events[k]? = some (.tick x t) →
  SA.freezeTime p.toParams u < t →
  FGBlock.Preceq (storeAt p c E rho k x).fg.F K →
  TargetReceiptService E rho (eraseFG K) (SA.freezeTime p.toParams u) x)
end AvailableChain.FGSA.Run
```

healing_h0_of and the healed consumers compile, but they still consume TCarrier,
H2A, H3, H5 and inv. HealingInputExport's field callbacks now have the full Jst
horizon. This is a corrected composition telescope, not full input production.
The local input request remains distinct. No full reset budget is added to it.

## Remaining assigned targets

- AvailableChainFGSAProofs.Proofs.Healing.Export
- AvailableChainFGSAProofs.Proofs.Healing.PostResetLeaseMove
- AvailableChainFGSAProofs.Proofs.Healing.PostResetLeaseStep
- AvailableChainFGSAProofs.Proofs.Healing.PostResetRawStep
- AvailableChainFGSAProofs.Proofs.Healing.ReleaseScope
- AvailableChainFGSAProofs.Tests.HealingPostResetLeaseStep
- AvailableChainFGSAProofs.Tests.HealingPostResetRawStep
- AvailableChainFGSAProofs.Tests.HealingReset
- AvailableChainFGSAProofs.Tests.HealingRiseOne

HealingRiseOne is a separate old-signature caller port. Its saved-window guards
stay at GST; phase starts must use Jst and its factories must use the returned
named producers. The full assigned build records every current source failure.
The positive P-As/H1 run fixtures are unchanged. Conditional signature tests and
strict audits do not close the unproduced all-cut steps or higher result requests.

## Validation

All cited logs are in .lake/sleep-ph2i/.

- dck-final.log: PASS; 575 GREEN roots, 50 strict groups, 3,650 permitted
  axiom results and 24 passing controls; map 105/114 GREEN.
- exports-final.log: all 575 GREEN roots; 469 proof modules, 253 exports,
  zero unaccepted, with the existing baseline. The nine OPEN roots are excluded.
- layers-final.log: 72 inherited findings, zero new.
- headers-final.log: PASS. sleep-scopes-final.log: PASS.
- source-audit.log: no admission, public source change or overlong changed Lean file.
- promotion-source.log and promotion-export-probe.log: source and exact wrapper body.
- producer-types.log: complete current producer types.
- assigned-final-build.log: complete 114-target probe before the final saved-gate
  proof refactor; the later DCK validates every current GREEN root.
- manifest-final.log: FG-SA shallow/deep pass. The required full script fails at
  the known AvailableChain.KitFG.pins legacy snapshot mismatch. No snapshot,
  allowance, source label or checker changes. Owner: lead/P-Da.

Full P-H2 closure, full Healing.Export, full Root and full manifest PASS are not claimed.
