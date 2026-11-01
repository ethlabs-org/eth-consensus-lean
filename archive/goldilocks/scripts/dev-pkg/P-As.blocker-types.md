# P-As Round 8 — exact remaining types

Base: 15ed93b9; branch sleep-pas8. Status: PREPARED / OPEN-P-H2.
All public Claims/Statements definitions and protocol sources are unchanged.
No Proofs/Healing source is edited. Evidence: .lake/sleep-pas-r8/.

## Returned requests consumed

HG.5 is produced by healing_frontierSearch_recovery. Assembly supplies RMonoAll,
RXing, RCap, RQCOrigin, joined last writes, row coverage, row receipt, progress
coverage/fold, FaultQ and honest quorum from the existing named producers.
The producer constructs the repair, opening and frontier scopes. The final reset
and H-time theorems have no search-factory input. Both HG.5 horizon guards stay.

healing_renewedPromotion receives hstart at Jst directly. RecoveryPerm is imported
through Healing.Export. No Assembly GST conversion or direct Healing leaf import
is added. Proposal service uses the real emission, receiver floor and finite epoch.

The cone and both joint-step routes use the returned RMonoAll producers.
H2-prime and H6 also receive RMonoAll. Carrier/H2A receive hset.toRecovery₂;
healing_healed receives hset. H4's suffix reader guard is proved by
assembly_healing_suffix_reader from the actual gate, applied wakes and horizon.
No service input is left for these returned producers.

## Four remaining H2 results

These are explicit arguments of the smallest per-run Assembly lemmas. They are
not record fields or universal services. The regime, actual witness and guards
are the ones in the P-H2 Round 8 handoff. They are true in the ordinary finite
sleep regime; their general production remains P-H2 Round 9 work.

```lean
namespace AvailableChain.FGSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
variable (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
variable (hset : HealingSet p c E rho G ΔF) (hbound : LivenessBoundW p ΔF)
variable (w : HealingWitness) (hreset : H0Reset p c E rho w)

-- assembly_healingInput_of_inv; owner P-H2, through postReset_joint₂_all.
variable (inv : ∀ i, PostResetInv p c E rho w i)

-- assembly_resetArrivalFull_at and assembly_hTime_at; owner P-H2.
variable (extension : p.δt = 2 * p.R →
  ∀ w, H0Reset p c E rho w →
    p.actionTime w.rStar + Γ p G + 4 * p.Δ ≤ rho.horizon →
    ∃ u Q, H0 p c E rho {w with u := u, QStar := Q})

-- assembly_healingInput_at; owner P-H2. No full reset budget is required.
variable (localInput : p.δt = 2 * p.R →
  ∀ w, H0 p c E rho w → tstar p w ≤ rho.horizon → HealingInput p c E rho w ΔF)

-- assembly_hTime_at; owner P-H2. The complete Jst horizon stays.
variable (fullInput : p.δt = 2 * p.R →
  recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
  ∀ w, H0 p c E rho w →
    HealingInput p c E rho w ΔF ∧
      tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ)
end AvailableChain.FGSA.Run
```

For inv, P-H2 must close postReset_resetLease_succ', postReset_leaseSafe_succ and
postReset_rawTransfer_succ. The returned cone, opening and service steps and
all Foundation inputs are supplied. The older conditional joint-step adapters
are consumers of these exact guarded results; they do not prove the steps.
The named step wrappers await those source ports. No whole-run NoRestart input
is recovered from HealingSet. If a producer telescope changes, the lead must
forward its exact type before the named wrapper can be accepted.

Every other explicit input is proved or has its named producer: hset/hbound,
H0/H0Reset, clock equality and finite horizons are the public run premises;
row origins, emitted names, lease writes, channels, source discipline, finality
cap/head and quorum are the existing Foundation/Finality/Shared producers.

## Exact OPEN routes in the 68-target map

55 targets are GREEN. Each of the following 13 imports Healing.Export and the
same open H2 chain: PostResetLeaseMove -> PostResetLeaseStep -> PostResetRawStep,
plus ReleaseScope. The first exact source blocker is PostResetLeaseMove at
77/102/134/277: the old receipt telescope and removed base.noRestart projection.
P-H2 owns those source ports and the complete Healing.Export route.

- AvailableChainFGSAProofs
- AvailableChainFGSAProofs.Proofs.Assembly.Healing
- AvailableChainFGSAProofs.Proofs.Assembly.ResetArrival
- AvailableChainFGSAProofs.Proofs.Assembly.Root
- AvailableChainFGSAProofs.Tests.Axioms
- AvailableChainFGSAProofs.Tests.FGCompose
- AvailableChainFGSAProofs.Tests.HealingHTime
- AvailableChainFGSAProofs.Tests.HealingReset
- AvailableChainFGSAProofs.Tests.LiveDC
- AvailableChainFGSAProofs.Tests.NonVacuity.Adversarial
- AvailableChainFGSAProofs.Tests.NonVacuity.FinalityClaims
- AvailableChainFGSAProofs.Tests.NonVacuity.HealingClaims
- AvailableChainFGSAProofs.Tests.WeakContinuationGrowthAssemblyAxioms

Exact transitive routes: .lake/sleep-pas-r8/target-blockers.log.
The facade also reaches stale HealingPhaseSettle:89/139 and HealingRiseOne
callers (P-H2). HealingFrontierRead:77/108/140/175/205/248 is an additional
P-H1-map caller failure on the returned healing API. The lead must route that
caller port. All are recorded separately in assigned-build.log. No test source
outside the P-As fixtures is changed here.

Full manifest and canonical coverage stop at the missing P-H2
PostResetLeaseMove.olean. The legacy snapshot repair already on this base passes.
No snapshot, baseline, import allowance or checker code is changed here.
