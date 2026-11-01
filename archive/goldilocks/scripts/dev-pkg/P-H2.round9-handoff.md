# P-H2 Round 9 handoff

Branch: sleep-ph2j. Base: 15ed93b9.
The original 114 assigned targets have no H2 proof obligation left.
The map also registers PostResetRaw as the support target for its bounded companion.
Source commit: e4a91ac1.
H2 producer proofs are complete. The full claim snapshot remains blocked on
existing H1 and P-As caller ports listed below.

## Producers for P-As

All names are in AvailableChain.FGSA.Run. The four result types requested in
round 8 stay unchanged. Assembly must replace the corresponding explicit inputs
with these producers. No induction step or healing service record remains an input.

- inv: healing_postReset_inv_recovery.
- extension: healing_h0_extension_recovery.
- localInput: healing_localInput_recovery.
- fullInput: healing_fullInput_recovery.

Their home is Proofs/Healing/HealingInputExport.lean. Healing.Export imports it.
The common telescope below lists every explicit run input. These are existing
Foundation, row-permission and finality laws. Their names are listed after the types.
The complete kernel-printed telescopes are in
.lake/sleep-ph2j/producer-types-final.log.

```lean
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
variable (p : Params)
variable {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
variable [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    (cap : RCap p c E rho) (source : TSrc p c E rho)
    (heldRows : ∀ e x W, HeldAt p c E rho e x W →
      ∀ u ∈ chainRows W, ∃ (a : RowWire p.n) (r : Nat),
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∃ k o t, k < e ∧ rho.events[k]? = some (.deliver x o t) ∧
          ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
            HonestRowBefore p c E rho e z r a ∧ p.actionTime r ≤ t)
    (finalityCap : ∀ (y i : Nat), 0 < y → ∀ x W, HeldAt p c E rho i x W →
      y ≤ (finalityView p W).h_F →
      ∃ z r a u, HonestRowBefore p c E rho i z r a ∧ RowSigner p c rho a z ∧
        RowWire.toRow? a = some u ∧ u ∈ chainRows W ∧
        u.finality_pair = some ⟨(finalityView p W).h_F, (finalityView p W).F.root⟩)
    (hhead : ∀ {j r : Nat} {z : V} {a : RowWire p.n} {u : Row (Fin p.n)},
      HonestRowAt p c E rho j z r a → RowSigner p c rho a z →
      a.toRow? = some u → ∀ fp, u.finality_pair = some fp →
      ∃ H, HeldAt p c E rho j z H ∧ fp.height = (heightView p H).h_j ∧
        fp.target = (heightView p H).J.root ∧
        KitFG.TargetQCAt p.E H fp.height (heightView p H).J)
    (rowCovered : ∀ (_hb : Base₂ p c E rho)
      (_hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
      (x : V), x ∈ rho.honest → ∀ (r : Nat) (nd : Node p),
      postClock E rho x (p.actionTime r) = some nd → ∀ C : FGBlock (Fin p.n),
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st → (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
```

The ordered common arguments are:

```lean
p c E rho hrec mono emittedNonempty emittedName writes xing origin
  cap source heldRows finalityCap hhead rowCovered
```

The following declaration headers use that common telescope. They give the exact
returned types. The joint producer also returns the reset lease, opening and cone cuts.

```lean
theorem healing_postReset_joint_recovery {w : HealingWitness}
    (hreset : H0Reset p c E rho w) :
    ∀ i, PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
      PostResetOpeningDomain p c E rho w i ∧ PostResetRetainedConeP p c E rho w i

theorem healing_postReset_inv_recovery {w : HealingWitness}
    (hreset : H0Reset p c E rho w) : ∀ i, PostResetInv p c E rho w i

theorem healing_h0_extension_recovery (_hδ : p.δt = 2 * p.R) :
    ∀ w, H0Reset p c E rho w →
      p.actionTime w.rStar + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∃ u Q, H0 p c E rho {w with u := u, QStar := Q}

theorem healing_localInput_recovery (rows : TRows p c E rho ΔF)
    (_hδ : p.δt = 2 * p.R) :
    ∀ w, H0 p c E rho w → tstar p w ≤ rho.horizon → HealingInput p c E rho w ΔF

```

fullInput omits hrec from the common arguments. It uses hset as the recovery input.
It additionally takes the exact rows, emittedPairs, progressCoverage, fold and quorum
laws below. No new horizon is added to localInput.

```lean
theorem healing_fullInput_recovery (hset : HealingSet p c E rho G ΔF)
    (hbound : LivenessBoundW p ΔF) (rows : TRows p c E rho ΔF)
    (emittedPairs : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
      {e : Height × BlockId}, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho)) :
    p.δt = 2 * p.R →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w →
        HealingInput p c E rho w ΔF ∧
          tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ
```

## Remaining explicit inputs and their producers

P-As owns the Foundation-to-Healing wiring. All these laws have named producers:

- hrec or hset: the existing HealingSet / RecoverySleep₂ premise.
- mono: fgsa_rMonoAll. Use the all-restart form.
- emittedNonempty: sourceDiscipline_emittedNonempty.
- emittedName: emittedName_window at hset.base.valid.toScheduleWellFormed.
- writes: fgsa_leaseOrigins_lastWrite at the same schedule. Its final clause includes
  joinedNow p pre = true. The complete type is in the common telescope.
- xing: fgsa_rXing with hset.base.idealization, linked, fault count and signatures.
- origin: sourceDiscipline_qcOrigin with the existing Base/fault package and fgsa_rStore.
- cap: fgsa_rCap_channel.
- source: sourceDiscipline_tSrc.
- heldRows: held_chain_row_origin_before.
- finalityCap: fgsa_finalityCap.
- hhead: cap_finality_head.
- rowCovered: rowPermission_covered E rho. Keep its Base and fault arguments.
- rows: fgsa_tRows_recovery p c E rho hset.toRecovery₂.
- emittedPairs: healing_reset_emittedName in Assembly/ResetArrival, whose exact type
  is unchanged; sourceDiscipline_emittedName plus heightView_eq_simplex gives it.
- progressCoverage: fgsa_batchCoverage p ΔF .progress c E rho.
- hfold: fgsa_foldTrichotomy_progress p.
- faultQ: fgsa_faultQ_of_count p hset.fault.
- honestQuorum: kmid_honest_quorum p c rho hset.base.linked hset.fault.
- hbound: the existing LivenessBoundW premise.
- hδ: the existing clock premise p.δt = 2 * p.R.

No input above is an OPEN H1 request. The conditional claim-composition wrappers
in Healing.Export keep their existing Foundation supplier arguments. For their
proposal-service input, use healing_proposal_receipt_recovery. For permanence,
use healing_tPerm_recovery with mono, xing and writes. Row receipt comes from rows.receipt.

## Guarded steps and finite receipts

The three produced steps are:

- postReset_resetLease_succ' in PostResetRawStep.
- postReset_leaseSafe_succ in PostResetLeaseStep.
- postReset_rawTransfer_succ in PostResetRawStep.

They return exactly ∀ i, PostResetResetLeaseStep / PostResetLeaseStep / PostResetRawStep
p c E rho w i. Their complete telescopes are kernel-printed in producer-types-final.log.
The joint producer constructs them, the cone step, opening step and service step.
P-As can consume inv directly.

healing_source_before_receipt_at_recovery in PostResetLeaseMove is the bounded
earlierRead adapter requested in round 8. Its complete type follows.

```lean
theorem healing_source_before_receipt_at_recovery [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (source : TSrc p c E rho) {i k : Nat} {K : FGBlock (Fin p.n)} {s u : Slot}
    {x : V} {t : Time} (hSource : SourceBefore p c E rho i K s) (hsu : s ≤ u)
    (hSync : E.t_GST ≤ SA.voteTime p.toParams u) (hx : x ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick x t)) (hafter : SA.freezeTime p.toParams u < t)
    (hFloor : FGBlock.Preceq (storeAt p c E rho k x).fg.F K) :
    TargetReceiptService E rho (eraseFG K) (SA.freezeTime p.toParams u) x
```

healing_output_moving_suffix_at in PostResetRaw is the bounded companion used by
H2. Its batch callback has this exact type:

```lean
∀ l, s + 1 ≤ l → timeIdx rho (SA.voteTime p.toParams l) ≤ cut →
  SA.voteTime p.toParams l ≤ rho.horizon →
  Gen.Pure.Batch (joinedHonest p E rho (SA.voteTime p.toParams l)).card
    (Gen.V2.Duty.faulty rho).card
```

The two uses prove the horizon guard from actual gate ticks. The original H1
healing_output_moving_suffix statement is byte-identical; its body wraps the
bounded companion. All other pre-existing statements in that H1 file are unchanged.

The old unbounded callback is false as a recovery producer. Use the concrete
HealingFixture.params and HealingFixture.run from FGSARun/Model/HealingFixture:
Δ=1, n=1, k=2, R=3, δt=6, GST=0, horizon=304, G=4 and ΔF=3. The trace has one
tick at each integer time 0..304, followed by self-delivery of each emitted object.
Set the environment's awake function to decide(t <= 304); keep all other fields
and the exact trace. The environment is unchanged at every time used by this
finite recovery run. It is asleep after time 304. For s=2, l=77 and
cut=run.events.length, voteTime(l)=309 and timeIdx(309)=cut. The old callback asks
for Batch 0 0, which is false. H2 stops this request and uses the finite companion.
The requested inv, extension, localInput and fullInput result types are unchanged.

## Sleep and deadline coverage

Receipt service uses the actual read and selected target, with its receiver floor.
Frozen volatile views use local restart-free epochs after the complete GST cut.
No proof recovers NoRestart from recovery. No future vote is requested past the
finite horizon. All relay inputs use HeadRelayLocalServiceScope.

A written reset extension proves postReset_written_ready and postReset_written_window.
The fast first transfer releases every incompatible lease, with no lease-age or
upper-k premise. Reset release uses the actual post-Jst source batch. Thus a live
pre-GST lock when k > 2R+3 is covered by release, not expiry.

Phase entry is recoveryStart p E. RowPermissionAt and saved transport windows stay
at GST. Budget sums, deadline constants and public claims are unchanged.
Only u and QStar change in the full-H0 extension.

Tests use the returned named producers. HealingReset has no Assembly import;
its private test adapter discharges the existing Foundation leaves. P-As owns
Assembly and Tests/NonVacuity. This writer changed neither tree.

## Validation and integration limits

All evidence is in .lake/sleep-ph2j/.

- dck-final.log: PASS. All original 114/114 targets are GREEN. The map has
  115/115 GREEN targets after the bounded support target is registered, and
  585 GREEN roots. All 50 strict groups passed: 3,699 permitted axiom results.
  All 24 DCK controls passed. Counts are also in package-counts.log.
- exports-final.log: all 585 GREEN roots; 474 proof modules, 253 exports,
  zero unaccepted. No baseline or allowance change.
- bounded-companion-build.log: Export and the four requested test ports pass --wfail.
- producer-types-final.log: complete exact types, including the bounded companion.
- source-audit.log: no admission, overlong changed Lean line, public/source change,
  H1 statement change, Assembly edit or NonVacuity edit.
- layers-final.log: 72 inherited findings, zero new. headers-final.log: PASS.
  sleep-scopes-final.log: PASS.
- manifest-first.log: the required full script passes FG-SA shallow/deep,
  legacy, V2, generic and Compose snapshots. It then stops at the full claim API
  import because HealingFrontierRead.olean is missing. The legacy KitFG.pins
  mismatch is fixed. Full manifest PASS is not claimed.
- manifest-source-build.log: the required snapshot source build finds the caller
  errors below. These are outside this writer's source changes.

P-As owns these remaining integration ports:

- Assembly/ResetArrival.lean:106, plus the successor calls at 480 and 499.
  Use RMonoAll and the returned source arguments, or consume inv directly.
- Assembly/Healing.lean:68.
- Tests/NonVacuity/HealingPackages.lean:453 (restore now takes a time argument).
- Tests/NonVacuity/HealingFirst.lean:205 (same restore API).
- Tests/NonVacuity/HealingReset.lean:202 (same restore API).

H1 owns the remaining snapshot test callers:

- Tests/HealingPhaseSettle.lean:89 and 139.
- Tests/HealingFrontierRead.lean:77, 108, 140, 175, 205 and 248.

No change is made to these H1 statements or to the P-As files. These ports are
needed for full Root and the global claim snapshot. They do not leave an H2
producer obligation. Re-run the full manifest after the owning packages are joined.
