# P-H2 Round 6 exact handoff

Status: PREPARED / OPEN. Base af373881, branch sleep-ph2g.
Do not merge this status with proof closure. Claims and Statements were not edited.
P-H1 r7 is at 49854c76 and is not merged here.

The independent promotion and selected settlement proofs compile. The joined gap
and selected proposal-parent reader-floor proofs compile. The latter retains the
parent at its original source and uses the actual receiver certificate through RXing.
It adds no receipt, exclusion, or universal carrier assumption.

P-H1 r7 calls its phase record SupportPermanenceServices. H2 now uses that actual
name. It is indexed by u/v/m/J/contest; it is not a whole-run service record.
The current opening/rise call sequence is the one in the r7 handoff:
healing_tPerm_at E rho hrec mono crossing writes hready hphase hServices
  hhead hgate hbody.
Repair's two budget branches use the r7 universal wrapper over the existing ready
phase factory. Their gap queries use recoveryStart <= proposal(threshold).
The frontier seed has only one phase record. It must not require a whole-run TPerm
merely to get the lease cover of q+1.

## Exact P-H1 requests

1. Merge healing_ready_read_cutoff, ResetScope.lean:68 at 4e506874.
The explicit argument readyCut in healing_settle_start_on has this exact type:

```lean
∀ t, recoveryStart p E ≤ t →
  E.t_GST ≤ slotStartZ p (((slotAt p t : Slot) : Int) - 1)
```

The consumer constructs a real tick after the selected receipt deadline and within
the finite horizon. It then uses this cut and RecoverySleep₂ to prove joinedNow.
No scheduled event is treated as an actual tick. The input is an arithmetic theorem,
not an object service, a new record field, or a new public premise.

2. Add these phase-local lease-cover adapters in RepairH6 / RepairH6S.
The r7 global TPerm adapters do not meet the frontier's local phase boundary.
P-H1 owns these exact targets. They retain the old expiry/new source split and are
true for the joined phase domain; no first-batch cleanup is requested.
The smallest consumer tfSeed_qSucc_lease_cover takes the two qualified cover
callbacks explicitly. Their bounds are the actual q+1 read and seed gate.
Neither callback is a record field or an unbounded receipt service.

```lean
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

theorem repair_lease_cover_two_at [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    (hServices : SupportPermanenceServices E rho u v m J contested)
    {β : Slot} (hβ : u < SA.proposalTime p.toParams β) {s : Slot}
    (hls : SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams s)
    (hvs : SA.voteTime p.toParams s ≤ v) : RepairLeaseCover E rho s

theorem repair_lease_cover_one_at [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    (hServices : SupportPermanenceServices E rho u v m J contested)
    {b : Slot} (hb : u ≤ SA.voteTime p.toParams b)
    (hSync : E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k)) {s : Slot}
    (hls : SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams s)
    (hvs : SA.voteTime p.toParams s ≤ v) : RepairLeaseCover E rho s

end AvailableChain.FGSA.Run
```

3. The ready phase factory is still P-H1's exact P5 obligation in
P-H1.round7-producers.md. The opening/repair/frontier record fields remain explicit
service inputs, with ready-phase, actual source, enabled gate, receiver-floor,
read-time and epoch guards. No constructor is claimed proved by an aggregate,
restriction lemma, or consumer. H1's universal TPerm wrapper alone does not close P5.

## Remaining P-H2 work

- Finish FrontierService's retained target/scopes calls with the new indexed
  RepairHeadServices. Repair and FrontierSeed now use .target and .scopes under
  a proved receiver floor; the later capped frontier needs its own selected floor.
- FrontierServiceGate cannot turn carriers bounded by v into RepairGateScope's
  carrier field through rho.horizon. Use a bounded local gate interface or construct
  the exact requested source service. Do not extend the read factory past v.
- Complete the three required repair/frontier signature test adapters after the
  source APIs compile. These tests remain assigned EXPECTED-FAIL/P-H2.
- AttemptRows and search callbacks now start at recoveryStart and select a
  PhaseWitnessReceiptScope. Complete their opening/repair argument plumbing.
- The old healing_rPhase wrapper still takes NoRestart. It is a legacy theorem,
  not a sleep producer. The selected retained settlement route uses no NoRestart.
  The complete RPhase producer remains P-H2 work; it must use the sleep-safe spread
  and durable phase-order producers.
- Re-thread the remaining Round 3-5 post-reset records and all-cut suppliers.
  The previous exact reconciliation/handoff notes remain historical evidence,
  not completed producers. No ownership is moved from H2 to H1.

The numeric constants, attempt sums, and GST saved-window transport bounds are
unchanged. The arithmetic tests reject the old source obligations in the four
supplied replays (both GST=21 runs use the same source check). They do not establish
ExecutionValid, signature, CStar, pending-delivery or full run inhabitation.
Those fixture obligations remain open.

## Validation on the unmerged base

- Independent proof/test build: PASS (closed-group-final.log).
- Strict GREEN audits: PASS, 40 sources and 3,345 results. Every result uses only
  propext, Classical.choice and Quot.sound. The new audit has 13 results.
- Layers: 72 inherited findings, zero new. Headers: PASS, zero failures.
- Complete GREEN exports: 320 proof modules, 253 exports, zero unaccepted;
  zero Gen exports. The canonical baseline is unchanged.
- Sleep source scopes: PASS, 1,393 active and 337 deferred PC-SA modules.
- DCK P-H2: FAIL at the inherited ComposeStmt:177 line warning under --wfail.
  P-H1 commit 396d90cc fixes that line, but it is not merged here.
- Required five-module test build: repair/frontier are blocked first by the
  unmerged SupportWrite:229 TPerm start mismatch. Promotion and terminal compile.
- Manifest: shallow FG-SA, deep FG-SA, legacy, V2, generic and compose stages pass.
  The first full run stopped on a missing Claims.Tests.OutageAlignment artifact.
  That artifact now builds. The final Claims stage is being retried separately.

Map: 111 assigned targets; 28 GREEN and 83 open. All open H2 targets keep P-H2.
The seven former GREEN SupportWrite importers are open on this base. The map has
498 GREEN roots. It adds the required D3 modules and the independent regression
audit; it does not hide the open sources or change checker allowances.

Evidence: .lake/sleep-ph2g/. The initial failed probes are retained. Only the final
successful build/audit logs are proof evidence. No H1, Outage, Claims, Statements,
model, checker implementation, canonical baseline, toolchain or dependency file was edited. No push, rebase,
merge, agent/review process, SSH, wrapper bypass, lake update or timeout was used.

## Final Round 6 status

PREPARED / OPEN. Commits: 12aa13e0, c5bb6663, d90c3330, ae971fff,
87270af2, plus the handoff commit that follows. The tracked tree will be clean.

The selected capped-witness receiver-floor proof now compiles:
healing_capped_witness_reader_floor in RecoveryService. Its source witness stays
at its original node. The current receiver certificate and cap prove the floor
before receipt. This covers F movement under the cap. The remaining work is source
witness selection and .target/.scopes plumbing in the later frontier consumer.
The final joined-start audit has 14 permitted results. The earlier full GREEN
strict pass covers 40 sources and 3,345 results; the extra capped-floor result
also passes in the final 14-command audit. All 24 package controls pass.

The last Claims manifest retry is blocked by the missing Outage.ArmingDuty artifact.
OutageAlignment, WeakContinuationW1 and ArmingGate now build without source edits.
The shallow, deep, legacy, V2, generic and compose manifest stages pass. A complete
check-fgsa-manifest.sh PASS is not claimed. DCK still fails on ComposeStmt:177's
inherited warning; the required repair/frontier tests still stop at SupportWrite:229.
Both are repaired on P-H1 r7 and remain unmerged here. Further H2 ports and source
producer closure are still open, as listed above; a merge alone does not close them.

Current map: 111 assigned, 28 GREEN, 83 open; 498 GREEN roots. Complete GREEN
exports have 253 accepted exports and zero unaccepted exports. Headers pass;
layers have 72 inherited findings and zero new findings. The final source diff has
no placeholders or lines over 100 columns. Claims and Statements are unchanged.

The lead must merge P-H1 r7 at 49854c76 and provide the exact local cover adapters
listed above. The readyCut input is already proved there. No merge was performed
by this writer. Local log and state are updated. Evidence: .lake/sleep-ph2g/.
