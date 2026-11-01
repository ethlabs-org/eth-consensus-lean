# FG-SA outage continuation under (V), w3

Status: proved and validated.
Branch: fgsa-outage-v. Base: 43733fe. No push.
No FinalitySlashableBound premise is needed.

## Commits

W1 and w2 end at 258bdb8b. Policy commit 1 is already present as 5dd22552.
W3 code commits:

- 92219616 Prove uncontested continuation HEAD coverage from frozen receipts
- 7670bb08 Prove outage continuation by joint event and label induction
- 84ef999e Policy-only: allow the approved OutageContinuation Export imports
- bc6cdbae Export the proved outage continuation claim under (V)

The second policy commit changes only scripts/check-layers.py. It permits
exactly Timing, Induction, Receipt, Frame, Gate, and Joint from the Outage
lane at OutageContinuation/Export. No other rule or allowance was changed.
All commits have the requested Claude-Session trailer.

## Exact companion

`Claims/OutageContinuation.lean` defines `OutageContinuationClaim p`.
It quantifies over every finite validator type V, codec c, environment E,
run rho, mode fast, times T, b₀, b₁, and row delay ΔF.
Its premise `OutageContinuationPrem` has exactly these fields:

- `pre`: `HealthyPrefix₂ p c E rho b₀ ΔF`, including Base₂ and acceptance relay.
- `sleepy`: the unchanged pre-b₀ sleepy inequality from Outage₂.
- `order`: `0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ rho.horizon`.
- `lag`: `T + (if fast then 4*p.Δ else L p - 3*p.Δ) ≤ b₀`.
- `lengthV`: `b₁ - b₀ + (b₀ - 6*p.Δ) % (4*p.Δ) ≤ L p`.
- `fastPart`: the unchanged pre-b₀ high-participation field from Outage₂.
- `sync`: full-run `PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF)`.
- `gst`: `E.t_GST ≤ b₁`.
- `partAfter`: `faulty.card < awakeHonest(t).card` for `b₁ ≤ t ≤ horizon`.

Here `L p = (4*(p.k : Time)-1)*p.Δ`. There is no eta budget and no
participation condition on [b₀,b₁). There is no FinalitySlashableBound.

The conclusion is: for every honest x and block B below
`S_at p c E rho (timeIdx rho T) x`, every honest y and `b₀ ≤ t ≤ horizon`
satisfy all four facts:
`B ⪯ S_at(...,timeIdx rho t,y)`, `B ⪯ stable_y(t)`,
`B ⪯ confirmed_y(t)`, and `B ∥ F_at(...,timeIdx rho t,y)`.
All reads are inclusive.

## Proof closure

`fgsa_outageContinuationClaim p : OutageContinuationClaim p` is the
proved unconditional companion theorem. The final assembly is in
`Assembly/Clean.lean:78`.
It uses the existing Clean cut and foundation producers. The claim-to-claim
bridge is in Shared/Claims. OutageContinuation/Export proves the matching claim from expanded
supplier interfaces. The frozen FGSAClaims record and old claims remain unchanged.

W3 adds three Receipt theorems:

- `outageV_covering_head_receipts`: authentic previous HEADs and all their
  paths reach the early cut. The next HEAD has their votes in its merged
  support pool and their ancestors in its frozen voter set.
- `outageV_frozen_path_receipt`: an old source accepted through the early
  boundary relays before freeze. Current F and monotonic F exclude conflicts.
- `outageV_uncontested_head`: the actual uncontested HEAD covers B.
  Its height witnesses are frozen. No receipt or score premise remains.

ContinuationJoint adds ten theorems:

- `outageV_history_through_relay`: event induction derives original source
  history and F compatibility through the regression relay cut.
- `outageV_contest_relay`: a contest supplies one exact carrier to all
  honest receivers. Its F exclusion facts come from earlier-label gates.
- `outageV_events_through_relay`: source history and S survive each event.
  Gate writes use the current result. Deliveries use the successor F fact.
- `outageV_received_marker_head`: the exact carrier stays in the cumulative
  store and protects later clocked HEAD reads.
- `outageV_clocked_root_compatible` and `outageV_clocked_contested_head`:
  scoped names and the output after the tick supply the actual frame facts.
- `outageV_restored_heads`: strong label induction proves compatibility
  for every restored scheduled HEAD. Before the first regression, HEADs
  cover B. A contest at that regression supplies the later marker.
- `outageV_first_restored_head`: the healthy batch or pre-expiry protection
  seeds coverage. It includes a sleeping node's deterministic read.
- `outageV_armed_outputs`: arming and the two inductions give every requested
  inclusive read, including deliveries at the horizon.
- `outageV_body`: both original modes supply arming at auxiliary endpoint
  b₀. Condition (V) supplies the restored-label bound.

The three wiring theorems are `outageContinuation_claim_of`,
`outageContinuation_of_body`, and `fgsa_outageContinuationClaim`.
All 69 typed helper and theorem audits use only propext, Classical.choice,
and Quot.sound. The full companion theorem uses exactly those three.
No sorry, admit, or new axiom was added.

## Open items and old reads

No paper proof fact remains open. No extra guard ruling is requested.
The kernel premise witness is complete in `Tests/OutageContinuationInhabit.lean`.
`outageContinuation_inhabited_sleep` proves every field of
`OutageContinuationPrem` in both modes for a 1-node run with full honest
sleep on [8,13). Condition (V) holds at equality. `not_outage₂` proves that
the old budget fails for this run.

The separate 168-event fixture in `Tests/OutageContinuationSleep.lean`
passes 18 executable audits. It permits full honest sleep on [17,21),
satisfies (V) at equality, and retains B through horizon 30. Its full kernel
premise proof remains open. The 583cee0 parameters still violate (V), by decide.

`Tests/OutageAfterWindowCounterexample.lean` checks the old budget and
output loss after recovery. It is an executable counterexample to extending
the old budget through the horizon, not to the old finite-window claim.

The final old-read audit passes. It scans 8,781 constants in 471 active
modules. The six old/finality readers and 185 height-only readers match
the unchanged baseline. No new read requires a lead ruling.
No old-read baseline or other allow list was changed.

## Validation

The final source passes all required checks:

- The full proof library and touched axiom tests build with --wfail.
- `bash scripts/check-build.sh` passes (a) through (j).
- Layers report zero new findings. GLY, including F-31, passes.
- `bash scripts/check-fgsa.sh` passes, including negative controls and old reads.
- The NEG=0 claims check passes axioms, coverage, used constants, lease checks,
  proof equations, unused imports, and the existing weak-continuation witness.
- The API manifest has 1,189 entries in 52 modules. All hashes match.
- All 69 explicit axiom audits pass. The full claim has only standard axioms.

CheckProofEqns has zero unaccepted exports and zero Gen exports. The import
audit needs no new keep marker. A direct scope check admits exactly the six
approved Export imports and rejects other Outage modules and other lanes.
A direct type check confirms that the Export concludes OutageContinuationClaim.

All existing Statements/Claims, FGSAClaims, model, run, generic, and kit files
remain byte-identical to 43733fe. Only the two approved guard edits differ.
The w3 additions are proofs, so the API manifest needs no new entries.

Successful final logs: /tmp/outage-w3-final2-build.log,
/tmp/outage-w3-final2-check-build.log, /tmp/outage-w3-final2-layers.log,
/tmp/outage-w3-final2-gly.log, /tmp/outage-w3-final2-fgsa.log,
/tmp/outage-w3-final2-claims.log, /tmp/outage-w3-final2-manifest.log,
and /tmp/outage-w3-final2-axioms.log. The earlier §3 commit passed its full
suite in /tmp/outage-w3-receipt-*.log. Exact audit targets are in
[OutageContinuationAxioms.lean](../../Tests/OutageContinuationAxioms.lean).
The normal shared Lean throttle was used. Sandbox access was needed for
its existing shared lock. No throttle bypass, lake update, agent, review
process, or push was used.
