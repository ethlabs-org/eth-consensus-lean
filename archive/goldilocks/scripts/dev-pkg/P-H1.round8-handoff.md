# P-H1 Round 8 handoff

Status: PREPARED. The Round 7 D3 list remains P-H2 work.
No P-H2 or P-Ou source was changed.

N1: RowPermissionAt and RowPermissionClaim keep GST. Commit b021cfa3 restores
that premise and removes its JOINED-START pin. The shallow and deep products
are regenerated. No other Claims source was changed.

N2: Healing/Export's row-permission wrapper now receives the GST bound its
proof already uses. OpeningCovered and OpeningCoveredLower are P-Fd modules;
their GST inputs remain valid transport bounds. A caller with hready supplies
GST <= u with healing_recovery_start_lower, as in the other phase adapters.
Claims Tests/HealingW already uses Jst for joinedGap and both reset horizons.
No additional start change is required in that test.

H6 floor: fgsa_retainedH6_event_floor and fgsa_retainedH6_time_floor prove
both receiver reads from RetainedH6Input and actual signed proposal emission.
The time form also uses RMonoAll. No receipt or whole-run NoRestart input is
used. repair_head_exact_legacy, repair_head_one and repair_head_two now end
with hServices and hp; delete the old final hFloors argument at a caller.
Their conclusion, lease-cover inputs and source geometry remain the same.
The selected RepairHeadServices.scopes producer is still OPEN/P-H1/P-ShA.

RecoveryProducers supplies count, epoch and enabled-guard constructors, then
conditional assemblies for P3-P10. The exact open leaves are listed in
P-H1.round8-producers.md. An assembly from open factories is not closure.
Use the module's theorem types for the factory argument order.

N4: healing_support_gate_prefix_count derives the threshold from a full
joined batch. healing_ready_batch_release_compat releases incompatible
leases of every age at that batch's actual release. It has no k upper bound
and no expiry premise. Its first/gate object-service inputs remain open.
It can be used at a later full batch. The reset-source fast release already
uses healing_support_release_compat in postReset_resetLease_at_reset.
Do not replace either release proof with pre-GST lease expiry.

Manifest validation: ArmingDuty now builds. Building all merged Outage
modules still fails in ContinuationReceipt, Close and ContinuationInduction.
P-Ou owns these failures. The full auxiliary snapshot also requires the H2
import closure. Missing compiled modules are not accepted audit exclusions.
The final report records the exact validation result and log paths.
