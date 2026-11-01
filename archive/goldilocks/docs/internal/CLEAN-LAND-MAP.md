# Clean lane landing map

This map records the renames and deletions made when the clean lane
(`pcsa-w2-clean` at `9242cad3`) was merged with main `c30bb265`, then `b7946b9b` and
`6611726b`, on `pcsa-clean-land`. Port later clean-lane commits with this map.

All names are in `AvailableChain.PCSA` or `AvailableChain.PCSA.Run`, as
before. Module paths are relative to `AvailableChainPCSAProofs/Proofs/`.

## Deleted modules (use the Shared module)

| Old module | New module |
|---|---|
| `Clean/BodyAdmission` | `Shared/BodyAdmission` |
| `Clean/BodyPersistence` | `Shared/BodyPersistence` |
| `Clean/BodyReceipt` | `Shared/BodyReceipt` and `Clean/AckTargetBody` |
| `Clean/Clock` | `Shared/Clock` (import `Clean/Saturation` directly) |
| `Clean/TreeReceipt` | `Shared/TreeReceipt` |
| `Clean/BodyScope` | `Shared/BodyScope` |

A file that imported `Clean.BodyReceipt` now imports `Clean.AckTargetBody`.
That module imports `Shared.BodyReceipt` and `Clean.AckAdmit`, so the old
import closure is kept. `Clean.AckAdmit` imports `Shared.Clock` and
`Clean.Saturation` in place of `Clean.Clock`.

## New module

| Module | Contents |
|---|---|
| `Clean/AckTargetBody` | `pcsa_ack_target_body_before_freeze` (moved from `Clean/BodyReceipt`, unchanged statement) and its private helper `pcsa_c3_idxBefore_mono` |

## Renamed declarations

| Old name | New name |
|---|---|
| `pcsa_clean_clock_body_scope` | `pcsa_clock_body_scope` (Shared/BodyScope) |
| `Run.pcsa_clean_body_scope` | `Run.pcsa_body_scope` (Shared/BodyScope) |
| `Run.pcsa_clean_scoped_root_eq` | `Run.pcsa_scoped_root_eq` (Shared/BodyScope) |
| `pcsa_admitBlock_proposals` (Clean/ProposalStore) | `pcsa_clean_admitBlock_proposals` |
| `pcsa_bestPC_slot_ge` (Clean/ViewRank) | `pcsa_clean_bestPC_slot_ge` |
| `Run.pcsa_formation_freeze_keep` (Clean/AckAdmit) | `Run.pcsa_clean_freeze_keep` |

The two last renames remove clashes with other lanes. The outage lane on
main has `Outage/Choice.pcsa_bestPC_slot_ge`, an existential statement. The
formation lane (`c45746d1`) has `Clean/FormationFreeze.pcsa_formation_freeze_keep`
under `Base₂`. The Clean versions keep their statements.

The Clean `pcsa_admitBlock_proposals` has a different statement from
`Foundations/Proposals.pcsa_admitBlock_proposals`, which keeps the name.
The Clean version takes the admission premises and gives the exact append.

## Deleted declarations (same statement on main)

| Deleted Clean copy | Main declaration |
|---|---|
| `Clean/PCScope.pcsa_clock_pcs` | `Shared/PCViews.pcsa_clock_pcs` |
| `Clean/ProposalReceipt.pcsa_clock_proposals` | `Foundations/Proposals.pcsa_clock_proposals` |
| `Clean/ProposalStore.pcsa_process_proposals_mono` | `Foundations/Proposals.pcsa_process_proposals_mono` |

`Clean/PCScope` imports `Shared.PCViews`. `Clean/ProposalReceipt` imports
`Foundations.Proposals`.

The 20 declarations of the deleted modules above keep their names in the
Shared modules: `pcsa_body_not_excluded`, `pcsa_body_accepted`,
`pcsa_tree_correspondence`, `pcsa_fullTree_of_frame`, `pcsa_body_clock_fg`,
`pcsa_body_process_fg_mono`, `pcsa_body_clock_keep`,
`pcsa_body_process_keep`, `Run.pcsa_body_stateBefore_mono`,
`pcsa_body_insert_data`, `pcsa_admitBlock_body_mem`,
`pcsa_c3_process_body_pred`, `pcsa_process_new_body`,
`Run.pcsa_body_receipt_origin`, `Run.pcsa_body_handles_direct`,
`Run.pcsa_body_relay_before_deadline`, `pcsa_clock_now`, `pcsa_process_now`,
`Run.pcsaClock`, `Run.pcsa_clock_read`.

## Removed claims

The six pending-label claims (and their `_def` theorems) are removed from
`AvailableChainPCSAClaims/Claims/Clean.lean` and from `Tests/Axioms.lean`.
The outage lane owns them: `CleanResultsNonemptyClaim`,
`CleanResultsChainPendingClaim`, `CleanHeadsAbovePendingClaim`,
`CleanDisseminationPendingClaim`, `CleanHeadsPastCutClaim`,
`CleanBlockReceiptClaim`.
