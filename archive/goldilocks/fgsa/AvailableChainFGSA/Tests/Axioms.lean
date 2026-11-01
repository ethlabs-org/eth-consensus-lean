module
public import AvailableChainFGSA.Proofs.Port.VoteMerge -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.Port.ContestFrame -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.Port.Tree -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.Port.Resolution -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.Port.Support -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.Port.Carry -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.Port.LocalReads -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.NamedReachable -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.HeadResolution -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.WindowOccurrences -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.WindowTerminal -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.WindowAdmissionInvariant -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.WindowRetention -- shake: keep (axioms)
public import AvailableChainFGSA.Statements.WindowEntries -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.EmissionFields -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.WindowProvenance -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.WindowHistory -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.WindowLiveness -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.WindowSelection -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.WindowCertificates -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.WindowStore -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.WindowInvariant -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.WindowHeightBridge -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.Head.Score -- shake: keep (F1b.4a axiom audit)
public import AvailableChainFGSA.Proofs.Head.Walk -- shake: keep (F1b.4a axiom audit)
public import AvailableChainFGSA.Proofs.Head.Transfer -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.Head.Pool -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.BlockAncestry
public import AvailableChainFGSA.Proofs.Carrier
public import AvailableChainFGSA.Proofs.Fields
public import AvailableChainFGSA.Proofs.Restart -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.Join -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.ActView
public import AvailableChainFGSA.Proofs.Nesting
public import AvailableChainFGSA.Proofs.Reconcile
public import AvailableChainFGSA.Proofs.Admission
public import AvailableChainFGSA.Proofs.StoreInv
public import AvailableChainFGSA.Proofs.Metadata
public import AvailableChainFGSA.Proofs.CrossNode
public import AvailableChainFGSA.Proofs.Head -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.SetEq -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.LeaseOutput -- shake: keep (axioms)
public import AvailableChainFGSA.Model.WindowViews -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.FrameViews -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.WindowReaders -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.WindowValidity -- shake: keep (axioms)
public import AvailableChainFGSA.Model.Spec.ACState -- shake: keep (axioms)
public import AvailableChainFGSA.Model.Spec.Codec -- shake: keep (axioms)
public import AvailableChainFGSA.Model.Spec.Frame -- shake: keep (axioms)
public import AvailableChainFGSA.Model.Spec.Objects -- shake: keep (axioms)
public import AvailableChainFGSA.Model.Spec.Transitions -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.Spec.Clock -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.Spec.Codec -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.Spec.Frame -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.Spec.Handlers -- shake: keep (axioms)
public import AvailableChainFGSA.Proofs.Spec.Locks -- shake: keep (axioms)

/-! Kernel dependency audit (Task 13 Step 1): one line for each public theorem of
Tasks 2 and 7–12. Each prints only `propext`, `Classical.choice`, `Quot.sound`, or
no axiom. `scripts/CheckFGSAAxioms.lean` checks every FGSA constant mechanically. -/

-- Proofs/Port/Resolution.lean
#print axioms AvailableChain.FGSA.Next.proposerSupportNext_eq_filter
#print axioms AvailableChain.FGSA.Next.proposerSupportNext_sublist
#print axioms AvailableChain.FGSA.Next.mem_proposerSupportNext_iff
#print axioms AvailableChain.FGSA.Next.mem_proposerSupportNext_iff_base
#print axioms AvailableChain.FGSA.Next.proposerSupportNext_unresolved
#print axioms AvailableChain.FGSA.Next.proposerSupportNext_drop
#print axioms AvailableChain.FGSA.Next.proposerSupportNext_keep
#print axioms AvailableChain.FGSA.Next.proposerSupportNext_eq_of_extends
#print axioms AvailableChain.FGSA.Next.proposerSupportNext_incidence
#print axioms AvailableChain.FGSA.Next.proposerSupportNext_supporters
#print axioms AvailableChain.FGSA.Next.proposerSupportNext_seat_support
#print axioms AvailableChain.FGSA.Next.proposerSupportNext_scoreOn
#print axioms AvailableChain.FGSA.Next.proposerSupportNext_score

-- Proofs/Port/Tree.lean
#print axioms AvailableChain.FGSA.Next.mem_tree
#print axioms AvailableChain.FGSA.Next.F_mem_tree
#print axioms AvailableChain.FGSA.Next.tree_subset_TF
#print axioms AvailableChain.FGSA.Next.fullTree_subset_tree
#print axioms AvailableChain.FGSA.Next.mem_erasedList
#print axioms AvailableChain.FGSA.Next.erasedList_eq

-- Proofs/BlockAncestry.lean
#print axioms AvailableChain.FGSA.block_preceq_refl
#print axioms AvailableChain.FGSA.block_preceq_trans
#print axioms AvailableChain.FGSA.block_preceq_antisymm
#print axioms AvailableChain.FGSA.block_genesis_preceq
#print axioms AvailableChain.FGSA.block_preceq_total_of_common
#print axioms AvailableChain.FGSA.block_compatible_comm
#print axioms AvailableChain.FGSA.block_compatible_of_common
#print axioms AvailableChain.FGSA.block_incompatible_of_preceq
#print axioms AvailableChain.FGSA.block_compatible_of_preceq_compatible

-- Proofs/Carrier.lean
#print axioms AvailableChain.FGSA.eraseFG_slot
#print axioms AvailableChain.FGSA.eraseFG_root
#print axioms AvailableChain.FGSA.eraseFG_parent
#print axioms AvailableChain.FGSA.eraseFG_eq_genesis
#print axioms AvailableChain.FGSA.eraseFG_preceq
#print axioms AvailableChain.FGSA.eraseFG_compatible
#print axioms AvailableChain.FGSA.eraseFG_injOn
#print axioms AvailableChain.FGSA.preceq_of_eraseFG_preceq
#print axioms AvailableChain.FGSA.compatible_iff_eraseFG
#print axioms AvailableChain.FGSA.viewRootInj_of_rootInj
#print axioms AvailableChain.FGSA.rootInjectiveOn_of_viewRootInj
#print axioms AvailableChain.FGSA.erase_rootInjective
#print axioms AvailableChain.FGSA.eraseFG_injective
#print axioms AvailableChain.FGSA.encLabel_inj
#print axioms AvailableChain.FGSA.encAuth_inj
#print axioms AvailableChain.FGSA.encRowBody_inj
#print axioms AvailableChain.FGSA.encRowWire_inj
#print axioms AvailableChain.FGSA.appOf_packBody
#print axioms AvailableChain.FGSA.packInner_inj
#print axioms AvailableChain.FGSA.packBody_inj
#print axioms AvailableChain.FGSA.rowsOk_iff
#print axioms AvailableChain.FGSA.rowsOk_node_packBody
#print axioms AvailableChain.FGSA.rows_eq_of_rowsOk

-- Proofs/Fields.lean
#print axioms AvailableChain.FGSA.admitHead_fg
#print axioms AvailableChain.FGSA.admitHead_base_blocks
#print axioms AvailableChain.FGSA.admitHead_base_stable
#print axioms AvailableChain.FGSA.admitHead_obligations
#print axioms AvailableChain.FGSA.admitHead_fastWrite
#print axioms AvailableChain.FGSA.admitHead_genuine
#print axioms AvailableChain.FGSA.admitRow_eq
#print axioms AvailableChain.FGSA.admitBlock_refused
#print axioms AvailableChain.FGSA.onView_fg
#print axioms AvailableChain.FGSA.onView_base_blocks
#print axioms AvailableChain.FGSA.onView_proposals
#print axioms AvailableChain.FGSA.onView_rowPool
#print axioms AvailableChain.FGSA.onView_fastWrite
#print axioms AvailableChain.FGSA.normalizeS_fg
#print axioms AvailableChain.FGSA.normalizeS_fields
#print axioms AvailableChain.FGSA.reconcile_fg
#print axioms AvailableChain.FGSA.freeze_blocks
#print axioms AvailableChain.FGSA.release_blocks
#print axioms AvailableChain.FGSA.saGate_blocks
#print axioms AvailableChain.FGSA.gateStep_fg
#print axioms AvailableChain.FGSA.gateStep_base_blocks
#print axioms AvailableChain.FGSA.gateStep_proposals
#print axioms AvailableChain.FGSA.gateStep_rowPool
#print axioms AvailableChain.FGSA.savedGenuine_append
#print axioms AvailableChain.FGSA.saGate_genuine
#print axioms AvailableChain.FGSA.gateStep_fresh
#print axioms AvailableChain.FGSA.gateStep_saved
#print axioms AvailableChain.FGSA.fastSet_prefix
#print axioms AvailableChain.FGSA.clockPre_fields
#print axioms AvailableChain.FGSA.clockPre_fg
#print axioms AvailableChain.FGSA.clockPre_genuine
#print axioms AvailableChain.FGSA.clockPre_fastWrite
#print axioms AvailableChain.FGSA.clock_fg
#print axioms AvailableChain.FGSA.clock_base_blocks
#print axioms AvailableChain.FGSA.clock_proposals
#print axioms AvailableChain.FGSA.clock_rowPool

-- Proofs/ActView.lean
#print axioms AvailableChain.FGSA.block_compatible_of_preceq
#print axioms AvailableChain.FGSA.block_compatible_of_below
#print axioms AvailableChain.FGSA.eraseFG_ancestor_mem
#print axioms AvailableChain.FGSA.actView_blocks
#print axioms AvailableChain.FGSA.actView_genesis_F
#print axioms AvailableChain.FGSA.actView_ancestor_closed
#print axioms AvailableChain.FGSA.actView_antitone
#print axioms AvailableChain.FGSA.actView_path
#print axioms AvailableChain.FGSA.blockExcluded_stable
#print axioms AvailableChain.FGSA.actView_eq
#print axioms AvailableChain.FGSA.actView_fields
#print axioms AvailableChain.FGSA.actView_noVeto
#print axioms AvailableChain.FGSA.actView_releaseCount_zero
#print axioms AvailableChain.FGSA.actView_onView
#print axioms AvailableChain.FGSA.actView_admitHead
#print axioms AvailableChain.FGSA.clockPre_eq
#print axioms AvailableChain.FGSA.onView_onView
#print axioms AvailableChain.FGSA.clock_eq_saClock_offGate
#print axioms AvailableChain.FGSA.clock_eq_saClockFrom_gate
#print axioms AvailableChain.FGSA.clock_eq_saClockFrom_gate'

-- Proofs/Nesting.lean
#print axioms AvailableChain.FGSA.outputNesting_v1
#print axioms AvailableChain.FGSA.normalizeS_nest
#print axioms AvailableChain.FGSA.reconcile_nest
#print axioms AvailableChain.FGSA.gateStep_nest
#print axioms AvailableChain.FGSA.admitRow_nest
#print axioms AvailableChain.FGSA.foldl_admitRow_nest
#print axioms AvailableChain.FGSA.admitProposal_stable
#print axioms AvailableChain.FGSA.process_nest
#print axioms AvailableChain.FGSA.clockPre_stable
#print axioms AvailableChain.FGSA.clock_nest
#print axioms AvailableChain.FGSA.outputNesting_stored
#print axioms AvailableChain.FGSA.finalized_preceq_stable

-- Proofs/Reconcile.lean
#print axioms AvailableChain.FGSA.reconcile_eq
#print axioms AvailableChain.FGSA.reconcile_obligations
#print axioms AvailableChain.FGSA.reconcile_genuine
#print axioms AvailableChain.FGSA.reconcile_savedGenuine
#print axioms AvailableChain.FGSA.reconcile_fastWrite
#print axioms AvailableChain.FGSA.reconcile_stable
#print axioms AvailableChain.FGSA.reconcile_frame
#print axioms AvailableChain.FGSA.storeControls_reconcile
#print axioms AvailableChain.FGSA.preceq_normal
#print axioms AvailableChain.FGSA.reconcile_idem
#print axioms AvailableChain.FGSA.reconcile_saCompat
#print axioms AvailableChain.FGSA.stable_preceq_normal
#print axioms AvailableChain.FGSA.reconcile_harmless
#print axioms AvailableChain.FGSA.reconcile_fastOrigin
#print axioms AvailableChain.FGSA.mem_genuine_of_saved
#print axioms AvailableChain.FGSA.reconcile_harmless_origin

-- Proofs/Admission.lean
#print axioms AvailableChain.FGSA.CStoreInv.toInv0
#print axioms AvailableChain.FGSA.pickPair_some_spec
#print axioms AvailableChain.FGSA.parentFG_spec
#print axioms AvailableChain.FGSA.parentFG_isSome_iff_root
#print axioms AvailableChain.FGSA.admitBlock_missingParent
#print axioms AvailableChain.FGSA.eraseFG_fgBlock
#print axioms AvailableChain.FGSA.fgBlock_parent
#print axioms AvailableChain.FGSA.fgBlock_slot
#print axioms AvailableChain.FGSA.fgBlock_root
#print axioms AvailableChain.FGSA.fgBlock_rows
#print axioms AvailableChain.FGSA.fgBlock_notMem
#print axioms AvailableChain.FGSA.toRow_forall₂
#print axioms AvailableChain.FGSA.blockAccepted_of_wellFormed
#print axioms AvailableChain.FGSA.rootTest_iff_blockTest
#print axioms AvailableChain.FGSA.blockAccepted_slot_pos
#print axioms AvailableChain.FGSA.blockAccepted_facts
#print axioms AvailableChain.FGSA.blockAccepted_rowsOk
#print axioms AvailableChain.FGSA.accepted_base_facts
#print axioms AvailableChain.FGSA.fg_on_block_accepts
#print axioms AvailableChain.FGSA.admitVote_withBlocks
#print axioms AvailableChain.FGSA.foldVotes_withBlocks
#print axioms AvailableChain.FGSA.foldVotes_fields
#print axioms AvailableChain.FGSA.admitProposal_of_accept
#print axioms AvailableChain.FGSA.base_admitProposal_accepts
#print axioms AvailableChain.FGSA.activeCompatible_eq
#print axioms AvailableChain.FGSA.foldl_admitRow_eq
#print axioms AvailableChain.FGSA.admitBlock_accepted_eq
#print axioms AvailableChain.FGSA.accepted_F_facts
#print axioms AvailableChain.FGSA.foldl_admitRow_view
#print axioms AvailableChain.FGSA.admitProposal_base_view
#print axioms AvailableChain.FGSA.actView_admitBlock_sameF
#print axioms AvailableChain.FGSA.actView_admitBlock_movedF
#print axioms AvailableChain.FGSA.admitBlock_sufficient
#print axioms AvailableChain.FGSA.admitBlock_sufficient_absent

-- Proofs/StoreInv.lean
#print axioms AvailableChain.FGSA.viewRootInj_TF
#print axioms AvailableChain.FGSA.fgsa_storeControls_eq_of_top_retained
#print axioms AvailableChain.FGSA.J_mem
#print axioms AvailableChain.FGSA.Z_mem
#print axioms AvailableChain.FGSA.savedGenuine_congr
#print axioms AvailableChain.FGSA.fastOrigin_congr
#print axioms AvailableChain.FGSA.cstoreInv_of_sublist
#print axioms AvailableChain.FGSA.cstoreInv_normalizeS
-- ROOT-DIGEST W3: deleted global-root audit; scoped replacement.
#print axioms AvailableChain.FGSA.storeStepRoots_of_blockAccepted
#print axioms AvailableChain.FGSA.cstoreInv_init
#print axioms AvailableChain.FGSA.cstoreInv_accepted_pre
#print axioms AvailableChain.FGSA.cstoreInv_admitBlock
#print axioms AvailableChain.FGSA.cstoreInv_process
#print axioms AvailableChain.FGSA.clockPre_obligations_sublist
#print axioms AvailableChain.FGSA.cstoreInv_clockPre
#print axioms AvailableChain.FGSA.writeObligation_keys
#print axioms AvailableChain.FGSA.writeKeys_keys
#print axioms AvailableChain.FGSA.saGateWriteKeys_level
#print axioms AvailableChain.FGSA.saGate_cases
#print axioms AvailableChain.FGSA.ne_of_saved
#print axioms AvailableChain.FGSA.notMem_keys_of_unsaved
#print axioms AvailableChain.FGSA.compat_of_confirmation
#print axioms AvailableChain.FGSA.cstoreInv_gateFresh
#print axioms AvailableChain.FGSA.cstoreInv_gateStep
#print axioms AvailableChain.FGSA.saCompat_gateStep
#print axioms AvailableChain.FGSA.fastOrigin_gateStep
#print axioms AvailableChain.FGSA.cstoreInv_clock
#print axioms AvailableChain.FGSA.storeInvariant
#print axioms AvailableChain.FGSA.fg_step_cases
#print axioms AvailableChain.FGSA.process_TF_new
#print axioms AvailableChain.FGSA.fMonotone
#print axioms AvailableChain.FGSA.process_F_mono
#print axioms AvailableChain.FGSA.clock_F_eq
#print axioms AvailableChain.FGSA.process_hmax_mono
#print axioms AvailableChain.FGSA.process_pair_mono
#print axioms AvailableChain.FGSA.actView_eq_image
#print axioms AvailableChain.FGSA.admitBlock_reconcile_harmless
#print axioms AvailableChain.FGSA.fgBlockOf_spec
#print axioms AvailableChain.FGSA.deepest_spec
#print axioms AvailableChain.FGSA.fgHead_stored
#print axioms AvailableChain.FGSA.rootInjectiveBelow_base
#print axioms AvailableChain.FGSA.leaseOf_eq_deadlineOf

-- Proofs/Metadata.lean
#print axioms AvailableChain.FGSA.admitVote_stamps
#print axioms AvailableChain.FGSA.foldVotes_stamps
#print axioms AvailableChain.FGSA.writeKeys_stamps
#print axioms AvailableChain.FGSA.saGate_stamps
#print axioms AvailableChain.FGSA.gateStep_stamps
#print axioms AvailableChain.FGSA.clockPre_stamps
#print axioms AvailableChain.FGSA.clock_cumulative
#print axioms AvailableChain.FGSA.accepted_st2
#print axioms AvailableChain.FGSA.admitProposal_prefix
#print axioms AvailableChain.FGSA.process_cumulative
#print axioms AvailableChain.FGSA.metaInv_init
#print axioms AvailableChain.FGSA.block?_proposal
#print axioms AvailableChain.FGSA.metaInv_admitRow
#print axioms AvailableChain.FGSA.metaInv_foldl_admitRow
#print axioms AvailableChain.FGSA.wire_block_mem
#print axioms AvailableChain.FGSA.accepted_rows_decode
#print axioms AvailableChain.FGSA.metaInv_accepted
#print axioms AvailableChain.FGSA.metaInv_process
#print axioms AvailableChain.FGSA.metaInv_clock
#print axioms AvailableChain.FGSA.metadataInvariant
#print axioms AvailableChain.FGSA.stored_wire_of_block

-- Proofs/CrossNode.lean
#print axioms AvailableChain.FGSA.contentAgree_symm
#print axioms AvailableChain.FGSA.contentAgree_self
#print axioms AvailableChain.FGSA.contentAgree
#print axioms AvailableChain.FGSA.contentAgree
#print axioms AvailableChain.FGSA.contentAgree_self
#print axioms AvailableChain.FGSA.eraseFG_ancestor_preceq
#print axioms AvailableChain.FGSA.fg_eq_of_eraseFG_eq_across
#print axioms AvailableChain.FGSA.fg_eq_of_root_eq_across
#print axioms AvailableChain.FGSA.preceq_iff_across
#print axioms AvailableChain.FGSA.compatible_iff_across
#print axioms AvailableChain.FGSA.rootInjectiveOn_across

-- Proofs/Head.lean (T7.W)
#print axioms AvailableChain.FGSA.erasedList_subset
#print axioms AvailableChain.FGSA.liveRoot_stored
#print axioms AvailableChain.FGSA.headInTree_stored
#print axioms AvailableChain.FGSA.getHead_stored
#print axioms AvailableChain.FGSA.headVote_zero
#print axioms AvailableChain.FGSA.headVote_stored
#print axioms AvailableChain.FGSA.liveRoot_preceq_headInTree
#print axioms AvailableChain.FGSA.F_preceq_liveRoot
#print axioms AvailableChain.FGSA.F_preceq_headInTree
#print axioms AvailableChain.FGSA.preceq_getHead_of_preceq_F
#print axioms AvailableChain.FGSA.preceq_fgHead_of_preceq_F
#print axioms AvailableChain.FGSA.preceq_headVote_of_preceq_F

-- AvailableChainKitFG/Certificates.lean (ChainStateFoldOrder; I14)
#print axioms AvailableChain.KitFG.insertIf_comm
#print axioms AvailableChain.KitFG.insertIf_idem
#print axioms AvailableChain.KitFG.process_row_eq
#print axioms AvailableChain.KitFG.process_row_comm
#print axioms AvailableChain.KitFG.process_row_idem
#print axioms AvailableChain.KitFG.foldl_process_row_push
#print axioms AvailableChain.KitFG.foldl_process_row_absorb
#print axioms AvailableChain.KitFG.foldl_process_row_dedup
#print axioms AvailableChain.KitFG.foldl_process_row_perm
#print axioms AvailableChain.KitFG.transition_perm
#print axioms AvailableChain.KitFG.transition_eq_of_mem_iff
#print axioms AvailableChain.KitFG.transition_eq_of_toFinset

-- T7.9 part A
#print axioms AvailableChain.FGSA.StoreSetEq
#print axioms AvailableChain.FGSA.admitRow_setEq
#print axioms AvailableChain.FGSA.proposalRows_perm_setEq
#print axioms AvailableChain.FGSA.propose_setEq -- ROOT-DIGEST-2 W1 C1: Option relation
#print axioms AvailableChain.GridCO.writeKeys_def
#print axioms AvailableChain.GridCO.gateWriteKeys_def

-- GridCO StoreFacts used by FGSA.
#print axioms AvailableChain.GridCO.ghostStep_child
#print axioms AvailableChain.GridCO.ghostWalk_mem
#print axioms AvailableChain.GridCO.confirmationFrom_mem
#print axioms AvailableChain.GridCO.gateFrom_target_origin
#print axioms AvailableChain.GridCO.gateFrom_eq_writeKeys
#print axioms AvailableChain.GridCO.admitVote_blocks
#print axioms AvailableChain.GridCO.admitVote_obligations
#print axioms AvailableChain.GridCO.gateFrom_blocks
#print axioms AvailableChain.GridCO.admitVote_stable
#print axioms AvailableChain.GridCO.genesis_prefix

-- Cross-store forms without a content-agreement premise.
#print axioms AvailableChain.FGSA.stored_fg_eq_of_erase_eq
#print axioms AvailableChain.FGSA.stored_fg_preceq_iff_erase
#print axioms AvailableChain.FGSA.stored_fg_compatible_eq_erase
#print axioms AvailableChain.FGSA.stored_fg_roots_injective

-- Proofs/LeaseOutput.lean
#print axioms AvailableChain.FGSA.storedTargetsBelowOutput_target
#print axioms AvailableChain.FGSA.admitProposal_obligations_slow
#print axioms AvailableChain.FGSA.gateFrom_target_origin_slow

#print axioms AvailableChain.FGSA.fgsa_early_subset_late
#print axioms AvailableChain.FGSA.fgsa_cleanSupport_no_equivocation
#print axioms AvailableChain.FGSA.fgsa_cleanSupport_seats_subset_late
#print axioms AvailableChain.FGSA.fgsa_prefixSupport_antitone
#print axioms AvailableChain.FGSA.fgsa_conflicting_support_sum_le_late
#print axioms AvailableChain.FGSA.fgsa_confirmationFrom_covers_majority

#print axioms AvailableChain.FGSA.fgsa_headVote_covers_of_transfer

#print axioms AvailableChain.FGSA.fgsa_getHead_covers_of_dominated_suffix

#print axioms AvailableChain.FGSA.fgsa_getHead_exact_of_dominated_suffix

#print axioms AvailableChain.FGSA.fgsa_getHead_reanchor_of_dominated_suffix

#print axioms AvailableChain.FGSA.fgsa_getHead_avoids_unsupported_child


#print axioms AvailableChain.FGSA.fgsa_confirmationFrom_exact_of_dominated_suffix

#print axioms AvailableChain.FGSA.fgsa_headInTree_covers_of_transfer

#print axioms AvailableChain.FGSA.fgsa_score_eq_on_retained_suffix

#print axioms AvailableChain.FGSA.fgsa_filtered_anchorClosed
#print axioms AvailableChain.FGSA.fgsa_headInTree_noEligibleChild
#print axioms AvailableChain.FGSA.fgsa_headInTree_mem_or_anchor

#print axioms AvailableChain.FGSA.fgsa_headInTree_reanchor_of_pivot

-- Migration 06: R6 acceptance and stored validity.
#print axioms AvailableChain.FGSA.blockAccepted_rowsValid
#print axioms AvailableChain.FGSA.admitBlock_invalid_rows
#print axioms AvailableChain.FGSA.fgBlockOf_mono
#print axioms AvailableChain.FGSA.rowsValidStored_admitBlock
#print axioms AvailableChain.FGSA.rowsValidStored_process
#print axioms AvailableChain.FGSA.rowsValidStored_clock
#print axioms AvailableChain.FGSA.rowsValidStored_reachable
#print axioms AvailableChain.FGSA.proposalRows_eq_proposalRowsFor

-- Proofs/WindowHeightBridge.lean
#print axioms AvailableChain.FGSA.Window.heightRefinement
#print axioms AvailableChain.FGSA.Window.windowHeightBridge
#print axioms AvailableChain.FGSA.Window.windowHeightLaws

-- Proofs/WindowInvariant.lean
#print axioms AvailableChain.FGSA.Window.window_ordered
#print axioms AvailableChain.FGSA.Window.window_bounds
#print axioms AvailableChain.FGSA.Window.window_capacity
#print axioms AvailableChain.FGSA.Window.window_post_not_ready
#print axioms AvailableChain.FGSA.Window.window_F_preceq_J
#print axioms AvailableChain.FGSA.Window.window_hF_le_hj
#print axioms AvailableChain.FGSA.Window.window_finalized_zero
#print axioms AvailableChain.FGSA.Window.window_hF_mono
#print axioms AvailableChain.FGSA.Window.window_F_mono
#print axioms AvailableChain.FGSA.Window.window_bit_retained
#print axioms AvailableChain.FGSA.Window.window_no_reentry
#print axioms AvailableChain.FGSA.Window.window_finality_of_cover

-- Proofs/WindowCertificates.lean
#print axioms AvailableChain.FGSA.Window.justificationBirth_window_iff_simplex
#print axioms AvailableChain.FGSA.Window.window_entry_origin
#print axioms AvailableChain.FGSA.Window.window_prefinal_entry_origin

-- Proofs/WindowStore.lean
#print axioms AvailableChain.FGSA.Window.acceptViable_eq
#print axioms AvailableChain.FGSA.Window.update_finality_h_max_eq
#print axioms AvailableChain.FGSA.Window.update_finality_J_eq
#print axioms AvailableChain.FGSA.Window.update_finality_h_j_eq
#print axioms AvailableChain.FGSA.Window.on_block_TF_eq
#print axioms AvailableChain.FGSA.Window.windowStoreInvariant_init
#print axioms AvailableChain.FGSA.Window.windowStoreInvariant_accept
#print axioms AvailableChain.FGSA.Window.window_on_block_of_refused
#print axioms AvailableChain.FGSA.Window.window_on_block_of_accepted
#print axioms AvailableChain.FGSA.Window.window_on_block_F_mono
#print axioms AvailableChain.FGSA.Window.windowStoreInvariant_on_block
#print axioms AvailableChain.FGSA.Window.window_on_block_TF_subset

-- Proofs/WindowProvenance.lean
#print axioms AvailableChain.FGSA.Window.window_provenance_entry
#print axioms AvailableChain.FGSA.Window.window_provenance_finalityRow
#print axioms AvailableChain.FGSA.Window.window_provenance_finalityQC
#print axioms AvailableChain.FGSA.Window.window_exists_crossing_quorum_ne_justified
#print axioms AvailableChain.FGSA.Window.window_exists_honest_timeout_of_crossing
#print axioms AvailableChain.FGSA.Window.window_headFields_latest

-- Proofs/WindowHistory.lean
#print axioms AvailableChain.FGSA.Window.window_final_birth
#print axioms AvailableChain.FGSA.Window.window_le_hF_covered
#print axioms AvailableChain.FGSA.Window.window_absent_le_hF_covered
#print axioms AvailableChain.FGSA.Window.window_evicted_above_hF
#print axioms AvailableChain.FGSA.Window.window_retained_bits_mono
#print axioms AvailableChain.FGSA.Window.window_latest_pair_kept
#print axioms AvailableChain.FGSA.Window.window_evicted_has_K_newer
#print axioms AvailableChain.FGSA.Window.window_entry_history

-- Proofs/WindowLiveness.lean
#print axioms AvailableChain.FGSA.Window.window_bit_add_of_row
#print axioms AvailableChain.FGSA.Window.window_bits_accumulate
#print axioms AvailableChain.FGSA.Window.window_finalize_of_accumulated_quorum
#print axioms AvailableChain.FGSA.Window.window_target_appended_newest
#print axioms AvailableChain.FGSA.Window.window_retained_of_few_newer
#print axioms AvailableChain.FGSA.Window.window_retained_along

-- Proofs/WindowRetention.lean
#print axioms AvailableChain.FGSA.Window.window_hj_mono
#print axioms AvailableChain.FGSA.Window.window_retained_of_scalar
#print axioms AvailableChain.FGSA.Window.window_retained_or_covered
#print axioms AvailableChain.FGSA.Window.window_exact_row_no_missing_effect
#print axioms AvailableChain.FGSA.Window.window_retained_of_few_births
#print axioms AvailableChain.FGSA.Window.window_retained_fresh_one_newer
#print axioms AvailableChain.FGSA.Window.RetainedW_def
#print axioms AvailableChain.FGSA.Window.CoveredW_def

-- Proofs/WindowSelection.lean
#print axioms AvailableChain.FGSA.Window.windowSelectionLaws
#print axioms AvailableChain.FGSA.Window.windowCertificateLaws
#print axioms AvailableChain.FGSA.Window.windowChainCertificate

#print axioms AvailableChain.FGSA.Window.projectHeight_def
#print axioms AvailableChain.FGSA.Window.parentState_def
#print axioms AvailableChain.FGSA.Window.headFields_def
#print axioms AvailableChain.FGSA.heightView_def
#print axioms AvailableChain.FGSA.fgsa_controls_eq_of_top_retained
#print axioms AvailableChain.FGSA.fgsa_fullTree_eq_of_top_retained
#print axioms AvailableChain.FGSA.fgsa_eligible_eq
#print axioms AvailableChain.FGSA.fgsa_headVote_eq_of_top_retained
#print axioms AvailableChain.FGSA.Window.window_hOf_eq
#print axioms AvailableChain.FGSA.Window.window_frontier_eq
#print axioms AvailableChain.FGSA.Window.window_lexMax_eq
#print axioms AvailableChain.FGSA.Window.window_filteredFrom_eq
#print axioms AvailableChain.FGSA.Window.window_storeControls_eq
#print axioms AvailableChain.FGSA.Window.window_storeFrame_eq
#print axioms AvailableChain.FGSA.Window.window_fjControls_eq
#print axioms AvailableChain.FGSA.Window.window_fjFrame_eq
#print axioms AvailableChain.FGSA.Window.headFields_eq_certificateHeadFields
#print axioms AvailableChain.FGSA.Window.rowValidW_iff
#print axioms AvailableChain.FGSA.Window.rowValidW_decodes
#print axioms AvailableChain.FGSA.Window.rowValidW_slot_irrel
#print axioms AvailableChain.FGSA.Window.rowValidW_fold
#print axioms AvailableChain.FGSA.Window.heightMatch_progress_first
#print axioms AvailableChain.FGSA.Window.window_update_finality_TF
#print axioms AvailableChain.FGSA.Window.window_update_finality_h_max
#print axioms AvailableChain.FGSA.Window.window_update_finality_pair
#print axioms AvailableChain.FGSA.Window.window_update_finality_F_cases

#print axioms AvailableChain.FGSA.heightView_bridge
#print axioms AvailableChain.FGSA.heightView_eq_simplex
#print axioms AvailableChain.FGSA.finalityView_def
#print axioms AvailableChain.FGSA.fgCertificateLaws
#print axioms AvailableChain.FGSA.fgJustificationLaws
#print axioms AvailableChain.FGSA.fgStoreSafety
#print axioms AvailableChain.FGSA.fgInputs_headFields
#print axioms AvailableChain.FGSA.emitted_finality_pair_of_headFields
#print axioms AvailableChain.FGSA.Window.windowStoreSafety

#print axioms AvailableChain.FGSA.fgsa_Z_preceq_liveRoot
#print axioms AvailableChain.FGSA.attest_source_heightView

-- S4.2b: entry history, terminal retention, and checked admission transfer.
#print axioms AvailableChain.FGSA.Window.EntryBitW
#print axioms AvailableChain.FGSA.Window.EntryBitW_def
#print axioms AvailableChain.FGSA.Window.entry_bit_insertW
#print axioms AvailableChain.FGSA.Window.entry_bit_persistW
#print axioms AvailableChain.FGSA.Window.entry_bit_occurrenceW
#print axioms AvailableChain.FGSA.Window.entry_historyW
#print axioms AvailableChain.FGSA.Window.terminal_retained_scalarW
#print axioms AvailableChain.FGSA.Window.terminal_retained_birthsW
#print axioms AvailableChain.FGSA.Window.terminal_retained_or_coveredW
#print axioms AvailableChain.FGSA.stored_r6wW
#print axioms AvailableChain.FGSA.stored_chain_r6wW
#print axioms AvailableChain.FGSA.Window.terminalRetentionW

-- ROOT-DIGEST: public root and content declarations.
#print axioms AvailableChain.FGSA.baseBlocks_rootInj
#print axioms AvailableChain.FGSA.blockAccepted_contentOk
#print axioms AvailableChain.FGSA.contentOk
#print axioms AvailableChain.FGSA.contentOk_proposalBlock
#print axioms AvailableChain.FGSA.contentOk_rowsOk
#print axioms AvailableChain.FGSA.eraseFG_preceq_iff
#print axioms AvailableChain.FGSA.erasedList_rootInj
#print axioms AvailableChain.FGSA.proposalBlock
#print axioms AvailableChain.FGSA.proposalInput

-- ROOT-DIGEST-2: new public W1 declarations from the signed checkpoint inventory.
namespace AvailableChain.Block
#print axioms findByRoot?
#print axioms findByRoot?_mem
#print axioms findByRoot?_of_unique
#print axioms findByRoot?_perm
#print axioms findByRoot?_root
#print axioms findByRoot?_spec
#print axioms findByRoot?_unique
end AvailableChain.Block

namespace AvailableChain.FGSA
#print axioms NamedProposal
#print axioms actView_resolutionTree
#print axioms actView_resolvedHead
#print axioms active_releaseCount_le
#print axioms active_releaseCount_zero
#print axioms active_resolvedBefore_base
#print axioms admitProposal_headDomain
#print axioms admitRow_headDomain
#print axioms admitVote_headDomain
#print axioms base_headDomain_none
#print axioms clock_headDomain
#print axioms clock_namedBodies
#print axioms contentAgree_projection
#print axioms foldRows_headDomain
#print axioms foldVotes_headDomain
#print axioms instDecidableEqNamedProposal
#print axioms instReprNamedProposal
#print axioms mem_namedBodies
#print axioms namedBodies_erase_domain
#print axioms namedBodies_erase_injective
#print axioms namedBodies_parent
#print axioms namedBodies_root_injective
#print axioms namedByErase?
#print axioms namedByErase?_complete
#print axioms namedByErase?_sound
#print axioms namedByErase?_stored
#print axioms namedContentOk
#print axioms namedParentHeld
#print axioms namedProposal
#print axioms namedProposal_erase
#print axioms named_erase_ancestor
#print axioms named_erase_eq_genesis
#print axioms named_erase_parent
#print axioms named_erase_root
#print axioms named_erase_slot
#print axioms named_preceq_erase
#print axioms named_preceq_refl
#print axioms named_preceq_trans
#print axioms process_headDomain
#print axioms proposal?_eq_some
#print axioms propose_isSome_of_reachable
#print axioms propose_parent_lookup
#print axioms reachable_named_store
#print axioms resolvedHead_mem
end AvailableChain.FGSA

namespace AvailableChain.FGSA.NamedProposal
#print axioms Preceq
#print axioms body
#print axioms digestInput
#print axioms erase
#print axioms genesis
#print axioms node
#print axioms parent
#print axioms preceq
#print axioms raw
#print axioms root
#print axioms rows
#print axioms slot
#print axioms support
end AvailableChain.FGSA.NamedProposal

namespace AvailableChain.FGSA.State
#print axioms namedBodies
end AvailableChain.FGSA.State

namespace AvailableChain.FGSA.Wire
#print axioms proposal?
end AvailableChain.FGSA.Wire

namespace AvailableChain.FGSA.instDecidableEqNamedProposal
#print axioms decEq
end AvailableChain.FGSA.instDecidableEqNamedProposal

namespace AvailableChain.FGSA.instReprNamedProposal
#print axioms repr
end AvailableChain.FGSA.instReprNamedProposal

-- AvailableChainFGSA/Model/ContestFrame.lean
#print axioms AvailableChain.FGSA.Next.controls
#print axioms AvailableChain.FGSA.Next.controlsNext_def
#print axioms AvailableChain.FGSA.Next.fullTree
#print axioms AvailableChain.FGSA.Next.fullTreeNext_def

-- AvailableChainFGSA/Proofs/Port/ContestFrame.lean
#print axioms AvailableChain.FGSA.Next.controls_eq_of_top_extends_F
#print axioms AvailableChain.FGSA.Next.fullTree_eq_of_top_extends_F
#print axioms AvailableChain.FGSA.Next.controls_contest_imp
#print axioms AvailableChain.FGSA.Next.controls_contest_witness
#print axioms AvailableChain.FGSA.Next.controls_J_preceq_of_rootIsJ
#print axioms AvailableChain.FGSA.Next.contestFullTree_subset_tree

-- AvailableChainKitFG/TreeFrameDef.lean
#print axioms AvailableChain.KitFG.treeStoreControlsView
#print axioms AvailableChain.KitFG.treeStoreControlsView_def
#print axioms AvailableChain.KitFG.treeStoreFrameView
#print axioms AvailableChain.KitFG.treeStoreFrameView_def
#print axioms AvailableChain.KitFG.treeFjControlsView
#print axioms AvailableChain.KitFG.treeFjControlsView_def
#print axioms AvailableChain.KitFG.treeFjFrameView
#print axioms AvailableChain.KitFG.treeFjFrameView_def

-- AvailableChainKitFG/TreeFrameBridge.lean
#print axioms AvailableChain.KitFG.treeECView
#print axioms AvailableChain.KitFG.treeECView_def
#print axioms AvailableChain.KitFG.treeStoreControlsView_contest_iff
#print axioms AvailableChain.KitFG.treeFjControlsView_contest_iff
#print axioms AvailableChain.KitFG.treeStoreControlsView_contest_witness
#print axioms AvailableChain.KitFG.treeFjControlsView_contest_witness
#print axioms AvailableChain.KitFG.treeStoreControlsView_contest_imp
#print axioms AvailableChain.KitFG.treeFjControlsView_contest_imp
#print axioms AvailableChain.KitFG.treeStoreControlsView_eq
#print axioms AvailableChain.KitFG.treeStoreFrameView_eq
#print axioms AvailableChain.KitFG.treeFjControlsView_eq
#print axioms AvailableChain.KitFG.treeFjFrameView_eq
#print axioms AvailableChain.KitFG.treeStoreControlsView_eq_of_no_offF_top
#print axioms AvailableChain.KitFG.treeFjControlsView_eq_of_no_offF_top
#print axioms AvailableChain.KitFG.treeStoreControlsView_J_preceq_of_rootIsJ
#print axioms AvailableChain.KitFG.treeFjControlsView_J_preceq_of_rootIsJ
-- S0-C: pure pinned-spec representation.

-- AvailableChainFGSA.Model.Spec.ACState
#print axioms AvailableChain.FGSA.Spec.ACState
#print axioms AvailableChain.FGSA.Spec.liveEntries
#print axioms AvailableChain.FGSA.Spec.lockMap
#print axioms AvailableChain.FGSA.Spec.locked
#print axioms AvailableChain.FGSA.Spec.normalizeRecord
#print axioms AvailableChain.FGSA.Spec.LeaseRelation

-- AvailableChainFGSA.Model.Spec.Codec
#print axioms AvailableChain.FGSA.Spec.parentSlotValid
#print axioms AvailableChain.FGSA.Spec.proposerAllowed
#print axioms AvailableChain.FGSA.Spec.admissionValid
#print axioms AvailableChain.FGSA.Spec.deliveryWire
#print axioms AvailableChain.FGSA.Spec.checkedDelivery
#print axioms AvailableChain.FGSA.Spec.digestSpec
#print axioms AvailableChain.FGSA.Spec.validPayload
#print axioms AvailableChain.FGSA.Spec.wellFormed

-- AvailableChainFGSA.Model.Spec.Frame
#print axioms AvailableChain.FGSA.Spec.FGState
#print axioms AvailableChain.FGSA.Spec.fgStateOf
#print axioms AvailableChain.FGSA.Spec.Frame
#print axioms AvailableChain.FGSA.Spec.frameOf
#print axioms AvailableChain.FGSA.Spec.viableTree

-- AvailableChainFGSA.Model.Spec.Objects
#print axioms AvailableChain.FGSA.Spec.Block.identities
#print axioms AvailableChain.FGSA.Spec.Block.representation
#print axioms AvailableChain.FGSA.Spec.BlockCorresponds
#print axioms AvailableChain.FGSA.Spec.Block.Assigned
#print axioms AvailableChain.FGSA.Spec.Wire.identities
#print axioms AvailableChain.FGSA.Spec.Block
#print axioms AvailableChain.FGSA.Spec.Block.preceq
#print axioms AvailableChain.FGSA.Spec.Block.root
#print axioms AvailableChain.FGSA.Spec.Block.slot
#print axioms AvailableChain.FGSA.Spec.Block.parent
#print axioms AvailableChain.FGSA.Spec.Block.embed
#print axioms AvailableChain.FGSA.Spec.Block.toFG
#print axioms AvailableChain.FGSA.Spec.Msg
#print axioms AvailableChain.FGSA.Spec.Wire
#print axioms AvailableChain.FGSA.Spec.Wire.embed
#print axioms AvailableChain.FGSA.Spec.Input
#print axioms AvailableChain.FGSA.Spec.Wire.decode
#print axioms AvailableChain.FGSA.Spec.Input.embed

-- AvailableChainFGSA.Model.Spec.Transitions
#print axioms AvailableChain.FGSA.Spec.expire
#print axioms AvailableChain.FGSA.Spec.advance
#print axioms AvailableChain.FGSA.Spec.insertRow
#print axioms AvailableChain.FGSA.Spec.onBlock
#print axioms AvailableChain.FGSA.Spec.tick
#print axioms AvailableChain.FGSA.Spec.slotTime
#print axioms AvailableChain.FGSA.Spec.phaseTime

-- AvailableChainFGSA.Proofs.Spec.Clock
#print axioms AvailableChain.FGSA.Spec.revoke_vote_time
#print axioms AvailableChain.FGSA.Spec.confirmation_cutoff_time
#print axioms AvailableChain.FGSA.Spec.phaseTime_strict
#print axioms AvailableChain.FGSA.Spec.schedule_embedding
#print axioms AvailableChain.FGSA.Spec.actionTime_embedding
#print axioms AvailableChain.FGSA.Spec.tick_order

-- AvailableChainFGSA.Proofs.Spec.Codec
#print axioms AvailableChain.FGSA.Spec.blockCorresponds_unique
#print axioms AvailableChain.FGSA.Spec.assigned_embed_injective
#print axioms AvailableChain.FGSA.Spec.delivery_check_embedding
#print axioms AvailableChain.FGSA.Spec.checkedDelivery_embedding
#print axioms AvailableChain.FGSA.Spec.wire_rejection_effect
#print axioms AvailableChain.FGSA.Spec.admission_rejection_effect
#print axioms AvailableChain.FGSA.Spec.embed_root
#print axioms AvailableChain.FGSA.Spec.embed_slot
#print axioms AvailableChain.FGSA.Spec.embed_parent
#print axioms AvailableChain.FGSA.Spec.embed_injective
#print axioms AvailableChain.FGSA.Spec.embed_preceq
#print axioms AvailableChain.FGSA.Spec.carrier_embedding
#print axioms AvailableChain.FGSA.Spec.embed_root_order
#print axioms AvailableChain.FGSA.Spec.embed_lists
#print axioms AvailableChain.FGSA.Spec.digest_embedding
#print axioms AvailableChain.FGSA.Spec.content_check_embedding
#print axioms AvailableChain.FGSA.Spec.wire_embed_auth
#print axioms AvailableChain.FGSA.Spec.decode_embedding
#print axioms AvailableChain.FGSA.Spec.wire_embed_injective
#print axioms AvailableChain.FGSA.Spec.wellFormed_embedding
#print axioms AvailableChain.FGSA.Spec.refusal_embedding

-- AvailableChainFGSA.Proofs.Spec.Frame
#print axioms AvailableChain.FGSA.Spec.frame_tree
#print axioms AvailableChain.FGSA.Spec.mem_viableTree
#print axioms AvailableChain.FGSA.Spec.viableTree_eq_filter

-- AvailableChainFGSA.Proofs.Spec.Handlers
#print axioms AvailableChain.FGSA.Spec.process_parent_slot_refused
#print axioms AvailableChain.FGSA.Spec.process_proposer_refused
#print axioms AvailableChain.FGSA.Spec.advance_outside_embedding
#print axioms AvailableChain.FGSA.Spec.advance_absent_embedding
#print axioms AvailableChain.FGSA.Spec.process_decode_refused
#print axioms AvailableChain.FGSA.Spec.parent_membership
#print axioms AvailableChain.FGSA.Spec.admitRow_pool
#print axioms AvailableChain.FGSA.Spec.normalized_record
#print axioms AvailableChain.FGSA.Spec.advance_embedding
#print axioms AvailableChain.FGSA.Spec.onBlock_future
#print axioms AvailableChain.FGSA.Spec.onBlock_refused
#print axioms AvailableChain.FGSA.Spec.onBlock_accepted

-- AvailableChainFGSA.Proofs.Spec.Locks
#print axioms AvailableChain.FGSA.Spec.lt_lockMap_iff
#print axioms AvailableChain.FGSA.Spec.locked_iff_map
#print axioms AvailableChain.FGSA.Spec.liveEntries_expire
#print axioms AvailableChain.FGSA.Spec.expire_lease_projection
#print axioms AvailableChain.FGSA.Spec.lockMap_cleanup
#print axioms AvailableChain.FGSA.Spec.lease_locked_iff

-- AvailableChainFGSA/Model/VoteMerge.lean
#print axioms AvailableChain.FGSA.Next.proposalsAtNext
#print axioms AvailableChain.FGSA.Next.voterBlocksNext
#print axioms AvailableChain.FGSA.Next.headVotesNext
#print axioms AvailableChain.FGSA.Next.headSupportNext

-- AvailableChainFGSA/Model/FrameNext.lean
#print axioms AvailableChain.FGSA.Next.liveRootNext
#print axioms AvailableChain.FGSA.Next.eligibleNext
#print axioms AvailableChain.FGSA.Next.headInTreeNext
#print axioms AvailableChain.FGSA.Next.getHeadNext
#print axioms AvailableChain.FGSA.Next.headVoteNext
#print axioms AvailableChain.FGSA.Next.proposerVotesNext
#print axioms AvailableChain.FGSA.Next.chainWireRowsNext
#print axioms AvailableChain.FGSA.Next.blockWireRowsNext
#print axioms AvailableChain.FGSA.Next.proposalRowsNext
#print axioms AvailableChain.FGSA.Next.proposeNext
#print axioms AvailableChain.FGSA.Next.fgHeadNext
#print axioms AvailableChain.FGSA.Next.fgBlockOfNext
#print axioms AvailableChain.FGSA.Next.deepestNext
#print axioms AvailableChain.FGSA.Next.fgSourceNext
#print axioms AvailableChain.FGSA.Next.fgInputsNext
#print axioms AvailableChain.FGSA.Next.attestNext

-- AvailableChainFGSA/Model/Legacy/Frame.lean
#print axioms AvailableChain.FGSA.Legacy.controls
#print axioms AvailableChain.FGSA.Legacy.fullTree
#print axioms AvailableChain.FGSA.Legacy.erasedList
#print axioms AvailableChain.FGSA.Legacy.liveRoot
#print axioms AvailableChain.FGSA.Legacy.eligible
#print axioms AvailableChain.FGSA.Legacy.headInTree
#print axioms AvailableChain.FGSA.Legacy.getHead
#print axioms AvailableChain.FGSA.Legacy.proposalsAt
#print axioms AvailableChain.FGSA.Legacy.voterBlocks
#print axioms AvailableChain.FGSA.Legacy.headVotes
#print axioms AvailableChain.FGSA.Legacy.headSupport
#print axioms AvailableChain.FGSA.Legacy.headVote
#print axioms AvailableChain.FGSA.Legacy.proposerVotes
#print axioms AvailableChain.FGSA.Legacy.proposerSupport
#print axioms AvailableChain.FGSA.Legacy.chainWireRows
#print axioms AvailableChain.FGSA.Legacy.blockWireRows
#print axioms AvailableChain.FGSA.Legacy.proposalRows
#print axioms AvailableChain.FGSA.Legacy.propose
#print axioms AvailableChain.FGSA.Legacy.fgHead
#print axioms AvailableChain.FGSA.Legacy.fgBlockOf
#print axioms AvailableChain.FGSA.Legacy.deepest
#print axioms AvailableChain.FGSA.Legacy.fgSource
#print axioms AvailableChain.FGSA.Legacy.fgInputs
#print axioms AvailableChain.FGSA.Legacy.attest

-- AvailableChainFGSA/Proofs/Port/VoteMerge.lean
#print axioms AvailableChain.FGSA.Legacy.controls_eq
#print axioms AvailableChain.FGSA.Legacy.fullTree_eq
#print axioms AvailableChain.FGSA.Legacy.erasedList_eq
#print axioms AvailableChain.FGSA.Legacy.liveRoot_eq
#print axioms AvailableChain.FGSA.Legacy.legacy_eligible_eq
#print axioms AvailableChain.FGSA.Legacy.headInTree_eq
#print axioms AvailableChain.FGSA.Legacy.getHead_eq
#print axioms AvailableChain.FGSA.Legacy.proposalsAt_eq
#print axioms AvailableChain.FGSA.Legacy.voterBlocks_eq
#print axioms AvailableChain.FGSA.Legacy.headVotes_eq
#print axioms AvailableChain.FGSA.Legacy.headSupport_eq
#print axioms AvailableChain.FGSA.Legacy.headVote_eq
#print axioms AvailableChain.FGSA.Legacy.proposerVotes_eq
#print axioms AvailableChain.FGSA.Legacy.proposerSupport_eq
#print axioms AvailableChain.FGSA.Legacy.chainWireRows_eq
#print axioms AvailableChain.FGSA.Legacy.blockWireRows_eq
#print axioms AvailableChain.FGSA.Legacy.proposalRows_eq
#print axioms AvailableChain.FGSA.Legacy.propose_eq
#print axioms AvailableChain.FGSA.Legacy.fgHead_eq
#print axioms AvailableChain.FGSA.Legacy.fgBlockOf_eq
#print axioms AvailableChain.FGSA.Legacy.deepest_eq
#print axioms AvailableChain.FGSA.Legacy.fgSource_eq
#print axioms AvailableChain.FGSA.Legacy.fgInputs_eq
#print axioms AvailableChain.FGSA.Legacy.attest_eq
#print axioms AvailableChain.FGSA.Next.proposalsAtNext_eq_of_retained
#print axioms AvailableChain.FGSA.Next.headVotesNext_eq_of_proposals
#print axioms AvailableChain.FGSA.Next.voterBlocksNext_eq_of_tree
#print axioms AvailableChain.FGSA.Next.headSupportNext_eq_of_retained
#print axioms AvailableChain.FGSA.Next.tree_eq_of_all_extends
#print axioms AvailableChain.FGSA.Next.fullTree_eq_of_controls
#print axioms AvailableChain.FGSA.Next.liveRootNext_eq_of_controls
#print axioms AvailableChain.FGSA.Next.eligibleNext_eq_of_controls
#print axioms AvailableChain.FGSA.Next.headInTreeNext_eq_of_controls
#print axioms AvailableChain.FGSA.Next.getHeadNext_eq_of_controls
#print axioms AvailableChain.FGSA.Next.headVoteNext_eq_of_reads

-- AvailableChainFGSA/Proofs/Port/Support.lean
#print axioms AvailableChain.FGSA.Next.port_proposerSupport_positive
#print axioms AvailableChain.FGSA.Next.port_scoreOn_resolved
#print axioms AvailableChain.FGSA.Next.port_support_filter_incidence
#print axioms AvailableChain.FGSA.Next.port_support_filter_score
#print axioms AvailableChain.FGSA.Next.port_headSupport_incidence
#print axioms AvailableChain.FGSA.Next.port_headSupport_scoreOn
#print axioms AvailableChain.FGSA.Next.port_headVotes_score
#print axioms AvailableChain.FGSA.Next.port_clean_score_card
#print axioms AvailableChain.FGSA.Next.port_clean_filter_score
#print axioms AvailableChain.FGSA.Next.port_ghostStep_congr
#print axioms AvailableChain.FGSA.Next.port_ghost_congr
#print axioms AvailableChain.FGSA.Next.port_confirmation_filter
#print axioms AvailableChain.FGSA.Next.port_selected_head_eq
#print axioms AvailableChain.FGSA.Next.port_proposer_selected_head
#print axioms AvailableChain.FGSA.Next.port_voter_selected_head
#print axioms AvailableChain.FGSA.Next.port_releaseCount_eq

-- AvailableChainFGSA/Proofs/Port/Carry.lean
#print axioms AvailableChain.FGSA.Next.port_retained_proposal_row
#print axioms AvailableChain.FGSA.Next.port_retained_raw_carry
#print axioms AvailableChain.FGSA.Next.port_retained_support_carry
#print axioms AvailableChain.FGSA.Next.port_retained_carry_score

-- AvailableChainFGSA/Proofs/Port/LocalReads.lean
#print axioms AvailableChain.FGSA.Next.port_resolvedHead_filter
#print axioms AvailableChain.FGSA.Next.port_resolvedBefore_filter
#print axioms AvailableChain.FGSA.Next.port_resolvedHead_above_F
#print axioms AvailableChain.FGSA.Next.port_resolvedHead_tree
#print axioms AvailableChain.FGSA.Next.port_resolvedBefore_tree
#print axioms AvailableChain.FGSA.Next.port_fastSet_projection
#print axioms AvailableChain.FGSA.Next.port_lease_projection
#print axioms AvailableChain.FGSA.Next.port_active_release_projection
#print axioms AvailableChain.FGSA.Next.port_fastSet_filter
#print axioms AvailableChain.FGSA.Next.port_fastWrite_projection

-- Guarded and canonical port helper audits.
#print axioms AvailableChain.FGSA.fgsa_controls_lo_le_store
#print axioms AvailableChain.FGSA.fgsa_fullTree_eq_filtered
#print axioms AvailableChain.FGSA.fgsa_headVote_eq_filtered
#print axioms AvailableChain.FGSA.fgsa_storeFrame_mem_above_liveRoot
#print axioms AvailableChain.FGSA.Next.port_controls_contest_imp_legacy
#print axioms AvailableChain.FGSA.Next.port_controls_eq_legacy_of_top_extends_F
#print axioms AvailableChain.FGSA.Next.port_fullTree_eq_legacy_of_top_extends_F
#print axioms AvailableChain.FGSA.Next.port_proposerSupport_eq_legacy_filter
#print axioms AvailableChain.FGSA.Next.port_proposerSupport_scoreOn_legacy
#print axioms AvailableChain.FGSA.Next.port_proposerSupport_score_legacy
#print axioms AvailableChain.FGSA.Next.port_proposerSupport_sublist_legacy
#print axioms AvailableChain.FGSA.Next.port_headSupport_incidence_legacy
#print axioms AvailableChain.FGSA.Next.port_headSupport_scoreOn_legacy
#print axioms AvailableChain.FGSA.Next.port_headVotes_score_legacy
#print axioms AvailableChain.FGSA.Next.port_proposer_selected_head_legacy
#print axioms AvailableChain.FGSA.Next.port_selected_head_eq_legacy
#print axioms AvailableChain.FGSA.Next.port_voter_selected_head_legacy
#print axioms AvailableChain.FGSA.Next.port_eligible_eq_legacy_of_controls
#print axioms AvailableChain.FGSA.Next.port_fullTree_eq_legacy_of_controls
#print axioms AvailableChain.FGSA.Next.port_getHead_eq_legacy_of_controls
#print axioms AvailableChain.FGSA.Next.port_headInTree_eq_legacy_of_controls
#print axioms AvailableChain.FGSA.Next.port_headSupport_eq_legacy_of_retained
#print axioms AvailableChain.FGSA.Next.port_headVote_eq_legacy_of_reads
#print axioms AvailableChain.FGSA.Next.port_headVotes_eq_legacy_of_proposals
#print axioms AvailableChain.FGSA.Next.port_liveRoot_eq_legacy_of_controls
#print axioms AvailableChain.FGSA.Next.port_proposalsAt_eq_legacy_of_retained
#print axioms AvailableChain.FGSA.Next.port_voterBlocks_eq_legacy_of_tree
#print axioms AvailableChain.FGSA.fgsa_fullTree_eq_treeFrame
#print axioms AvailableChain.FGSA.fgsa_storeControls_eq_tree

-- Sleep W2a: restart, join, suppressed gates and invariant induction.
#print axioms AvailableChain.FGSA.wipe_now
#print axioms AvailableChain.FGSA.wipe_restartTime
#print axioms AvailableChain.FGSA.wipe_fg
#print axioms AvailableChain.FGSA.wipe_proposals
#print axioms AvailableChain.FGSA.wipe_rowPool
#print axioms AvailableChain.FGSA.wipe_blocks
#print axioms AvailableChain.FGSA.wipe_obligations
#print axioms AvailableChain.FGSA.wipe_stableRecord
#print axioms AvailableChain.FGSA.wipe_fastWrite
#print axioms AvailableChain.FGSA.wipe_blockStamp
#print axioms AvailableChain.FGSA.restartVotes_eq
#print axioms AvailableChain.FGSA.acRestart_now
#print axioms AvailableChain.FGSA.acRestart_restartTime
#print axioms AvailableChain.FGSA.acRestart_fg
#print axioms AvailableChain.FGSA.acRestart_proposals
#print axioms AvailableChain.FGSA.acRestart_rowPool
#print axioms AvailableChain.FGSA.acRestart_blocks
#print axioms AvailableChain.FGSA.acRestart_obligations
#print axioms AvailableChain.FGSA.acRestart_stableRecord
#print axioms AvailableChain.FGSA.acRestart_blockStamp
#print axioms AvailableChain.FGSA.acRestart_fastWrite
#print axioms AvailableChain.FGSA.acRestart_genuine
#print axioms AvailableChain.FGSA.acRestart_voteStamp_keys
#print axioms AvailableChain.FGSA.acRestart_votes_nodup
#print axioms AvailableChain.FGSA.acRestart_voteStamp_nodup
#print axioms AvailableChain.FGSA.acRestart_two_per_seat
#print axioms AvailableChain.FGSA.acRestart_replay_stamp
#print axioms AvailableChain.FGSA.restartSources_eq
#print axioms AvailableChain.FGSA.restartSources_parent_order
#print axioms AvailableChain.FGSA.reachable_acRestart
#print axioms AvailableChain.FGSA.joinedNow_none
#print axioms AvailableChain.FGSA.joinedNow_iff
#print axioms AvailableChain.FGSA.joinedNow_slot_zero
#print axioms AvailableChain.FGSA.clockPre_joined
#print axioms AvailableChain.FGSA.clockPre_obligations_unjoined
#print axioms AvailableChain.FGSA.cstoreInv_wipe
#print axioms AvailableChain.FGSA.cstoreInv_gateUnjoined
#print axioms AvailableChain.FGSA.metaInv_wipe
#print axioms AvailableChain.FGSA.storedTargetsBelowOutput_wipe
#print axioms AvailableChain.FGSA.normalizeS_eq_of_nestOK
#print axioms AvailableChain.FGSA.gateStep_unjoined
#print axioms AvailableChain.FGSA.gateStep_unjoined_eq
#print axioms AvailableChain.FGSA.gateStep_other
#print axioms AvailableChain.FGSA.gateStep_fresh_cases
#print axioms AvailableChain.FGSA.storeBundleInvariant
#print axioms AvailableChain.FGSA.base_headDomain_none
#print axioms AvailableChain.FGSA.acRestart_replay_order
#print axioms AvailableChain.FGSA.acRestart_block_stamp
