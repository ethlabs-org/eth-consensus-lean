module
public import AvailableChainKitFG.WindowCertificates -- shake: keep (axioms)
public import AvailableChainKitFG.WindowSelection -- shake: keep (axioms)
public import AvailableChainKitFG.WindowStore -- shake: keep (axioms)
public import AvailableChainKitFG.WindowReaders -- shake: keep (axioms)
public import AvailableChainKitFG.WindowProvenance -- shake: keep (axioms)

public import AvailableChainKitFG.WindowHeightBridge -- shake: keep (axioms)
public import AvailableChainKitFG.WindowSteps -- shake: keep (axioms)
public import AvailableChainKitFG.WindowInvariant -- shake: keep (axioms)
public import AvailableChainKitFG.TreeCorrespondence -- shake: keep (axioms)
public import AvailableChainKitFG.TreeFrameGeometry -- shake: keep (axioms)
public import AvailableChainKitFG.TreeTwoChanges -- shake: keep (axioms)
public import AvailableChainKitFG.TreeFrameBridge -- shake: keep (axioms)
public import AvailableChainKitFG.FrameChannels -- shake: keep (axioms)
public import AvailableChainKitFG.Accountable -- shake: keep (axioms)
public import AvailableChainKitFG.CrossingNoFinal -- shake: keep (axioms)
public import AvailableChainKitFG.Correspondence -- shake: keep (axioms)
public import AvailableChainKitFG.CausalCap -- shake: keep (axioms)
public import AvailableChainKitFG.ViewLockChains -- shake: keep (axioms)
public import AvailableChainKitFG.TwoChanges -- shake: keep (axioms)
public import AvailableChainKitFG.RowBits -- shake: keep (axioms)
public import AvailableChainKitFG.RecordHigh -- shake: keep (axioms)
public import AvailableChainKitFG.ClientOnceSafety -- shake: keep (axioms)
public import AvailableChainKitFG.RecordHighOnce -- shake: keep (axioms)
public import AvailableChainKitFG.FrameGeometry -- shake: keep (axioms)
public import AvailableChainKitFG.AccountableCore -- shake: keep (axioms)
public import AvailableChainKitFG.WindowTransport -- shake: keep (axioms)
public import AvailableChainKitFG.WindowEntriesDef -- shake: keep (axioms)
public import AvailableChainKitFG -- shake: keep (axioms)

/-! Kernel dependency audit for the FG chain lemmas without root premises. -/

#print axioms AvailableChain.KitFG.slashableWeight_or_justified_eq
#print axioms AvailableChain.KitFG.e1Weight_or_finalized_preceq
#print axioms AvailableChain.KitFG.slashableWeight_or_finalized_preceq
#print axioms AvailableChain.KitFG.e1Weight_or_finalized_compatible_of_le
#print axioms AvailableChain.KitFG.slashableWeight_or_finalized_compatible
#print axioms AvailableChain.KitFG.exists_crossing_quorum_ne_justified
#print axioms AvailableChain.KitFG.e1Weight_of_finalityQC_not_preceq
#print axioms AvailableChain.KitFG.slashableWeight_of_finalized_crossing
#print axioms AvailableChain.KitFG.exists_honest_timeout_of_crossing
#print axioms AvailableChain.KitFG.frame_facts
#print axioms AvailableChain.KitFG.causalCap_row
#print axioms AvailableChain.KitFG.causalCap_justified_row
#print axioms AvailableChain.KitFG.finalityCap_row
#print axioms AvailableChain.KitFG.finalityCap_height_row
#print axioms AvailableChain.KitFG.causalCap

#print axioms AvailableChain.KitFG.storeFrame_noContest_of_crossed
#print axioms AvailableChain.KitFG.storeFrame_contest_of_compatible
#print axioms AvailableChain.KitFG.storeFrame_height_of_crossed_prefix
#print axioms AvailableChain.KitFG.storeFrame_retention_of_compatible
#print axioms AvailableChain.KitFG.ViewLockOfChainsStatement_def
#print axioms AvailableChain.KitFG.ViewLockOfHonestChainsStatement_def
#print axioms AvailableChain.KitFG.viewLock_of_chains
#print axioms AvailableChain.KitFG.viewLock_of_honest_chains
#print axioms AvailableChain.KitFG.LowerFDomainIdentityStatement_def
#print axioms AvailableChain.KitFG.lowerF_domain_identity
#print axioms AvailableChain.KitFG.chainBits_def
#print axioms AvailableChain.KitFG.sameBitState_def
#print axioms AvailableChain.KitFG.rowMatchesBit_def
#print axioms AvailableChain.KitFG.BitPersistStatement_def
#print axioms AvailableChain.KitFG.BitFromRowStatement_def
#print axioms AvailableChain.KitFG.bit_fold_covered
#print axioms AvailableChain.KitFG.bit_persist
#print axioms AvailableChain.KitFG.bit_from_row
#print axioms AvailableChain.KitFG.HighRecord_def
#print axioms AvailableChain.KitFG.RecordHighStatement_def
#print axioms AvailableChain.KitFG.NoHighContestStatement_def
#print axioms AvailableChain.KitFG.recordHigh
#print axioms AvailableChain.KitFG.noHighContest

-- Send-once client: pure content, record safety, and restart laws.
#print axioms AvailableChain.KitFG.onceSignedContent_eq_iff
#print axioms AvailableChain.KitFG.onceKey_eq_iff_signedContent_eq
#print axioms AvailableChain.KitFG.record_row_without_finality
#print axioms AvailableChain.KitFG.record_row_optional_finality
#print axioms AvailableChain.KitFG.createRowOnce_released
#print axioms AvailableChain.KitFG.createRowOnce_none
#print axioms AvailableChain.KitFG.createRowOnce_safe
#print axioms AvailableChain.KitFG.createRowOnce_valid
#print axioms AvailableChain.KitFG.createRowOnce_sent
#print axioms AvailableChain.KitFG.createRowOnce_sameHeight
#print axioms AvailableChain.KitFG.clientRunOnce_covers
#print axioms AvailableChain.KitFG.clientRunOnce_noSlash
#print axioms AvailableChain.KitFG.clientRunOnce_fresh
#print axioms AvailableChain.KitFG.clientRunOnce_keys_nodup
#print axioms AvailableChain.KitFG.clientRecordOnce_sent
#print axioms AvailableChain.KitFG.clientRecordOnce_append
#print axioms AvailableChain.KitFG.clientRunOnce_append
#print axioms AvailableChain.KitFG.record_row_once_signer_irrel
#print axioms AvailableChain.KitFG.createRowOnce_signer_irrel
#print axioms AvailableChain.KitFG.clientRunOnce_signedContent_nodup
#print axioms AvailableChain.KitFG.recordInv_createRowOnce
#print axioms AvailableChain.KitFG.recordExtends_createRowOnce
#print axioms AvailableChain.KitFG.covers_createRowOnce
#print axioms AvailableChain.KitFG.createRowOnce_noSelfSlash
#print axioms AvailableChain.SimplexFG.createRowOnce_def

-- The send-once high guard reuses the old row-count argument.
#print axioms AvailableChain.KitFG.RecordHighOnceStatement_def
#print axioms AvailableChain.KitFG.recordHigh_optional_finality
#print axioms AvailableChain.KitFG.recordHighOnce

-- ROOT-DIGEST: public root and content declarations.
#print axioms AvailableChain.KitFG.RootInjectiveOn_def
#print axioms AvailableChain.KitFG.StoreStepRoots
#print axioms AvailableChain.KitFG.StoreStepRoots_def
#print axioms AvailableChain.KitFG.candidateJ_rootInj_of_viewRootInj
#print axioms AvailableChain.KitFG.e1Weight_or_finalized_preceq_of_parent_roots
#print axioms AvailableChain.KitFG.finalized_preceq_parent_of_certificate
#print axioms AvailableChain.KitFG.parent_preceq_parent
#print axioms AvailableChain.KitFG.preceq_parent_of_ne
#print axioms AvailableChain.KitFG.slashableWeight_or_finalized_compatible_of_parent_roots

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

-- AvailableChainKitFG/TreeCorrespondence.lean
#print axioms AvailableChain.KitFG.treePair_eq_of_lexKey_eq
#print axioms AvailableChain.KitFG.treeLexMax_eq_of_greatest
#print axioms AvailableChain.KitFG.treeLexMax_spec
#print axioms AvailableChain.KitFG.treeLexMax_of_none
#print axioms AvailableChain.KitFG.treeTop_extends_J

-- AvailableChainKitFG/TreeFrameGeometry.lean
#print axioms AvailableChain.KitFG.treeStore_contest_persist
#print axioms AvailableChain.KitFG.treeStore_contest_persist_of_inv

-- AvailableChainKitFG/TreeTwoChanges.lean
#print axioms AvailableChain.KitFG.treeLe_frontier
#print axioms AvailableChain.KitFG.treePhaseOf
#print axioms AvailableChain.KitFG.treeEJ
#print axioms AvailableChain.KitFG.treeEJ_def
#print axioms AvailableChain.KitFG.treeNFrame
#print axioms AvailableChain.KitFG.treePhaseOf_eq
#print axioms AvailableChain.KitFG.treeNFrame_eq
#print axioms AvailableChain.KitFG.treeFjControls_contest
#print axioms AvailableChain.KitFG.treeGap_of_ne
#print axioms AvailableChain.KitFG.treeTop_contest
#print axioms AvailableChain.KitFG.treeTop_uncontested
#print axioms AvailableChain.KitFG.treeTop_contested
#print axioms AvailableChain.KitFG.treeRootIsJ_iff
#print axioms AvailableChain.KitFG.treeOne_le_frontier
#print axioms AvailableChain.KitFG.treeLexMax_fst_lt
#print axioms AvailableChain.KitFG.treeLexMax_top_of_carrier
#print axioms AvailableChain.KitFG.treeLexMax_carrier_of_top
#print axioms AvailableChain.KitFG.treeECView_of_contest
#print axioms AvailableChain.KitFG.treeECView_mono_of_retained
#print axioms AvailableChain.KitFG.treeEvidence_mono
#print axioms AvailableChain.KitFG.treeEffFrame_of_bits
#print axioms AvailableChain.KitFG.treeNFrame_eq_phaseFrame
#print axioms AvailableChain.KitFG.treeTwoChanges
#print axioms AvailableChain.KitFG.treeTwoChanges_count
#print axioms AvailableChain.KitFG.treeTwoChanges_nested

-- P0b1 window transport and equation audit.
#print axioms AvailableChain.SimplexFG.Window.initial_def
#print axioms AvailableChain.SimplexFG.Window.process_row_def
#print axioms AvailableChain.SimplexFG.Window.advance_height_def
#print axioms AvailableChain.SimplexFG.Window.greatestReady_def
#print axioms AvailableChain.SimplexFG.Window.finalizeWindow_def
#print axioms AvailableChain.SimplexFG.Window.targetQuorum_def
#print axioms AvailableChain.SimplexFG.Window.progReady_def
#print axioms AvailableChain.SimplexFG.Window.process_height_events_def
#print axioms AvailableChain.SimplexFG.Window.transition_def
#print axioms AvailableChain.SimplexFG.Window.derive_def
#print axioms AvailableChain.SimplexFG.Window.heightMatch_def
#print axioms AvailableChain.SimplexFG.Window.windowMatch_def
#print axioms AvailableChain.SimplexFG.Window.staleUseful_def
#print axioms AvailableChain.SimplexFG.Window.r6w_def
#print axioms AvailableChain.SimplexFG.Window.latestQfin_def
#print axioms AvailableChain.SimplexFG.Window.acceptViable_def
#print axioms AvailableChain.SimplexFG.Window.update_finality_def
#print axioms AvailableChain.SimplexFG.Window.on_block_def
#print axioms AvailableChain.KitFG.Window.projectHeight_def
#print axioms AvailableChain.KitFG.Window.parentState_def
#print axioms AvailableChain.KitFG.Window.headFields_def
#print axioms AvailableChain.KitFG.Window.projectFinality_def
#print axioms AvailableChain.KitFG.Window.projectCertEntry_def
#print axioms AvailableChain.KitFG.Window.certificateHeight_def
#print axioms AvailableChain.KitFG.Window.certificateFinality_def
#print axioms AvailableChain.KitFG.Window.certificateFolded_def
#print axioms AvailableChain.KitFG.Window.certificateSelection_def
#print axioms AvailableChain.KitFG.Window.EntryOriginAt_def
#print axioms AvailableChain.KitFG.Window.heightView_def
#print axioms AvailableChain.KitFG.Window.finalityView_def
#print axioms AvailableChain.KitFG.Window.RetainedW_def
#print axioms AvailableChain.KitFG.Window.CoveredW_def
#print axioms AvailableChain.KitFG.Window.EntryBitW_def
#print axioms AvailableChain.KitFG.Window.window_addBit_def
#print axioms AvailableChain.KitFG.WindowFoldMap_def
#print axioms AvailableChain.KitFG.WindowFoldMap.fold_eq
#print axioms AvailableChain.KitFG.WindowFoldMap.view_eq
#print axioms AvailableChain.KitFG.WindowFoldMap.foldMap_height_eq
#print axioms AvailableChain.KitFG.WindowFoldMap.foldMap_finality_eq

#print axioms AvailableChain.KitFG.Window.heightRefinement
#print axioms AvailableChain.KitFG.Window.windowHeightBridge
#print axioms AvailableChain.KitFG.Window.windowHeightLaws
#print axioms AvailableChain.KitFG.Window.window_addBit_key
#print axioms AvailableChain.KitFG.Window.window_addBit_bits
#print axioms AvailableChain.KitFG.Window.window_row_fields
#print axioms AvailableChain.KitFG.Window.window_fold_fields
#print axioms AvailableChain.KitFG.Window.window_fold_entry
#print axioms AvailableChain.KitFG.Window.window_greatest_spec
#print axioms AvailableChain.KitFG.Window.window_strict_node
#print axioms AvailableChain.KitFG.Window.window_fold_sources
#print axioms AvailableChain.KitFG.Window.window_ordered
#print axioms AvailableChain.KitFG.Window.window_bounds
#print axioms AvailableChain.KitFG.Window.window_capacity
#print axioms AvailableChain.KitFG.Window.window_post_not_ready
#print axioms AvailableChain.KitFG.Window.window_F_preceq_J
#print axioms AvailableChain.KitFG.Window.window_hF_le_hj
#print axioms AvailableChain.KitFG.Window.window_finalized_zero
#print axioms AvailableChain.KitFG.Window.window_hF_mono
#print axioms AvailableChain.KitFG.Window.window_F_mono
#print axioms AvailableChain.KitFG.Window.window_bit_retained
#print axioms AvailableChain.KitFG.Window.window_no_reentry
#print axioms AvailableChain.KitFG.Window.window_finality_of_cover

#print axioms AvailableChain.KitFG.Window.justificationBirth_window_iff_simplex
#print axioms AvailableChain.KitFG.Window.window_entry_origin
#print axioms AvailableChain.KitFG.Window.window_prefinal_entry_origin
#print axioms AvailableChain.KitFG.Window.windowSelectionLaws
#print axioms AvailableChain.KitFG.Window.windowCertificateLaws
#print axioms AvailableChain.KitFG.Window.windowChainCertificate
#print axioms AvailableChain.KitFG.Window.acceptViable_eq
#print axioms AvailableChain.KitFG.Window.window_update_finality_TF
#print axioms AvailableChain.KitFG.Window.window_update_finality_h_max
#print axioms AvailableChain.KitFG.Window.window_update_finality_pair
#print axioms AvailableChain.KitFG.Window.window_update_finality_F_cases
#print axioms AvailableChain.KitFG.Window.update_finality_h_max_eq
#print axioms AvailableChain.KitFG.Window.update_finality_J_eq
#print axioms AvailableChain.KitFG.Window.update_finality_h_j_eq
#print axioms AvailableChain.KitFG.Window.on_block_TF_eq
#print axioms AvailableChain.KitFG.Window.windowStoreInvariant_init
#print axioms AvailableChain.KitFG.Window.windowStoreInvariant_accept
#print axioms AvailableChain.KitFG.Window.window_on_block_of_refused
#print axioms AvailableChain.KitFG.Window.window_on_block_of_accepted
#print axioms AvailableChain.KitFG.Window.window_on_block_F_mono
#print axioms AvailableChain.KitFG.Window.windowStoreInvariant_on_block
#print axioms AvailableChain.KitFG.Window.window_on_block_TF_subset
#print axioms AvailableChain.KitFG.Window.windowStoreSafety
#print axioms AvailableChain.KitFG.Window.window_hOf_eq
#print axioms AvailableChain.KitFG.Window.window_frontier_eq
#print axioms AvailableChain.KitFG.Window.window_lexMax_eq
#print axioms AvailableChain.KitFG.Window.window_filteredFrom_eq
#print axioms AvailableChain.KitFG.Window.window_storeControls_eq
#print axioms AvailableChain.KitFG.Window.window_storeFrame_eq
#print axioms AvailableChain.KitFG.Window.window_fjControls_eq
#print axioms AvailableChain.KitFG.Window.window_fjFrame_eq
#print axioms AvailableChain.KitFG.Window.headFields_eq_certificateHeadFields
#print axioms AvailableChain.KitFG.Window.window_provenance_entry
#print axioms AvailableChain.KitFG.Window.window_provenance_finalityRow
#print axioms AvailableChain.KitFG.Window.window_provenance_finalityQC
#print axioms AvailableChain.KitFG.Window.window_exists_crossing_quorum_ne_justified
#print axioms AvailableChain.KitFG.Window.window_exists_honest_timeout_of_crossing
#print axioms AvailableChain.KitFG.Window.window_headFields_latest
#print axioms AvailableChain.KitFG.Window.window_final_birth
#print axioms AvailableChain.KitFG.Window.window_le_hF_covered
#print axioms AvailableChain.KitFG.Window.window_absent_le_hF_covered
#print axioms AvailableChain.KitFG.Window.window_evicted_above_hF
#print axioms AvailableChain.KitFG.Window.window_retained_bits_mono
#print axioms AvailableChain.KitFG.Window.window_latest_pair_kept
#print axioms AvailableChain.KitFG.Window.window_evicted_has_K_newer
#print axioms AvailableChain.KitFG.Window.window_entry_history
#print axioms AvailableChain.KitFG.Window.window_bit_add_of_row
#print axioms AvailableChain.KitFG.Window.window_bits_accumulate
#print axioms AvailableChain.KitFG.Window.window_finalize_of_accumulated_quorum
#print axioms AvailableChain.KitFG.Window.window_target_appended_newest
#print axioms AvailableChain.KitFG.Window.window_retained_of_few_newer
#print axioms AvailableChain.KitFG.Window.window_retained_along
#print axioms AvailableChain.KitFG.Window.window_hj_mono
#print axioms AvailableChain.KitFG.Window.window_retained_of_scalar
#print axioms AvailableChain.KitFG.Window.window_retained_or_covered
#print axioms AvailableChain.KitFG.Window.window_exact_row_no_missing_effect
#print axioms AvailableChain.KitFG.Window.window_retained_of_few_births
#print axioms AvailableChain.KitFG.Window.window_retained_fresh_one_newer
#print axioms AvailableChain.KitFG.Window.entry_bit_insertW
#print axioms AvailableChain.KitFG.Window.entry_bit_persistW
#print axioms AvailableChain.KitFG.Window.entry_bit_occurrenceW
#print axioms AvailableChain.KitFG.Window.entry_historyW
#print axioms AvailableChain.KitFG.Window.terminal_retained_scalarW
#print axioms AvailableChain.KitFG.Window.terminal_retained_birthsW
#print axioms AvailableChain.KitFG.Window.terminal_retained_or_coveredW
#print axioms AvailableChain.KitFG.Window.terminalRetentionW
#print axioms AvailableChain.KitFG.Window.r6w_fold
#print axioms AvailableChain.KitFG.Window.heightMatch_progress_first
