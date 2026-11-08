module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Candidates.PreConfirmations.OneRelease
public import ConsensusLean.Instances.Goldilocks.Lemmas.Candidates.PreConfirmations.Provenance

@[expose] public section

/-! # ½ pre-confirmations: the proved statements, with their axioms pinned

One theorem per proved statement of `Candidates/PreConfirmations/Statements` and per law of the
one release, proved by the lemma of `Lemmas/Candidates/PreConfirmations`. Not proved here (not in
scope): `CoreStepAtCallStart`, `ProposalAtCallStart`, `CoreStepOfNoKeys`, `ParentStartIsCore`. -/

namespace Consensus.Goldilocks.PreConfirmations.Test

open SA EvidenceRelease PreConfirmations

theorem oneRel_lawful (sp : SAParams) : (oneReleaseStage sp).Lawful (oneReleaseKeep sp) :=
  oneReleaseStage_lawful sp

theorem oneRelease_fixes (sp : SAParams) : (oneReleaseStage sp).Fixes fun _ _ => True :=
  oneReleaseStage_fixes sp

theorem oneRelease_scan (sp : SAParams) (FGP : Type) : OneReleaseScan sp FGP := oneReleaseScan

theorem refresh_idem (sp : SAParams) (FGP : Type) : RefreshIdem sp FGP := refreshIdem

theorem auth_compat (sp : SAParams) (FGP : Type) : AuthorityCompatible sp FGP :=
  authorityCompatible

theorem authority_window (sp : SAParams) (FGP : Type) : AuthorityWindow sp FGP := authorityWindow

theorem pcProj_facts (sp : SAParams) (FGP : Type) : PCProjFacts sp FGP := pcProjFacts

theorem pcBase_facts (sp : SAParams) (FGP : Type) : PCBaseFacts sp FGP := pcBaseFacts

theorem pcAnchor_facts (sp : SAParams) (FGP : Type) : PCAnchorFacts sp FGP := pcAnchorFacts

theorem pcPath_sameState (sp : SAParams) (FGP : Type) : PCPathSameState sp FGP :=
  pcPathSameState

theorem ackSends_window (sp : SAParams) : AckSendsWindow sp := ackSendsWindow

theorem onAck_window (sp : SAParams) : OnAckWindow sp := onAckWindow

theorem record_window (sp : SAParams) : RecordWindow sp := recordWindow

theorem ackCall_coreId (sp : SAParams) (FGP : Type) {σ : Type} (E : UnlockStage sp wlockStore σ)
    (c : σ) (m : WriteMode) (ro : ReplayOrder sp FGP) : AckCallCoreId sp FGP E c m ro :=
  ackCallCoreId

theorem restart_resets (sp : SAParams) (FGP : Type) {σ : Type} (E : UnlockStage sp wlockStore σ)
    (c : σ) (m : WriteMode) (ro : ReplayOrder sp FGP) : RestartResets sp FGP E c m ro :=
  restartResets

theorem projState_core (sp : SAParams) (FGP : Type) {σ : Type} (E : UnlockStage sp wlockStore σ)
    (c : σ) (m : WriteMode) (ro : ReplayOrder sp FGP) : ProjStateCore sp FGP E c m ro :=
  projStateCore

theorem key_provenance (sp : SAParams) (FGP : Type) {σ : Type} (E : UnlockStage sp wlockStore σ)
    (c : σ) (m : WriteMode) (ro : ReplayOrder sp FGP) : KeyProvenance sp FGP E c m ro :=
  keyProvenance

end Consensus.Goldilocks.PreConfirmations.Test

-- `#guard_msgs in #print axioms` puts the command off column 0; the pinned messages are longer
-- than 100 columns.
set_option linter.style.whitespace false
set_option linter.style.longLine false

/-- info: 'Consensus.Goldilocks.PreConfirmations.Test.oneRel_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.PreConfirmations.Test.oneRel_lawful

/-- info: 'Consensus.Goldilocks.PreConfirmations.Test.oneRelease_fixes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.PreConfirmations.Test.oneRelease_fixes

/-- info: 'Consensus.Goldilocks.PreConfirmations.Test.oneRelease_scan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.PreConfirmations.Test.oneRelease_scan

/-- info: 'Consensus.Goldilocks.PreConfirmations.Test.refresh_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.PreConfirmations.Test.refresh_idem

/-- info: 'Consensus.Goldilocks.PreConfirmations.Test.auth_compat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.PreConfirmations.Test.auth_compat

/-- info: 'Consensus.Goldilocks.PreConfirmations.Test.authority_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.PreConfirmations.Test.authority_window

/-- info: 'Consensus.Goldilocks.PreConfirmations.Test.pcProj_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.PreConfirmations.Test.pcProj_facts

/-- info: 'Consensus.Goldilocks.PreConfirmations.Test.pcBase_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.PreConfirmations.Test.pcBase_facts

/-- info: 'Consensus.Goldilocks.PreConfirmations.Test.pcAnchor_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.PreConfirmations.Test.pcAnchor_facts

/-- info: 'Consensus.Goldilocks.PreConfirmations.Test.pcPath_sameState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.PreConfirmations.Test.pcPath_sameState

/-- info: 'Consensus.Goldilocks.PreConfirmations.Test.ackSends_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.PreConfirmations.Test.ackSends_window

/-- info: 'Consensus.Goldilocks.PreConfirmations.Test.onAck_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.PreConfirmations.Test.onAck_window

/-- info: 'Consensus.Goldilocks.PreConfirmations.Test.record_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.PreConfirmations.Test.record_window

/-- info: 'Consensus.Goldilocks.PreConfirmations.Test.ackCall_coreId' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.PreConfirmations.Test.ackCall_coreId

/-- info: 'Consensus.Goldilocks.PreConfirmations.Test.restart_resets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.PreConfirmations.Test.restart_resets

/-- info: 'Consensus.Goldilocks.PreConfirmations.Test.projState_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.PreConfirmations.Test.projState_core

/-- info: 'Consensus.Goldilocks.PreConfirmations.Test.key_provenance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.PreConfirmations.Test.key_provenance
