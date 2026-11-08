module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Candidates.LateCertificate
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.RelTrace
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.WeightedEm

@[expose] public section

/-! # Candidate runs, forgotten: the projections and the unlock oracles

The forgotten calls, labels and traces of the evidence-release and late-certificate SAs at a
write mode (`projCallM`, `projLabelM`, `projTraceM`; `projCallCM`, `projLabelCM`, `projTraceCM`),
the stage's call input, context and forgotten unlock (`callInputWM`, `ctxCM`, `unlockAtEM`), and
their unlock oracles (`erOracleM`, `certOracleM`), so that statements over a candidate's
forgotten run can name them. Definitions only; every theorem about them is in
`Lemmas/Candidates` (`localRunU_projTraceM`, `localRunU_projTraceCM`, …). -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable {sp : SAParams} {FGP : Type}

section Stage

variable {ro : ReplayOrder sp FGP} {σ : Type} (E : UnlockStage sp wlockStore σ) (c : σ)
  (m : WriteMode)

variable (sp) in
/-- The weighted state whose locks the unlock of the call reads (`callInput`). -/
noncomputable abbrev callInputWM (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (goldilocksSA sp FGP ro).Call → WState sp.n
  | .message v => optimisticConfirmationWM sp m { X with ac := admitVote sp X.ac t v } Φ t
  | .block B => optimisticConfirmationWM sp m { X with ac := blockReceipt sp X.ac t B } Φ t
  | _ => X

variable (sp) in
/-- The forgotten locks after the stage's unlock of the call's input. -/
noncomputable abbrev unlockAtEM (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (k : (goldilocksSA sp FGP ro).Call) : Set Lock :=
  WLock.lock '' wlockStore.unlockWith sp E c (callInputWM sp m X Φ t k).wlocks Φ t
    ((sp.slot t : Int) - 1) (callViewM sp m X.ac Φ t k)


end Stage

variable {ro : ReplayOrder sp FGP} {m : WriteMode}

variable (ro) in
/-- The parent's call of a call of the evidence-release SA at mode `m`. -/
abbrev projCallM : (evidenceReleaseSAM sp m FGP ro).Call → (goldilocksSA sp FGP ro).Call
  | .tick => .tick
  | .proposal => .proposal
  | .toFG => .toFG
  | .message m => .message m
  | .block B => .block B
  | .restart => .restart


/-- The parent's label of a label of the evidence-release SA at mode `m`. -/
abbrev projLabelM (ℓ : ACLabel (evidenceReleaseSAM sp m FGP ro)) :
    ACLabel (goldilocksSA sp FGP ro) :=
  ⟨projCallM ro ℓ.call, ℓ.frame, ℓ.emits.map projEm⟩

/-- **The forgotten trace**: the parent's states, calls and emissions of an AC trace of the
evidence-release SA at mode `m`. -/
abbrev projTraceM (tr : ACTrace (evidenceReleaseSAM sp m FGP ro)) : SATrace sp FGP ro where
  init y := (tr.init y).ac
  node := tr.node
  time := tr.time
  event := tr.event
  pos := tr.pos
  label i := (tr.label i).map projLabelM
  post i := (tr.post i).ac
  awake := tr.awake
  observationHorizon := tr.observationHorizon

/-- The unlock oracle of a trace of the evidence-release SA at mode `m`: at each labelled cut, the
forgotten locks after `unlockW` of the call's input. -/
noncomputable abbrev erOracleM (tr : ACTrace (evidenceReleaseSAM sp m FGP ro)) (i : Nat) :
    Set Lock :=
  match tr.label i with
  | some ℓ => unlockAtEM sp (evidenceStage sp) () m (tr.state (tr.node i) i) ℓ.frame (tr.time i)
      (projCallM ro ℓ.call)
  | none => ∅


end Consensus.Goldilocks.EvidenceRelease

namespace Consensus.Goldilocks.LateCertificate

open SA EvidenceRelease

variable {sp : SAParams} {FGP : Type}

variable {m : WriteMode} {ro : ReplayOrder sp FGP}

variable (ro) in
/-- The parent's call of a call of the late-certificate SA at mode `m`. -/
abbrev projCallCM : (certRecoverySAM sp m FGP ro).Call → (goldilocksSA sp FGP ro).Call
  | .tick => .tick
  | .proposal => .proposal
  | .toFG => .toFG
  | .message v => .message v
  | .block B => .block B
  | .restart => .restart

variable (ro) in
/-- The stage's context of a call: the archive after the call's receipt, and the last restart. -/
abbrev ctxCM (X : CState sp.n) (t : Time) : (certRecoverySAM sp m FGP ro).Call → CertCtx sp.n
  | .message v => certCtx (archiveRecord sp X.arch t v) X.er.ac
  | .block B => certCtx (archiveAll sp X.arch t (blockVotes B)) X.er.ac
  | .restart => ⟨Archive.arrival [], (t : WithBot Time)⟩
  | _ => certCtx X.arch X.er.ac


/-- The parent's label of a label of the late-certificate SA at mode `m`. -/
abbrev projLabelCM (ℓ : ACLabel (certRecoverySAM sp m FGP ro)) :
    ACLabel (goldilocksSA sp FGP ro) :=
  ⟨projCallCM ro ℓ.call, ℓ.frame, (ℓ.emits.map projC).map projEm⟩

/-- **The forgotten trace**: the parent's states, calls and emissions of an AC trace of the
late-certificate SA at mode `m`. -/
abbrev projTraceCM (tr : ACTrace (certRecoverySAM sp m FGP ro)) : SATrace sp FGP ro where
  init y := (tr.init y).er.ac
  node := tr.node
  time := tr.time
  event := tr.event
  pos := tr.pos
  label i := (tr.label i).map projLabelCM
  post i := (tr.post i).er.ac
  awake := tr.awake
  observationHorizon := tr.observationHorizon

/-- The unlock oracle of a trace of the late-certificate SA at mode `m`: at each labelled cut, the
forgotten locks after the candidate's unlock of the call's input at mode `m`, at the call's
context. -/
noncomputable abbrev certOracleM (tr : ACTrace (certRecoverySAM sp m FGP ro)) (i : Nat) :
    Set Lock :=
  match tr.label i with
  | some ℓ => unlockAtEM sp (certStageW sp)
      (ctxCM ro (tr.state (tr.node i) i) (tr.time i) ℓ.call) m (tr.state (tr.node i) i).er
      ℓ.frame (tr.time i) (projCallCM ro ℓ.call)
  | none => ∅


end Consensus.Goldilocks.LateCertificate

end
