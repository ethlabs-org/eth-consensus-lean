module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Candidates.EvidenceRelease
public import ConsensusLean.Instances.Goldilocks.Spec.WeightedLocks.LateCertificate

@[expose] public section

/-! # The late-certificate SA at a write mode

The late-certificate SA (`Spec/WeightedLocks/LateCertificate`, `certRecoverySA`) at a write mode
`m`, written once and uniformly in the mode: every handler is the late-certificate SA's, with
evidence-release's handler at the candidate's stage `certStageW` replaced by the same handler at
mode `m` (`Candidates/EvidenceRelease`: `acOnMessageEM`, `acOnBlockEM`, `acOnTickEM`,
`acRestartEM`). The archive, its receipts, the stage's context and the emissions' read points are
the late-certificate SA's. `ac_proposal` (`acProposalC`) and `ac_to_fg` (`acToFGC`) write nothing
and are the late-certificate SA's.

No definition tests whether the mode is the parent's; that the parent's mode gives the
late-certificate SA is a theorem (`Lemmas/Candidates/LateCertificate`). Definitions only. -/

namespace Consensus.Goldilocks.LateCertificate

open SA EvidenceRelease

variable {FGP : Type} (sp : SAParams) (m : WriteMode)

/-- `ac_on_message` at validator `self` at mode `m`: the receipt archives the vote, then
evidence-release's handler at mode `m` runs with the candidate's stage, reading the archive; the
emitted votes are archived. -/
noncomputable def acOnMessageCM (self : Fin sp.n) (X : CState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (v : Vote sp.n) : CState sp.n × List (EmC sp FGP) :=
  let arr := archiveRecord sp X.arch t v
  let r := acOnMessageEM sp (certStageW sp) (certCtx arr X.er.ac) m self X.er Φ t v
  (⟨r.1, archiveAll sp arr t (r.2.map Emission.msg)⟩, r.2.map (liftEm sp arr))

/-- `ac_on_block` at validator `self` at mode `m`: the receipt archives the block's payload votes,
then evidence-release's handler at mode `m` runs with the candidate's stage; the emitted votes are
archived. -/
noncomputable def acOnBlockCM (self : Fin sp.n) (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) : CState sp.n × List (EmC sp FGP) :=
  let arr := archiveAll sp X.arch t (blockVotes B)
  let r := acOnBlockEM sp (certStageW sp) (certCtx arr X.er.ac) m self X.er Φ t B
  (⟨r.1, archiveAll sp arr t (r.2.map Emission.msg)⟩, r.2.map (liftEm sp arr))

/-- `ac_on_tick` at validator `self` at mode `m`: evidence-release's at mode `m`, with the
candidate's stage; the emitted votes are archived. -/
noncomputable def acOnTickCM (self : Fin sp.n) (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    CState sp.n × List (EmC sp FGP) :=
  let r := acOnTickEM sp (certStageW sp) (certCtx X.arch X.er.ac) m self X.er Φ t
  (⟨r.1, archiveAll sp X.arch t (r.2.map Emission.msg)⟩, r.2.map (liftEm sp X.arch))

/-- `ac_restart` at validator `self` at mode `m`, replaying in the order `ro`: the archive is
dropped, evidence-release's restart at mode `m` replays with the candidate's stage (reading the
dropped archive and the restart at `t`), and the replayed blocks' payload votes and the emitted
votes are archived at `t`. -/
noncomputable def acRestartCM (ro : ReplayOrder sp FGP) (self : Fin sp.n) (X : CState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : CState sp.n × List (EmC sp FGP) :=
  let arr := (ro.order t Φ).foldl (fun a B => archiveAll sp a t (blockVotes B)) []
  let r := acRestartEM sp (certStageW sp) ⟨Archive.arrival [], (t : WithBot Time)⟩ m ro self X.er
    Φ t
  (⟨r.1, archiveAll sp arr t (r.2.map Emission.msg)⟩, r.2.map (liftEm sp arr))

/-- **The late-certificate SA at mode `m`**, with the restart replay order `ro`: the SA of
`certRecoverySA` with the handlers at mode `m`. -/
@[reducible] noncomputable def certRecoverySAM (FGP : Type) (ro : ReplayOrder sp FGP) :
    ACInterface sp.toParams FGP where
  State := CState sp.n
  Msg := Vote sp.n
  Payload := Payload sp.n
  validPayload := validPayload
  validMsg := fun _ => True
  holdsMsg := fun X v => v ∈ X.er.ac.pool v.slot ∨ v ∈ X.arch.map Prod.fst
  genesisPayload := ([], [])
  initial := CState.initial sp.genesisRoot
  onMessage := acOnMessageCM sp m
  onBlock := acOnBlockCM sp m
  onTick := acOnTickCM sp m
  proposal := acProposalC sp
  toFG := acToFGC sp
  confirmed := fun X => acConfirmed sp X.er.ac
  head := fun X => acHead sp X.er.ac
  restart := acRestartCM sp m ro

end Consensus.Goldilocks.LateCertificate

end
