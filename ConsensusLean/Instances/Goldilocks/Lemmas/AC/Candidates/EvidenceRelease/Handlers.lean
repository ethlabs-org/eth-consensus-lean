module
public import ConsensusLean.Instances.Goldilocks.Spec.WeightedLocks.Instance

public section

/-! # Evidence-release's handlers are the stage-generic ones at its stage

`Spec/WeightedLocks/Actions` writes the weighted handlers once over an unlock stage (`tryVoteE`,
`acOnMessageE`, `acOnBlockE`, `acOnTickE`, `acProposalE`, `acRestartE`, `unlockStateE`) and defines
evidence-release's as these at `evidenceStage` with no context. The characterising equations below
hold by `rfl` in both directions: each `W` handler unfolds to the generic one, and the generic one
at `(evidenceStage sp, ())` folds back to the `W` handler. -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable {sp : SAParams} {FGP : Type}

theorem unlockState_eq (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) (s : Int)
    (V : View sp.n) :
    unlockState sp X Φ t s V = unlockStateE sp (evidenceStage sp) () X Φ t s V := by
  rfl

theorem tryVoteW_eq (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    tryVoteW sp self X Φ t = tryVoteE sp (evidenceStage sp) () self X Φ t := by
  rfl

theorem acOnMessageW_eq (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (v : Vote sp.n) :
    acOnMessageW sp self X Φ t v = acOnMessageE sp (evidenceStage sp) () self X Φ t v := by
  rfl

theorem acOnBlockW_eq (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) :
    acOnBlockW sp self X Φ t B = acOnBlockE sp (evidenceStage sp) () self X Φ t B := by
  rfl

theorem acOnTickW_eq (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    acOnTickW sp self X Φ t = acOnTickE sp (evidenceStage sp) () self X Φ t := by
  rfl

theorem acProposalW_eq (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    acProposalW sp X Φ t = acProposalE sp (evidenceStage sp) () X Φ t := by
  rfl

theorem acRestartW_eq (ro : ReplayOrder sp FGP) (self : Fin sp.n) (X : WState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    acRestartW sp ro self X Φ t = acRestartE sp (evidenceStage sp) () ro self X Φ t := by
  rfl

/-- The generic unlock at evidence-release's stage, folded back. -/
theorem unlockStateE_evidenceStage (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) (s : Int)
    (V : View sp.n) :
    unlockStateE sp (evidenceStage sp) () X Φ t s V = unlockState sp X Φ t s V := by
  rfl

/-- The generic `try_vote` at evidence-release's stage, folded back. -/
theorem tryVoteE_evidenceStage (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : tryVoteE sp (evidenceStage sp) () self X Φ t = tryVoteW sp self X Φ t := by
  rfl

/-- The generic `ac_on_block` at evidence-release's stage, folded back. -/
theorem acOnBlockE_evidenceStage (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (B : Blk sp.n FGP) :
    acOnBlockE sp (evidenceStage sp) () self X Φ t B = acOnBlockW sp self X Φ t B := by
  rfl

end Consensus.Goldilocks.EvidenceRelease

end
