module
public import AvailableChainFGSAProofs.Proofs.Foundations.Sources
public import AvailableChainFGSAProofs.Proofs.Foundations.Store
public import AvailableChainFGSAClaims.Statements.ComposeStmt

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

set_option linter.unusedFintypeInType false in
/-- The retained Fintype instance is unused by the schedule-only source bound. -/
theorem fgsa_tSrc [Fintype V] {pt : Unit} (hb : BasePrem p c E rho pt) :
    TSrc p c E rho :=
  sourceDiscipline_tSrc p c E rho hb.set.valid.toScheduleWellFormed

set_option linter.unusedFintypeInType false in
/-- The retained Fintype instance is unused by the schedule-only label bound. -/
theorem fgsa_labelBound [Fintype V] {pt : Unit} (hb : BasePrem p c E rho pt) :
    LabelBound p c E rho :=
  sourceDiscipline_labelBound p c E rho hb.set.valid.toScheduleWellFormed

/-- The frozen atomic node-honesty premise is unused by the store invariants. -/
theorem fgsa_timingContract [Fintype V] {pt : Unit}
    (hb : SourceDisciplinePrem p c E rho pt) : TimingContract p c E rho where
  rowLag := fun _ _ _ _ _ _ he hh => emit_lt_handles p c rho E hb.set.valid he hh
  certLag := sourceDiscipline_strat p c E rho hb (fgsa_rStore p c E rho)
  label := sourceDiscipline_labelBound p c E rho hb.set.valid.toScheduleWellFormed
  atomic := fun i x _ => ⟨(cstoreInv_stateBefore E rho i x).saCompat,
    (storeBundle_stateBefore E rho i x).nest⟩
  tickFG := by
    intro x t nd hpre nd' hpost
    rw [postClock_def, hpre] at hpost
    cases hpost
    exact clock_fg p nd.st t


end AvailableChain.FGSA.Run
end
