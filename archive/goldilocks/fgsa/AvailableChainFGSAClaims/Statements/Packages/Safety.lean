module
public import AvailableChainFGSAClaims.Statements.Regimes
public import AvailableChainFGSAClaims.Statements.Windows

@[expose] public section

namespace AvailableChain.FGSA.Run

structure PtS where
  s : Slot
structure PtSP where
  s : Slot
  P : Block
structure PtSX where
  s : Slot
  X : Block

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V] [Fintype V]

/-- Foundation package for claims that need only Base. -/
structure BasePrem {Pt : Type} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (_pt : Pt) : Prop where
  set : BaseSet p c E rho

/-- Safety premise with a separate row delivery bound.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
structure SameLabelPrem (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (pt : PtS) : Prop where
  set : BaseSet p c E rho
  sync : Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams pt.s) (SA.gateTime p.toParams pt.s)

structure SourceDisciplinePrem {Pt : Type} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (_pt : Pt) : Prop where
  set : BaseSet p c E rho
  quorum : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card

structure FinalizedSafetyPrem {Pt : Type} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (_pt : Pt) : Prop where
  set : BaseSet p c E rho
  fault : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3

/-- Safety premise with a separate row delivery bound.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
structure CleanPrem {Pt : Type} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (_pt : Pt) (ΔF : Time := E.Δ) : Prop where
  set : CleanSet p c E rho ΔF

/-- Safety premise with a separate row delivery bound.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
structure CleanPrefixPrem (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (pt : PtB₀) (ΔF : Time := E.Δ) : Prop where
  set : CleanPrefixSet p c E rho pt.b₀ ΔF

/-- Safety premise with a separate row delivery bound.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
structure CleanCutPrem (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (pt : PtB₀) (ΔF : Time := E.Δ) : Prop where
  set : CleanCutSet p c E rho pt.b₀ ΔF

/-- R5-65: time-free release premise, family (0). -/
structure ReleasePrem (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (_pt : Unit) : Prop where
  set : BaseSet p c E rho
  lt : (Gen.V2.Duty.faulty rho).card < SA.releaseThreshold p.toParams

end AvailableChain.FGSA.Run
end
