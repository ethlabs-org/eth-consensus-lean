module
public import AvailableChainFGSAClaims.Statements.Packages.Safety

@[expose] public section

namespace AvailableChain.FGSA.Run

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V] [Fintype V]

/-- bp.cleanInclusion.v2; 03 §5; P3:3238–3250; S3a FS9:2037–2043.
DC Generic/Regimes:92 SleepyRegime: INTENTIONAL: CleanSet supplies the FG-SA
healthy prefix; the gate must lie in the finite run (S3a Q12)
ΔF: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
structure CleanInclusionPrem (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (pt : PtSP) (ΔF : Time := E.Δ) : Prop where
  set : CleanSet p c E rho ΔF
  prop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P
  hhor : SA.gateTime p.toParams pt.s ≤ rho.horizon

/-- bp.exactProposal.v2; 00:985–997; S3a FS9:2037–2041.
DC Generic/Claims:28–33 AvailableAt: INTENTIONAL: the FG-SA local adoption
statement uses CleanSet and a supplied honest proposal (03 §4)
ΔF: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
structure ExactProposalPrem (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (pt : PtSP) (ΔF : Time := E.Δ) : Prop where
  set : CleanSet p c E rho ΔF
  prop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P
  hhor : SA.voteTime p.toParams pt.s ≤ rho.horizon

end AvailableChain.FGSA.Run
end
