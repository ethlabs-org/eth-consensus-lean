module
public import AvailableChainFGSARun.Statements.Interface
public import AvailableChainGeneric.Statements.AC.Duty.Reads

@[expose] public section

namespace AvailableChain.FGSA.Run

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Event-indexed AC reads. The parent read extracts the parent of a proposal.
The fast read is empty on a saved label; it never reads `fastWriteAt`. -/
def fgsaAC {p : Params} {In : Type} {c : AppCodec In} {V : Type} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : Gen.AC.Duty.ACReads E rho .root where
  I := fgsaInterface p c
  prm := p.toParams
  output i x := (V2.D.Run.stateBefore E rho i x).st.base.stableRecord
  anchor i x := eraseFG (V2.D.Run.stateBefore E rho i x).st.fg.F
  head i x := let st := (V2.D.Run.stateBefore E rho i x).st
              some (headVote p st (st.slot p))
  parent _ b := b.parent
  raw i s x := let st := (V2.D.Run.stateBefore E rho i x).st
               SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F)
                 (SA.Root.expire { actView st with now := SA.gateTime p.toParams s }
                   (SA.gateTime p.toParams s)) s
  leases i x := (V2.D.Run.stateBefore E rho i x).st.base.obligations
  fast i s x := let st := clockPre p (V2.D.Run.stateBefore E rho i x).st
                          (SA.gateTime p.toParams s)
                if (SA.Root.savedGenuine st.base s).isSome then [] else
                  fastSet p (eraseFG st.fg.F) (actView st) s
  now i x := (V2.D.Run.stateBefore E rho i x).st.base.now
  activeView i x := actView (V2.D.Run.stateBefore E rho i x).st
  admissionLevels := @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine p.n .root

end AvailableChain.FGSA.Run
end
