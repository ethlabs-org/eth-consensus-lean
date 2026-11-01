module
public import AvailableChainFGCompose.Proofs.SafetyOrigin
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyScope
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyStore

set_option linter.privateModule false

public section
namespace AvailableChain.FGSA.Run.Tests.P0Origin
open AvailableChain.SimplexFG AvailableChain.FGCompose

/-! P0-origin: FG-SA is an instance of the origin record. The frozen FG-SA store laws give
the origin record with no pending object, and the origin consumers give the same results as
the frozen consumers. No FG-SA declaration changes. -/

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- The FG-SA instance of the origin record: no object is pending. -/
private theorem fgsa_origin_laws :
    FGSafetyStoreOriginLaws (fgsaCoreReads p c) (fgsaSafetyReads p c)
      (heightView p) (finalityView p) (fun nd => Reachable p nd.st) (fun _ _ => False) :=
  safetyStoreOriginLaws_of_storeLaws (fgsaSafetyStoreLaws p c)

/-- The origin event-agreement consumer at the FG-SA reads: the same generic conclusion as
`safety_event_agreement` at the frozen record. -/
private theorem fgsa_origin_event_agreement
    (hr : safetyScopedRoots (fgsaCoreReads p c) (RootBlockInRun p c E rho))
    (hb : safetyBound (fgsaCoreReads p c) (fgsaSafetyReads p c) p.E E rho)
    (i j : Nat) (x y : V) :
    FGBlock.compatible ((fgsaCoreReads p c).core (V2.D.Run.stateBefore E rho i x)).fg.F
      ((fgsaCoreReads p c).core (V2.D.Run.stateBefore E rho j y)).fg.F = true :=
  safety_event_agreement_origin _ _ _ _ _ E rho _ _ _ (fgsaCoreLaws p c)
    (fgsa_origin_laws p c) (fgCertificateLaws p) (fgsaSafetyScopeLaws p c E rho) hr hb i j x y

/-- The origin carriage consumer at the FG-SA reads. -/
private theorem fgsa_origin_read_carriage (hU : V2.D.UnforgeableSignatures E rho)
    (t : Time) (x : V) :
    safetyCarriage (fgsaSafetyReads p c) E rho
      (safetyRows (fgsaCoreReads p c) (V2.D.Run.readAt E rho t x)) :=
  safety_read_carriage_origin (fgsaCoreLaws p c) (fgsa_origin_laws p c)
    (fgsaSafetyWireLaws p c) hU t x

#print axioms fgsa_origin_laws
#print axioms fgsa_origin_event_agreement
#print axioms fgsa_origin_read_carriage

end AvailableChain.FGSA.Run.Tests.P0Origin
end
