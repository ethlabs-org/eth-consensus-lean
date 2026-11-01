module
public import AvailableChainFGSARun.Proofs.Roots -- shake: keep (re-export)
public import AvailableChainFGSA.Proofs.CrossNode -- shake: keep (re-export)

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC NamedRootCollisionFree] Exact named delivery gives full agreement. -/
theorem contentAgree_run (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho) (v w : V) (i j : Nat) :
    ContentAgree (V2.D.Run.stateBefore E rho i v).st (V2.D.Run.stateBefore E rho j w).st := by
  intro s N hN s' N' hN' he
  cases namedProposal_eq E rho hr (namedScope_stored_proposal E rho i v hN)
    (namedScope_stored_proposal E rho j w hN') he
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end AvailableChain.FGSA.Run
