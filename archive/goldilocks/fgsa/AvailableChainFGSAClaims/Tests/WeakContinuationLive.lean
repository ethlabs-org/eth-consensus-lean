module
public import AvailableChainFGSAClaims.Statements.WeakContinuationLive -- shake: keep (test examples)

public section

namespace AvailableChain.FGSA.Run.Tests.WeakContinuationLive

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]

-- Keep the source witness and discharge the safety guard from cut coverage.
example {G ΔF : Time}
    (h : BoundedSafetyLivenessRecovery₂ p (V := V) c G ΔF) :
    BoundedSafetyRecovery₂ p (V := V) c G ΔF := by
  intro hδ E source hs
  obtain ⟨u, Q, iStar, cut, live⟩ := h hδ E source hs
  refine ⟨u, Q, iStar, cut, ?_⟩
  intro E' rho continuation
  exact (live E' rho continuation).safety (cut.beforeEnd.le.trans continuation.covered)

-- No state or safety premise is needed when the gate is beyond the horizon.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (u : Slot) (Q : Block) (iStar : Nat) (ΔF : Time)
    (h : rho.horizon < SA.gateTime p.toParams u) :
    WeakContinuationLiveAt₂ p c E rho u Q iStar ΔF where
  safety := fun hcut => False.elim (not_le_of_gt h hcut)
  inclusion := fun hcut => False.elim (not_le_of_gt h hcut)
  growth := fun hcut => False.elim (not_le_of_gt h hcut)

end AvailableChain.FGSA.Run.Tests.WeakContinuationLive
end
