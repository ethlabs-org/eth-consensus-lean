module
public import AvailableChainFGSAClaims.Statements.WeakContinuationGrowth

@[expose] public section

namespace AvailableChain.FGSA.Run

/-- Additive WC corruption-growth companion. DC RecoveredBy uses the same
whole-run slashing premise. The source witness is uniform over continuations.
The frozen WC aggregate is unchanged. -/
def WeakContinuationGrowthClaim (p : Params) (G : Time) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
    (c : AppCodec In) (ΔF : Time),
    BoundedGrowthRecovery₂ p (V := V) c G ΔF

end AvailableChain.FGSA.Run
end
