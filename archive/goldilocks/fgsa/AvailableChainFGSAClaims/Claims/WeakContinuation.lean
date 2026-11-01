module
public import AvailableChainFGSAClaims.Statements.WeakContinuationLive

@[expose] public section

namespace AvailableChain.FGSA.Run

/-- Additive claim for DC NamedVoteConsumers:56-61, with the intentional
FG-SA differences stated in BoundedSafetyRecovery₂. Like HTimeStatement,
this claim quantifies the validator and input types and the application codec.
ΔF is universal and explicit, with no default.
It states safety only; it does not replace HealingInput or finality liveness. -/
def WeakContinuationClaim (p : Params) (G : Time) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In) (ΔF : Time),
    BoundedSafetyRecovery₂ p (V := V) c G ΔF

/-- bp.weakContinuationAvailable.v2 = safety + inclusion (blueprint 23:103–192);
growth: paper proof in 23 §17 (bp.weakContinuationGrowth.v2).
DC Legacy/Definitions/NamedVoteConsumers.lean:56–61 BoundedSafetyRecovery: SAME
safety role; DC Legacy/Liveness.lean:29–71: SAME inclusion and growth roles.
INTENTIONAL: one joint gate gives safety, actual-proposal service, and
growth conditional on each awake-proposer recurrence gap (B33).
The validator and input types, codec, and explicit row delay are universal. -/
def WeakContinuationLiveClaim (p : Params) (G : Time) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
    (c : AppCodec In) (ΔF : Time),
    BoundedSafetyLivenessRecovery₂ p (V := V) c G ΔF

end AvailableChain.FGSA.Run
end
