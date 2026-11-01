import AvailableChainFGSAInhabit.WeakContinuationW1
import AvailableChainFGSAProofs.Proofs.Assembly.Root

open AvailableChain AvailableChain.FGSA AvailableChain.FGSA.Run
open AvailableChain.FGSA.Run.Tests.WeakContinuationWitness

/-! WC-W1CHECK: the W1 application of the closed weak-continuation claim.

Run from the repository root after the Claims, Proofs and Inhabit builds:
  lake env lean scripts/CheckWeakContinuationW1.lean

Apply the aggregate field to the W1 strong recovery, then to its clean
continuation. Print the theorem's axioms for scripts/check-fgsa-claims.sh.
That check rejects compile errors, warnings and axioms other than propext,
Classical.choice and Quot.sound. -/

namespace AvailableChain.FGSA.Run.Tests.WeakContinuationWitness

/-- WC plan r2.1, §8 Job 4; DC: SAME source witness before continuation.
Apply the closed aggregate field to the W1 source and its weaker continuation. -/
theorem w1_weakContinuationLive :
    ∃ (u : Slot) (Q : Block) (iStar : Nat),
      BoundedHealingCut₂ params unitCodec strongEnv source u Q iStar 1 ∧
      WeakContinuationLiveAt₂ params unitCodec weakEnv continuation u Q iStar 1 := by
  have hδ : params.δt = 2 * params.R := by decide
  obtain ⟨u, Q, iStar, hcut, hcont⟩ :=
    (fgsaClaims params).weakContinuationLive 4 unitCodec 1 hδ
      strongEnv source w1_strongRecovery
  exact ⟨u, Q, iStar, hcut, hcont weakEnv continuation w1_cleanContinuationSleep⟩

#print axioms w1_weakContinuationLive

end AvailableChain.FGSA.Run.Tests.WeakContinuationWitness
