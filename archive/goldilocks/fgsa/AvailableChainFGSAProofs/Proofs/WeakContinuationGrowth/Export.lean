module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Replay -- shake: keep (retained local replay)
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Counts -- shake: keep (half-cap quorum facts)
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Origins -- shake: keep (slashing-based low finalization)

public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Seed -- shake: keep (seed state replay)
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.StepInit -- shake: keep (initial invariant)

public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Frame -- shake: keep (companion frame)

public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.EventReplay -- shake: keep (local event correspondence)

public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Dynamics -- shake: keep (weaker event induction)

public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Empty -- shake: keep (empty retained continuation)
public import AvailableChainFGSAClaims.Claims.WeakContinuationGrowth -- shake: keep (companion public claim)

/-! Additive WC growth lane. These are proved component lemmas.
The closed WeakContinuationGrowthClaim is still open; see OPEN.md. -/
