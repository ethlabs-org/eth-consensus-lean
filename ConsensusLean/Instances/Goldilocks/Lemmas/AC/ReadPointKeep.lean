module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockKeepStep

public section

/-! # Goldilocks SA: a kept lock is live at the read point of a vote

consensus-lean#135 (WI-16), r14 s1 L1.2. At an honest cast at cut `i`, a stored lock `l` on `B`
that the call keeps (no expiry, `B` its own viable ancestor, `unlock` at the call's view
`unlockView` does not move it) is a lock of the vote's read point
(`mem_readPoint_locks_of_keep`), so `B` is a live lock block there
(`mem_readPoint_liveLockBlocks_of_keep`). The `try_vote` that emits the vote unlocks against the
merged view of its input, which is `unlockView` of the call. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}

end Consensus.Goldilocks.SA

end
