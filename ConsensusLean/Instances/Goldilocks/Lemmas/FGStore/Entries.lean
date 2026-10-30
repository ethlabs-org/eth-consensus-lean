module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run

public section

/-! # Goldilocks FG store: quorum-free entries (the core of G1.10)

Every attestation on the chain of `X` that counts for the entry `E` at height `h` (its height
pair is `(h, E)`) was processed by `y` before `T + Δ` (the own proposal is `y`'s first cut at
`T + Δ`, and its payload comes from the pool), so an honest one was signed before `T + Δ`, at a
public time, so at or before `T`, and (K1) at or before `T₀`: its signer is a namer of `E`. The
progress set of a state at height `h` with entry `E` holds only the signers of such attestations
on its chain, so it stays below `q` (and the target set, inside it): no block from `A` to `X`
justifies or times out, and the height and entry stay. -/

namespace Consensus.Goldilocks.Store

variable (P : Params) (ACP : Type)

/-- **G1.10, the core.** -/
theorem quorum_free_entries : QuorumFreeEntries P ACP := by
  sorry

end Consensus.Goldilocks.Store

end
