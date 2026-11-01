module
public import AvailableChainGeneric.Statements.Pure.Schedule -- shake: keep (public aliases or axiom audit commands)

@[expose] public section

/-! Qualified search (21:2377–2378; 00:297–301), P3 §4.6.
GEN-FIRST: the exact QualSearch and its producers already exist in Gen.Pure.
Consumers: the post-freeze best/search companions (deferred; user 2026-10-02). -/

namespace AvailableChain.FGSA.Run
export Gen.Pure (QualSearch)
end AvailableChain.FGSA.Run
end
