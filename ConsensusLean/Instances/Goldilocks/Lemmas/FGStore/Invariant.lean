module
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Tree
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Entry
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Handlers

public section

/-! # Goldilocks FG store: the reachable-state invariant (G0.1, F.2, G0.3, entry states)

One invariant of the FG states that the handlers reach, by induction over the steps: the tree
is kept by root, finite, contains genesis and is closed under parents with increasing slots;
every accepted block has a chain in the tree whose fold is its state (G0.1), which places the
entry, justification and finalization of its state on its chain; and the caches name accepted
blocks of accepted states (G0.3). The statements of part 1 about one reachable state follow. -/

namespace Consensus.Goldilocks.Store

variable (P : Params) (ACP : Type)

/-- A held root names the block with that root. -/
theorem Reachable.blocks_root {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (h : st.Reachable acp₀) {r : Nat} {X : NodeBlock P ACP} (hX : st.blocks r = some X) :
    X.root = r := by
  sorry

/-- **G0.1 (store).** -/
theorem chain_state_of_chain : ChainStateOfChain P ACP := by
  sorry

/-- **F.2 at the store, the accepted tree.** -/
theorem accepted_tree : AcceptedTree P ACP := by
  sorry

/-- **F.2 at the store, the tree only grows.** -/
theorem tree_grows : TreeGrows P ACP := by
  sorry

/-- **G0.3.** -/
theorem cache_invariants : CacheInvariants P ACP := by
  sorry

/-- **G0.2 (c), (h) at the store.** -/
theorem entry_state_of_source : EntryStateOfSource P ACP := by
  sorry

end Consensus.Goldilocks.Store

end
