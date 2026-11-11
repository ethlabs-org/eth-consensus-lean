module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.CorrectLocal
public import ConsensusLean.Spec.Shape.Run

@[expose] public section

/-! # Unconditional local-store chain representation

Admission-free contracts only: no instances or evidence are supplied. Local-store ancestry
and store extension are distinct from ancestry in a coherent union of different readers.
Neither law assumes collision freedom or constant faults. Actual-read transport and protocol
invariants must supply their premises before the unconditional shape claims can consume them.
-/

namespace Consensus.Goldilocks.Generic

open Shape Blocks

/-- UNPROVED representation laws for the same chain and header maps used by the engine.
The concrete sources are `Lemmas/Simulation/Chains.lean:62` (`chainTo_prefix`) and
`:85` (`chainTo_mono`). The latter needs reachability only of the old store and membership
of the old tip; neither law needs root hashing correctness or coherent-union ancestry.
The intended consumers are unconditional nesting and final monotonicity, not cross-reader
agreement. Instantiating this contract for an arbitrary AC remains a supplier obligation. -/
structure ChainRepresentation {P : Params} (A : NodeAC P) {Info : Type}
    (chain : NodeState A → A.Blk → List A.Blk) (header : A.Blk → Header Info) : Prop where
  /-- Ancestry in one reachable store gives a prefix, including reflexive ancestry. -/
  same_store_prefix : ∀ st : NodeState A, st.fg.Reachable A.genesisPayload →
    ∀ B C, st.fg.Anc B C →
      List.IsPrefix ((chain st B).map header) ((chain st C).map header)
  /-- Extending the store preserves the represented chain of every previously held block.
  The later AC state and durable record need not equal the earlier ones. -/
  store_growth : ∀ st st' : NodeState A, st.fg.Reachable A.genesisPayload →
    st.fg.tree ⊆ st'.fg.tree → ∀ B, B ∈ st.fg.tree →
      (chain st B).map header = (chain st' B).map header

end Consensus.Goldilocks.Generic

end
