module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant

public section

/-! # Goldilocks FG store: the finalized block is strictly below its finalizer

In a reachable store, `Σ.F` other than genesis is finalized by the state of a strict descendant
in the tree (`F_lt_finalizer`): the finality votes for the pair `(h_F, F)` are counted only in
blocks of a greater height, which strictly extend `F` (workbench#12 §4). (`Σ.F = Σ.J` itself is
possible away from genesis: a chain state can finalize its latest justified pair, and
`update_finality` then moves `Σ.F` onto `Σ.J`.) Used by `Compose/Service/Held`
(`updater_F_anc_proposal`). Open. -/

namespace Consensus.Goldilocks.Store

/-- **The finalizer of `Σ.F` strictly extends it** (open). -/
theorem F_lt_finalizer {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) (hF : st.F ≠ P.genesisBlock acp₀) :
    ∃ B ∈ st.tree, (st.σ B.root).F = st.F.root ∧ st.Anc st.F B ∧ st.F ≠ B := by
  sorry

end Consensus.Goldilocks.Store

end
