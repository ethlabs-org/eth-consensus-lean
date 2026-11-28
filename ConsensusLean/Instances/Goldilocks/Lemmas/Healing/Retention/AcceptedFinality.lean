module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety

public section

/-! # Goldilocks Healing: replay finality enters the cache

Successful acceptance puts the carrier's replay-finalized block below the actual cache under the FG
fault bound (`accepted_finality_cached`), with no reset, time or height bound. The growing G1.9 (b)
(`Healing.Growing.cache_acceptance`) reads it on the static prefix of the run. -/

namespace Consensus.Goldilocks.Healing

/-- An honest acceptance caches its carrier's replay-finalized block. Unlike the claims' HR.5,
this needs neither a reset nor a lower bound on time or height: replay safety compares the old
cache with the target, and the advancing case is `accepted_replay_finalized_cached`. -/
theorem accepted_finality_cached {P : Params} {ACP : Type} {acp₀ : ACP}
    {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}
    (hr : FGLocalRun acp₀ H U tr) (hf : Hᶜ.ncard < 2 * P.fg.q - P.n)
    {y : Fin P.n} (hy : y ∈ H) {k : Nat} {B X : NodeBlock P ACP}
    (ha : tr.AcceptAt y k B) (hX : X ∈ (tr.store y (k + 1)).tree)
    (hXr : X.root = ((tr.store y (k + 1)).σ B.root).F) :
    (tr.store y (k + 1)).Anc X (tr.store y (k + 1)).F := by
  have hpost := Goldilocks.Store.store_reachable hr hy (k + 1)
  have hB : B ∈ (tr.store y (k + 1)).tree := by
    rw [(Goldilocks.Store.tree_grows _ _ _ _
      (Goldilocks.Store.store_reachable hr hy k)).1 _ _
      (Goldilocks.Store.accept_onBlock hr hy ha)]
    exact Set.mem_insert _ _
  have hcompat := Goldilocks.Store.replay_finalized_safety hr hf hy hy hB hX hXr (j := k)
  have hout : Anc U X (tr.store y (k + 1)).F := by
    rcases hcompat with hXF | hFX
    · have hm := (Goldilocks.Store.finalized_monotone _ _ _).1 _ _
        (Goldilocks.Store.accept_onBlock hr hy ha)
      exact hXF.trans (hm.mono (hr.tree_subset y hy (k + 1)))
    · exact accepted_replay_finalized_cached hr hf hy ha hX hXr hFX
  exact Goldilocks.Store.anc_of_U hr hy hout
    (Goldilocks.Store.cache_invariants _ _ _ _ hpost).1

end Consensus.Goldilocks.Healing

end
