module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Quorum
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Accountable
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.HeldSafety

public section

/-! # Goldilocks Healing, HR.4: G1.2 over FG traces

G1.2 (claims G1.2, G1.3) at chain level is `FG.FGParams.finalization_meets_crossing`
(`Lemmas/FGChain/Accountable`). Over an FG trace with `f < 2q − n` it gives, with the signing
argument of `held_atts_safe` (unforgeability, `Store.signed_run`, client safety G0.5), that a
block finalized at height `h_F` in an honest store is an ancestor of every honest block of state
height `> h_F` (`finalized_anc_of_lt_fg`, an instance of `Store.finalized_anc_of_safe`). -/

namespace Consensus.Goldilocks.Healing

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

/-- **G1.2 over an FG trace** (claims G1.2, G1.4). With `f < 2q − n`, a block `F` finalized by
the state of a held `X` in an honest store is an ancestor of every block `W` of an honest store
whose state height exceeds the finalized height: otherwise `F` is not a root of `W`'s chain, and
the finality quorum on `X`'s chain meets the crossing quorum on `W`'s chain in an honest
validator with an E1 pair, against client safety. -/
theorem finalized_anc_of_lt_fg (hr : FGLocalRun acp₀ H U tr) (hH : Hᶜ.ncard < 2 * P.fg.q - P.n)
    {y z : Fin P.n} (hy : y ∈ H) (hz : z ∈ H) {k m : Nat} {X F W : NodeBlock P ACP}
    (hX : X ∈ (tr.store y k).tree) (hF : F ∈ (tr.store y k).tree)
    (hFr : F.root = ((tr.store y k).σ X.root).F) (hW : W ∈ (tr.store z m).tree)
    (hlt : ((tr.store y k).σ X.root).hF < ((tr.store z m).σ W.root).h) :
    Goldilocks.Anc U F W :=
  (Store.finalized_anc_of_safe (Goldilocks.Store.store_reachable hr hy k)
    (Goldilocks.Store.store_reachable hr hz m) hr.coherent (hr.tree_subset y hy k)
    (hr.tree_subset z hz m) hH (held_atts_safe hr hy hz k m) hX hF hFr hW hlt).mono
    (hr.tree_subset z hz m)

end Consensus.Goldilocks.Healing

end
