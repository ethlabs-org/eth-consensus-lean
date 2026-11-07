module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.FG.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality

public section

/-! # Replay finality enters the cache at the actual acceptance event

The pre-state and post-state of an acceptance are both retained through that event's time.
No honesty at the next cut's possibly later timestamp is required.
-/

namespace Consensus.Goldilocks.Healing.Growing

/-- Successful acceptance transfers replay finality to the cache. The quorum budget and
the receiver's honesty are charged at the acceptance, not the next observation time. -/
theorem accepted_replay_finalized_cached {P : Params} {ACP : Type} {acp₀ : ACP}
    {H : Time → Set (Fin P.n)} {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}
    (hr : Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr)
    {y : Fin P.n} {k : Nat} (hy : y ∈ H (tr.time k))
    (hH : (H (tr.time k))ᶜ.ncard < 2 * P.fg.q - P.n)
    {B X : NodeBlock P ACP}
    (ha : tr.AcceptAt y k B) (hX : X ∈ (tr.store y (k + 1)).tree)
    (hXr : X.root = ((tr.store y (k + 1)).σ B.root).F)
    (hFX : Anc U (tr.store y k).F X) : Anc U X (tr.store y (k + 1)).F := by
  have hs : ∀ i, i ≤ k + 1 → (tr.upTo (tr.time k)).state y i = tr.state y i :=
    fun i hi => Trace.upTo_state tr y fun q hq => hr.time_mono (by omega)
  have hacc : FGTrace.AcceptAt (tr.upTo (tr.time k)) y k B :=
    (Trace.upTo_callAt tr).mpr ⟨le_rfl, ha⟩
  simpa only [FGTrace.store, hs k (by omega), hs (k + 1) le_rfl] using
    Healing.accepted_replay_finalized_cached (hr.upTo (hr.time_nonneg k)) hH hy
      (k := k) (B := B) (X := X) hacc
      (by simpa only [FGTrace.store, hs (k + 1) le_rfl] using hX)
      (by simpa only [FGTrace.store, hs (k + 1) le_rfl] using hXr)
      (by simpa only [FGTrace.store, hs k (by omega)] using hFX)

end Consensus.Goldilocks.Healing.Growing

end
