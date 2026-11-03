module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Recovery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements

public section

/-! # Goldilocks Healing: replay finality enters the cache (HR.5)

Successful acceptance puts the carrier's replay-finalized block below the actual cache under
the FG fault bound. Reset timing and high height are unnecessary for this stronger fact;
`CacheAcceptanceAfterReset` is its Goldilocks projection, with its statement unchanged. -/

namespace Consensus.Goldilocks.Healing

/-- An honest acceptance caches its carrier's replay-finalized block. Unlike HR.5, this needs
neither a reset nor a lower bound on time or height: replay safety compares the old cache with
the target, and the advancing case is `accepted_replay_finalized_cached`. -/
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
    · have hm := (Goldilocks.Store.finalized_monotone _ _ _ _
        (Goldilocks.Store.store_reachable hr hy k)).1 _ _
        (Goldilocks.Store.accept_onBlock hr hy ha)
      exact hXF.trans (hm.mono (hr.tree_subset y hy (k + 1)))
    · exact accepted_replay_finalized_cached hr hf hy ha hX hXr hFX
  exact Goldilocks.Store.anc_of_U hr hy hout
    (Goldilocks.Store.cache_invariants _ _ _ _ hpost).1

/-- **HR.5:** an honest acceptance after the reset caches its high replay-finalized target. -/
theorem cache_acceptance_after_reset : CacheAcceptanceAfterReset := by
  intro sp ro proposer dg H tr g ΔF hrun hh hnc a _ha y hy k B hB _htime Fs hFs hroot _hheight
  have hreq := SA.interface_requirements sp (List (FG.Att sp.n)) ro
  have hfg := Compose.fg_projection _ _ dg H _ tr proposer
    ⟨hreq.1, hreq.2.1, hreq.2.2.1, hreq.2.2.2, SA.proposal_payload_valid sp _ ro⟩
    hrun.genesis_root_ok hrun.toLocalRun hnc
  have hst : ∀ i, tr.projFG.store y i = (tr.state y i).fg :=
    fun i => by simp only [FGTrace.store, Compose.projFG_state hrun.toLocalRun hy i]
  have hpost : tr.projFG.store y (k + 1) = (tr.post k).fg := by
    rw [hst, tr.state_succ_of_call hB]
  have hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.toParams.n := by
    have hf := hh.2.2
    have hn := sp.toParams.hn
    change Hᶜ.ncard < 2 * ((2 * sp.toParams.n + 2) / 3) - sp.toParams.n
    omega
  have h := accepted_finality_cached hfg hf hy (Compose.projFG_callAt.mpr hB)
    (hpost.symm ▸ hFs) (hpost.symm ▸ hroot)
  simpa only [hpost] using h

end Consensus.Goldilocks.Healing

end
