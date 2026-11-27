module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Frontier.Accountable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.OwnBlockReady
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo

public section

/-! # Preview coverage from chain conviction, without an FG fault bound -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- A held carrier's replay finality is below the reader's actual cache under
the continuation's existing chain-conviction premise. No numeric FG fault
bound, reset, healthy window or stable-finality premise is added. -/
theorem held_replay_finality_cached_of_conviction
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hcv : Compose.Growing.ChainConvictedBelow tr H)
    {y : Fin sp.n} {j : Nat} {t : Time} (ht : 0 ≤ t)
    (hj : ∀ k < j, tr.time k ≤ t) (hy : y ∈ H t)
    {B F : AC.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ (tr.state y j).fg.tree) (hF : F ∈ (tr.state y j).fg.tree)
    (hFr : F.root = ((tr.state y j).fg.σ B.root).F) :
    (tr.state y j).fg.Anc F (tr.state y j).fg.F := by
  let rt := tr.upTo t
  have rr := hrun.upTo ht
  have fg := Compose.fg_projection_from
    (fun y _ => Compose.requirements_from sp ro (rr.vstart y)) rr.genesis_root_ok
    rr.toLocalRun (hnc.upTo t)
  have hs : ∀ k, rt.projFG.store y k = (rt.state y k).fg :=
    fun k => by
      change (tr.upTo t).projFG.store y k = ((tr.upTo t).state y k).fg
      simp only [FGTrace.store, Compose.projFG_state rr.toLocalRun hy k]
  have hsJ : rt.projFG.store y j = (tr.state y j).fg := by
    rw [hs, Trace.upTo_state tr y hj]
  have comparisons : ∀ k {C X : AC.Blk sp.n (List (FG.Att sp.n))},
      C ∈ (rt.projFG.store y k).tree → X ∈ (rt.projFG.store y k).tree →
      X.root = ((rt.projFG.store y k).σ C.root).F →
      ∀ W ∈ (rt.projFG.store y k).tree,
        ((rt.projFG.store y k).σ C.root).hF < ((rt.projFG.store y k).σ W.root).h →
        (rt.projFG.store y k).Anc X W := by
    intro k C X hC hX hXr W hW hlt
    obtain ⟨i, _, hi, he⟩ := Trace.upTo_state_exists (d := t) tr hrun.time_mono y k
    rw [hs, he] at hC hX hXr hW hlt ⊢
    exact store_anc_of_honest_anc_at hrun hnc ht hi hy
      (Consensus.Goldilocks.Growing.GoldilocksRun.finalized_anc_of_lt_conv
        hrun hnc hcv ht hi hy ht hi hy hC hX hXr hW hlt) hW
  have acceptance : ∀ {k C X}, rt.projFG.AcceptAt y k C →
      X ∈ (rt.projFG.store y (k + 1)).tree →
      X.root = ((rt.projFG.store y (k + 1)).σ C.root).F →
      (rt.projFG.store y (k + 1)).Anc X (rt.projFG.store y (k + 1)).F := by
    intro k C X ha hX hXr
    have hb := Store.accept_onBlock fg hy ha
    have hC : C ∈ (rt.projFG.store y (k + 1)).tree := by
      rw [(Store.tree_grows _ _ _ _ (Store.store_reachable fg hy k)).1 C _ hb]
      exact Set.mem_insert _ _
    exact Store.onBlock_finality_cached_of_ancestry (Store.store_reachable fg hy k)
      hb hX hXr (comparisons (k + 1) hC hX hXr)
  rw [← hsJ] at hB hF hFr ⊢
  rcases Store.tree_accepted fg hy hB with he | ⟨k, hkj, ha⟩
  · rw [he, show (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).root =
        sp.toParams.genesisRoot from rfl,
      Healing.Store.σ_genesis (Store.store_reachable fg hy j)] at hFr
    have heF : F = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload :=
      fg.coherent.1 (fg.tree_subset y hy j hF)
        (fg.tree_subset y hy j (Healing.Store.genesis_mem (Store.store_reachable fg hy j))) hFr
    rw [heF]
    exact (Store.accepted_tree _ _ _ _ (Store.store_reachable fg hy j)).2.2.2 _
      (Store.cache_invariants _ _ _ _ (Store.store_reachable fg hy j)).1
  have hb := Store.accept_onBlock fg hy ha
  have hBk : B ∈ (rt.projFG.store y (k + 1)).tree := by
    rw [(Store.tree_grows _ _ _ _ (Store.store_reachable fg hy k)).1 B _ hb]
    exact Set.mem_insert _ _
  obtain ⟨_, ⟨F', hF', hF'r, _⟩, _⟩ := Store.entry_state_of_source _ _ _ _
    (Store.store_reachable fg hy (k + 1)) B hBk
  have hBm := (Store.held_mono fg hy hkj hBk).2
  have heF : F' = F := fg.coherent.1
    (fg.tree_subset y hy j (Store.held_mono fg hy hkj hF').1)
    (fg.tree_subset y hy j hF) (hF'r.trans (hBm ▸ hFr.symm))
  subst F'
  exact Store.cached_preview_at_later_cut fg hy hkj (acceptance ha hF' hF'r)

/-- Every target in the observed reader frame extends the held block's
root-free preview, even in the sleepy suffix with only chain conviction. -/
theorem held_preview_ancestor_frame_of_conviction
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hcv : Compose.Growing.ChainConvictedBelow tr H)
    {y : Fin sp.n} {j : Nat} {t : Time} (ht : 0 ≤ t)
    (hj : ∀ k < j, tr.time k ≤ t) (hy : y ∈ H t)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} {pr : Nat}
    (hB : B ∈ (tr.state y j).fg.tree) (hp : B.parent = some pr) :
    ∃ F ∈ (tr.state y j).fg.tree,
      F.root = sp.toParams.fg.finalityPreview ((tr.state y j).fg.σ pr) B.slot B.fgPayload ∧
      ∀ X ∈ (tr.state y j).fg.toFrame.tree, (tr.state y j).fg.Anc F X := by
  have hr := fg_reachable_at hrun ht hj hy
  obtain ⟨_, ⟨F, hF, hFr, _⟩, _⟩ := Store.entry_state_of_source _ _ _ _ hr B hB
  have hcached := held_replay_finality_cached_of_conviction hrun hnc hcv ht hj hy hB hF hFr
  refine ⟨F, hF, hFr.trans ?_, fun X hX => hcached.trans hX.2⟩
  obtain ⟨_, _, _, hstep⟩ := Healing.Store.step_σ hr hB hp
  exact sp.toParams.fg.stateTransition_finalityPreview hstep

end Consensus.Goldilocks.Healing.Growing

end
