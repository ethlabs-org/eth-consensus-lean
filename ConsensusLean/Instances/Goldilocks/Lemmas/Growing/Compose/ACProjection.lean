module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.ACProjection

public section

namespace Consensus.Goldilocks.Compose.Growing

/-- The AC projection uses the historical tree universe, not a terminal honest cohort; the
requirement-5 premise at the starts of the nodes honest at `0` covers every retained cohort. -/
theorem ac_projection : ACProjection := by
  intro P A dg H sg tr proposer ini hq hpay h hnc
  have retained (i : Nat) := Compose.ac_projection P A dg (H (tr.time i)) sg
    (tr.upTo (tr.time i)) proposer hq
    (fun y hy => hpay y (h.antitone (h.time_nonneg i) hy)) (h.upTo (h.time_nonneg i))
    (hnc.upTo _)
  have call {y i ℓ} (hc : tr.projAC.CallAt y i ℓ) :
      (tr.upTo (tr.time i)).projAC.CallAt y i ℓ := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  have frame {i Φ} (hf : A.FrameIn ((tr.upTo (tr.time i)).HonestBlocks
      (H (tr.time i))) Φ) : A.FrameIn (tr.HonestBlocksAt H) Φ :=
    ⟨hf.1, fun _ hx => RunTrace.honestBlocks_upTo_subset h.time_mono (h.time_nonneg i)
      (hf.2 hx)⟩
  have lawful {i Φ Φ' c} (hc : A.CallOK ((tr.upTo (tr.time i)).HonestBlocks
      (H (tr.time i))) Φ (tr.time i) c Φ') :
      A.CallOK (tr.HonestBlocksAt H) Φ (tr.time i) c Φ' := ⟨frame hc.1, hc.2⟩
  refine
    { antitone := h.antitone
      coherent := honest_blocks_coherent_local h hnc
      init := fun y hy => by simp only [RunTrace.projAC]; rw [h.init y hy]; rfl
      exec := fun i ℓ hl hy => ?_
      frameLaw := fun y i ℓ hy hc => ?_
      time_nonneg := h.time_nonneg
      time_mono := h.time_mono
      awake_of_call := fun y i ℓ hy hc =>
        h.awake_of_call y i hy ⟨_, Compose.projAC_callAt.mp hc⟩
      restart_of_sleep := fun y i ℓ u hy hc hu hui hs hb => ?_
      restart_at_wake := fun y u v hy hu huv hs hw => ?_
      sleep_of_restart := fun y i ℓ hy hc hr => ?_ }
  · have he := (retained i).exec i ℓ (call ⟨rfl, hl⟩).2 hy
    rw [RunTrace.upTo_projAC, Trace.upTo_node, Trace.upTo_post,
      Trace.upTo_state tr.projAC (tr.projAC.node i) (i := i)
        (fun k hk => h.time_mono hk.le)] at he
    exact he
  · have back {j ℓ'} (hc' : (tr.upTo (tr.time i)).projAC.CallAt y j ℓ') := by
      rw [RunTrace.upTo_projAC] at hc'
      exact ((Trace.upTo_callAt _).mp hc').2
    have nocall {a} (hn : (tr.upTo (tr.time i)).projAC.NoCallBetween y a i) :
        tr.projAC.NoCallBetween y a i := by
      intro j haj hji ℓ' hc'
      apply hn j haj hji ℓ'
      rw [RunTrace.upTo_projAC]
      exact (Trace.upTo_callAt _).mpr ⟨h.time_mono hji.le, hc'⟩
    rcases (retained i).frameLaw y hy i ℓ (call hc) with
      ⟨hn, Φ, hi, hf, hok⟩ | ⟨j, ℓ', hj, hc', hn, hok⟩
    · exact Or.inl ⟨nocall hn, Φ, hi, frame hf, lawful hok⟩
    · exact Or.inr ⟨j, ℓ', hj, back hc', nocall hn, lawful hok⟩
  · apply (retained i).restart_of_sleep y hy i ℓ u (call hc) hu hui
      (fun hw => hs hw.1)
    intro j hj ℓ' hc'
    rw [RunTrace.upTo_projAC] at hc'
    exact hb j hj ℓ' ((Trace.upTo_callAt _).mp hc').2
  · have hr := Compose.ac_projection P A dg (H v) sg (tr.upTo v) proposer hq
      (fun y hy => hpay y (h.antitone (hu.trans huv.le) hy)) (h.upTo (hu.trans huv.le))
      (hnc.upTo v)
    obtain ⟨k, ⟨ℓ, hc, hrestart⟩, huk, hkv⟩ :=
      hr.restart_at_wake y hy u v hu huv (fun hw => hs hw.1) ⟨hw, le_rfl⟩
    rw [RunTrace.upTo_projAC] at hc
    exact ⟨k, ⟨ℓ, ((Trace.upTo_callAt _).mp hc).2, hrestart⟩, huk, hkv⟩
  · obtain ⟨u, hu, hui, hs, hb⟩ := (retained i).sleep_of_restart y hy i ℓ (call hc) hr
    refine ⟨u, hu, hui, fun hw => hs ⟨hw, hui.le⟩, fun j hj ℓ' hc' => ?_⟩
    apply hb j hj ℓ'
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨h.time_mono hj.le, hc'⟩

end Consensus.Goldilocks.Compose.Growing

end
