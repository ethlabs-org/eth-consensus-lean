module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection

public section

namespace Consensus.Goldilocks.Compose.Growing

/-- The FG projection obeys each law at the caller's own honesty horizon. -/
theorem fg_projection : FGProjection := by
  intro P A dg H sg tr proposer hq hg h hnc
  have retained (i : Nat) := Compose.fg_projection P A dg (H (tr.time i)) sg
    (tr.upTo (tr.time i)) proposer hq hg (h.upTo (h.time_nonneg i)) (hnc.upTo _)
  have call {y i ℓ} (hc : tr.projFG.CallAt y i ℓ) :
      (tr.upTo (tr.time i)).projFG.CallAt y i ℓ := by
    rw [RunTrace.upTo_projFG]
    exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  refine
    { antitone := h.antitone
      coherent := honest_blocks_coherent_local h hnc
      init := fun y hy => ?_
      exec := fun i ℓ hl hy => ?_
      tree_subset := fun y i t ht hb hy X hX => ?_
      time_nonneg := h.time_nonneg
      time_mono := h.time_mono
      attest_public := fun y i src signed hy hc =>
        (retained i).attest_public y hy i src signed (call hc)
      own_first := fun y i B hy hc hp ht k hk ℓ hck => ?_
      attest_order := fun y j src signed hy hc i ℓ hij hci ht => ?_
      own_payload := fun y i B hy hc hp ht a ha => ?_
      unforgeable := fun y i a hy hc hv => ?_ }
  · change ((tr.init y).fg, (tr.init y).record) = _
    rw [h.init y hy]
    rfl
  · have he := (retained i).exec i ℓ (call ⟨rfl, hl⟩).2 hy
    rw [RunTrace.upTo_projFG, Trace.upTo_node, Trace.upTo_post] at he
    rw [Trace.upTo_state tr.projFG (tr.projFG.node i) (i := i)
      (fun k hk => h.time_mono hk.le)] at he
    exact he
  · have hs := Trace.upTo_state tr.projFG y hb
    have hs' := Trace.upTo_state tr y hb
    have hp := Compose.projFG_state (h.upTo ht) hy i
    rw [RunTrace.upTo_projFG, hs, hs'] at hp
    exact ⟨y, i, t, ht, hb, hy, by simpa only [FGTrace.store, hp] using hX⟩
  · apply (retained i).own_first y hy i B (call hc) hp ht k hk ℓ
    rw [RunTrace.upTo_projFG]
    exact (Trace.upTo_callAt _).mpr ⟨h.time_mono hk.le, hck⟩
  · apply (retained j).attest_order y hy j src signed (call hc) i ℓ hij
      (by rw [RunTrace.upTo_projFG]; exact (Trace.upTo_callAt _).mpr ⟨h.time_mono hij.le, hci⟩) ht
  · have hp' := (retained i).own_payload y hy i B (call hc) hp ht a ha
    simpa only [FGTrace.store, RunTrace.upTo_projFG,
      Trace.upTo_state tr.projFG y (fun k hk => h.time_mono hk.le)] using hp'
  · have hc' : (tr.upTo (tr.time i)).projFG.ProcessAt y i a := by
      obtain ⟨ℓ, hc, ha⟩ := hc
      exact ⟨ℓ, call hc, ha⟩
    obtain ⟨j, hji, src, hj⟩ := (retained i).unforgeable y hy i a hc' hv
    rw [RunTrace.upTo_projFG] at hj
    exact ⟨j, hji, src, ((Trace.upTo_callAt _).mp hj).2⟩

end Consensus.Goldilocks.Compose.Growing

end
