module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Growing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Trace.UpTo

public section

namespace Consensus.Goldilocks

variable {P : Params}

namespace Growing

variable {ACP : Type} {acp₀ : ACP} {H : Time → Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

/-- **Retention of the FG contract.** -/
theorem FGLocalRun.upTo (h : Growing.FGLocalRun acp₀ H U tr) {d : Time} (hd : 0 ≤ d) :
    Consensus.Goldilocks.FGLocalRun acp₀ (H d) U (tr.upTo d) := by
  have hm := h.time_mono
  have anti : ∀ {t}, t ≤ d → H d ⊆ H t := fun ht => h.antitone ht
  have hstate : ∀ {y i}, tr.time i ≤ d → (tr.upTo d).state y i = tr.state y i :=
    fun hi => Trace.upTo_state tr _ fun _ hk => (hm hk.le).trans hi
  refine
    { coherent := h.coherent
      init := fun y hy => h.init y (anti hd hy)
      exec := fun i ℓ hl hy => ?_
      tree_subset := fun y hy i => ?_
      time_nonneg := h.time_nonneg
      time_mono := hm
      attest_public := fun y hy i src signed hc => ?_
      own_first := fun y hy i B hc hp hs k hk ℓ hck => ?_
      attest_order := fun y hy j src signed hc i ℓ hij hci hti => ?_
      own_payload := fun y hy i B hc hp hs => ?_
      unforgeable := fun y hy i a ha hv => ?_ }
  · obtain ⟨hid, hl⟩ := (Trace.upTo_label_eq_some tr).mp hl
    rw [hstate hid]
    exact h.exec i ℓ hl (anti hid hy)
  · obtain ⟨i₀, -, hb, hs⟩ := Trace.upTo_state_exists tr hm y i
    change ((tr.upTo d).state y i).1.tree ⊆ U
    rw [hs]
    exact h.tree_subset y i₀ d hd hb hy
  · obtain ⟨hid, hc⟩ := (Trace.upTo_callAt tr).mp hc
    exact h.attest_public y i src signed (anti hid hy) hc
  · obtain ⟨hid, hc⟩ := (Trace.upTo_callAt tr).mp hc
    exact h.own_first y i B (anti hid hy) hc hp hs k hk ℓ ((Trace.upTo_callAt tr).mp hck).2
  · obtain ⟨hjd, hc⟩ := (Trace.upTo_callAt tr).mp hc
    exact h.attest_order y j src signed (anti hjd hy) hc i ℓ hij
      ((Trace.upTo_callAt tr).mp hci).2 hti
  · obtain ⟨hid, hc⟩ := (Trace.upTo_callAt tr).mp hc
    change ∀ a ∈ B.fgPayload, a ∈ ((tr.upTo d).state y i).1.atts
    rw [hstate hid]
    exact h.own_payload y i B (anti hid hy) hc hp hs
  · obtain ⟨ℓ, hc, haℓ⟩ := ha
    obtain ⟨hid, hc⟩ := (Trace.upTo_callAt tr).mp hc
    obtain ⟨j, hji, src, hj⟩ := h.unforgeable y i a (anti hid hy) ⟨ℓ, hc, haℓ⟩ (anti hid hv)
    exact ⟨j, hji, src, (Trace.upTo_callAt tr).mpr ⟨(hm hji.le).trans hid, hj⟩⟩

end Growing

end Consensus.Goldilocks

end
