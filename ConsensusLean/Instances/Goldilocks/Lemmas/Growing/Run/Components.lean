module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.FG.Retention
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Growing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo

public section

/-! # Retention of the component contracts

The prefix through `d ≥ 0` of an AC or FG trace under growing faults satisfies the static
contract for the validators honest at `d` (`Growing.ACLocalRun.upTo`, `Growing.FGLocalRun.upTo`),
as `Growing.GoldilocksRun.upTo` does for runs: a validator honest at `d` was honest at every
earlier cut. -/

namespace Consensus.Goldilocks

variable {P : Params}

namespace Growing

variable {FGP : Type} {A : ACInterface P FGP} {H : Time → Set (Fin P.n)} {U : Set A.Blk}
  {tr : ACTrace A}

/-- **Retention of the AC contract.** -/
theorem ACLocalRun.upTo (h : Growing.ACLocalRun A H U tr) {d : Time} (hd : 0 ≤ d) :
    Consensus.Goldilocks.ACLocalRun A (H d) U (tr.upTo d) := by
  have hm := h.time_mono
  have anti : ∀ {t}, t ≤ d → H d ⊆ H t := fun ht => h.antitone ht
  have hstate : ∀ {y i}, tr.time i ≤ d → (tr.upTo d).state y i = tr.state y i :=
    fun hi => Trace.upTo_state tr _ fun _ hk => (hm hk.le).trans hi
  have hcall : ∀ {y i ℓ}, tr.time i ≤ d → tr.CallAt y i ℓ → (tr.upTo d).CallAt y i ℓ :=
    fun hi hc => (Trace.upTo_callAt tr).mpr ⟨hi, hc⟩
  have hnone : ∀ {y j i}, tr.NoCallBetween y j i → ACTrace.NoCallBetween (tr.upTo d) y j i :=
    fun hn k hjk hki ℓ hc => hn k hjk hki ℓ ((Trace.upTo_callAt tr).mp hc).2
  refine
    { coherent := h.coherent
      init := fun y hy => h.init y (anti hd hy)
      exec := fun i ℓ hl hy => ?_
      frameLaw := fun y hy i ℓ hc => ?_
      time_nonneg := h.time_nonneg
      time_mono := hm
      awake_of_call := fun y hy i ℓ hc => ?_
      restart_of_sleep := fun y hy i ℓ u hc hu hui hs hb => ?_
      restart_at_wake := fun y hy u v hu huv hs hv => ?_
      sleep_of_restart := fun y hy i ℓ hc hr => ?_ }
  · obtain ⟨hid, hl⟩ := (Trace.upTo_label_eq_some tr).mp hl
    rw [hstate hid]
    exact h.exec i ℓ hl (anti hid hy)
  · obtain ⟨hid, hc⟩ := (Trace.upTo_callAt tr).mp hc
    rcases h.frameLaw y i ℓ (anti hid hy) hc with ⟨hn, Φ₀, h1, h2, h3⟩ | ⟨j, ℓ', hji, hcj, hn, hok⟩
    · exact Or.inl ⟨hnone hn, Φ₀, h1, h2, h3⟩
    · exact Or.inr ⟨j, ℓ', hji, hcall ((hm hji.le).trans hid) hcj, hnone hn, hok⟩
  · obtain ⟨hid, hc⟩ := (Trace.upTo_callAt tr).mp hc
    exact ⟨h.awake_of_call y i ℓ (anti hid hy) hc, hid⟩
  · obtain ⟨hid, hc⟩ := (Trace.upTo_callAt tr).mp hc
    exact h.restart_of_sleep y i ℓ u (anti hid hy) hc hu hui (fun ha => hs ⟨ha, hui.le.trans hid⟩)
      fun j hj ℓ' hcj => hb j hj ℓ' (hcall ((hm hj.le).trans hid) hcj)
  · obtain ⟨hv, hvd⟩ := hv
    obtain ⟨k, ⟨ℓ, hk, hr⟩, huk, hkv⟩ := h.restart_at_wake y u v (anti hvd hy) hu huv
      (fun ha => hs ⟨ha, huv.le.trans hvd⟩) hv
    exact ⟨k, ⟨ℓ, hcall (hkv.trans hvd) hk, hr⟩, huk, hkv⟩
  · obtain ⟨hid, hc⟩ := (Trace.upTo_callAt tr).mp hc
    obtain ⟨u, hu, hui, hs, hb⟩ := h.sleep_of_restart y i ℓ (anti hid hy) hc hr
    exact ⟨u, hu, hui, fun ha => hs ha.1,
      fun j hj ℓ' hcj => hb j hj ℓ' ((Trace.upTo_callAt tr).mp hcj).2⟩

end Growing

end Consensus.Goldilocks

end
