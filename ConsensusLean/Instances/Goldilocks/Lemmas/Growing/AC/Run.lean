module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Components
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC

public section

/-! # Retention of the SA run contract

The retained run keeps `U`. Its honest-object laws use the original laws at retained calls;
pool provenance is reconstructed through those calls, including the final frozen state.
-/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {proposer : Nat → Fin sp.n}

/-- The prefix is an SA run for the validators still honest at its horizon, in the same `U`. -/
theorem ACRun.upTo {ini} (h : ACRun proposer tr H U ini) {d : Time} (hd : 0 ≤ d) :
    SA.ACRun proposer (tr.upTo d) (H d) U ini := by
  have hr := h.localRun.upTo hd
  have hm := h.localRun.time_mono
  have anti : ∀ {t}, t ≤ d → H d ⊆ H t := fun ht => h.localRun.antitone ht
  have pool : ∀ y ∈ H d, ∀ i σ, ∀ v ∈ ((tr.upTo d).state y i).pool σ,
      v.val ∈ H d → ∃ j < i, ∃ e, VoteAt (tr.upTo d) v.val j e ∧ e.msg = v := by
    intro y hy i
    induction i with
    | zero =>
      intro σ v hv _
      change v ∈ ((tr.upTo d).init y).pool σ at hv
      rw [hr.init y hy, (h.vstart y).pool σ] at hv
      simp at hv
    | succ i ih =>
      intro σ v hv hvH
      by_cases hn : (tr.upTo d).node i = y ∧ (tr.upTo d).label i ≠ none
      · obtain ⟨ℓ, hl⟩ := Option.ne_none_iff_exists'.mp hn.2
        have hc : (tr.upTo d).CallAt y i ℓ := ⟨hn.1, hl⟩
        obtain ⟨hid, hc₀⟩ := (Trace.upTo_callAt tr).mp hc
        have hy₀ := anti hid hy
        have he := hr.exec i ℓ hl (hn.1 ▸ hy)
        rw [hn.1] at he
        rw [state_succ_of_call hc] at hv
        have hΦ : FrameOK ℓ.frame := by
          rcases hr.frameLaw y hy i ℓ hc with ⟨_, _, _, _, hok⟩ | ⟨_, _, _, _, _, hok⟩ <;>
            exact hok.1.1
        have hslot : v.slot = σ := by
          have hv' := hv
          rw [← state_succ_of_call hc] at hv'
          exact state_pool_slot_from sp hr h.vstart hy (i + 1) σ v hv'
        by_cases hrs : ℓ.call = .restart
        · have hR := restart_state sp FGP ro y ((tr.upTo d).state y i) ℓ.frame
            ((tr.upTo d).time i) hΦ (hr.time_nonneg i)
          rw [hrs] at he
          change acRestart sp ro y ((tr.upTo d).state y i) ℓ.frame ((tr.upTo d).time i) = _ at he
          rw [he] at hR
          obtain ⟨_, B, hB, hvB⟩ := hR.2.2.2.2.2.2.2.2.1 σ v hv
          obtain ⟨j, hj, e, hvote, hev⟩ := h.honest.carried_vote y i ℓ hy₀ hc₀ B hB v hvB
            (anti hid hvH)
          exact ⟨j, hj.trans (Nat.lt_succ_self i), e,
            upTo_voteAt.mpr ⟨(hm hj.le).trans hid, hvote⟩, hev⟩
        · by_cases hold : v ∈ ((tr.upTo d).state y i).pool v.slot
          · obtain ⟨j, hj, e, hvote, hev⟩ := ih v.slot v hold hvH
            exact ⟨j, hj.trans (Nat.lt_succ_self i), e, hvote, hev⟩
          · have hnew : v ∈ ((goldilocksSA sp FGP ro).step y ((tr.upTo d).state y i)
                ℓ.frame ((tr.upTo d).time i) ℓ.call).1.pool v.slot := by
              rw [he, hslot]
              exact hv
            rcases Compose.step_pool_insertion_source y _ _ _ _ hrs v hold hnew with
              hm | ⟨B, hb, hvB⟩ | ⟨e, hem, hev⟩
            · obtain ⟨j, hj, e, hvote, hev⟩ := h.honest.message_vote y i ℓ v hy₀ hc₀ hm
                (anti hid hvH)
              exact ⟨j, hj.trans (Nat.lt_succ_self i), e,
                upTo_voteAt.mpr ⟨(h.localRun.time_mono hj.le).trans hid, hvote⟩, hev⟩
            · obtain ⟨j, hj, e, hvote, hev⟩ := h.honest.carried_vote y i ℓ hy₀ hc₀ B
                ((accept_new sp hr hy ⟨ℓ, hc, hb⟩).1 ℓ hc) v hvB (anti hid hvH)
              exact ⟨j, hj.trans (Nat.lt_succ_self i), e,
                upTo_voteAt.mpr ⟨(h.localRun.time_mono hj.le).trans hid, hvote⟩, hev⟩
            · rw [he] at hem
              have hvote : VoteAt (tr.upTo d) y i e := ⟨ℓ, hc, hem⟩
              have hval := (castAt_spec hr hy ⟨hc, hem⟩).1
              exact ⟨i, Nat.lt_succ_self i, e, (hev ▸ hval) ▸ hvote, hev⟩
      · have hs : (tr.upTo d).state y (i + 1) = (tr.upTo d).state y i := by
          simp only [Trace.state, ite_eq_right hn]
        rw [hs] at hv
        obtain ⟨j, hj, e, hvote, hev⟩ := ih σ v hv hvH
        exact ⟨j, hj.trans (Nat.lt_succ_self i), e, hvote, hev⟩
  refine ⟨h.stock, hr, ⟨pool, ?_, ?_, ?_, ?_⟩, h.vstart⟩
  · intro y hy i ℓ v hc hl hvH
    obtain ⟨hid, hc⟩ := (Trace.upTo_callAt tr).mp hc
    obtain ⟨j, hj, e, hvote, hev⟩ := h.honest.message_vote y i ℓ v (anti hid hy) hc hl
      (anti hid hvH)
    exact ⟨j, hj, e, upTo_voteAt.mpr ⟨(hm hj.le).trans hid, hvote⟩, hev⟩
  · intro y hy i ℓ hc B hB v hv hvH
    obtain ⟨hid, hc⟩ := (Trace.upTo_callAt tr).mp hc
    obtain ⟨j, hj, e, hvote, hev⟩ := h.honest.carried_vote y i ℓ (anti hid hy) hc B hB v hv
      (anti hid hvH)
    exact ⟨j, hj, e, upTo_voteAt.mpr ⟨(hm hj.le).trans hid, hvote⟩, hev⟩
  · rintro B ⟨y, hy, i, ℓ, hc, hB⟩ hg
    obtain ⟨hid, hc⟩ := (Trace.upTo_callAt tr).mp hc
    exact h.honest.proposer B ⟨y, i, ℓ, anti hid hy, hc, hB⟩ hg
  · rintro B B' ⟨y, hy, i, ℓ, hc, hB⟩ ⟨y', hy', i', ℓ', hc', hB'⟩ hp hpp hs
    obtain ⟨hid, hc⟩ := (Trace.upTo_callAt tr).mp hc
    obtain ⟨hid', hc'⟩ := (Trace.upTo_callAt tr).mp hc'
    exact h.honest.one_block_before h.localRun.antitone (anti hid hy) hc hB hid
      (anti hid' hy') hc' hB' hid' hp hpp hs

end Consensus.Goldilocks.SA.Growing

end
