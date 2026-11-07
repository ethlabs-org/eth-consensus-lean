module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Base
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes

public section

/-! # Next transfer with participation counted at the vote

The counted votes must have been cast while honest. Their earlier slot then puts them before
the consuming vote, and retention preserves the participation count exactly.
-/

namespace Consensus.Goldilocks.SA.Growing

theorem next_transfer (sp : SAParams) : NextTransfer sp := by
  intro FGP ro H U tr proposer hrun m y i B ℓ e hy hc hs hall hhalf hcarry hf hviab hearlier
  have hr := hrun.localRun
  have hm := hr.time_mono
  have hry := hrun.upTo (hr.time_nonneg i)
  have hc' := upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hslot : e.msg.slot = sp.slot (tr.time i) := (castAt_spec hry.localRun hy hc').2.1
  have before : ∀ {x j e'}, x ∈ H (tr.time j) → VoteAt tr x j e' → e'.msg.slot = m → j < i := by
    intro x j e' hx hv hvs
    obtain ⟨ℓ', hv⟩ := hv
    have hs' : e'.msg.slot = sp.slot (tr.time j) := (castAt_spec (hr.upTo (hr.time_nonneg j)) hx
      (upTo_castAt.mpr ⟨le_rfl, hv⟩)).2.1
    by_contra h
    have hmono := slot_mono sp (hr.time_nonneg i) (hm (Nat.le_of_not_gt h))
    rw [← hslot, ← hs', hvs, hs] at hmono
    omega
  have hbefore : sp.ts m + 3 * sp.Δ ≤ tr.time i := by
    have h := (ts_le_iff_le_slot sp (hr.time_nonneg i) (m + 1 : Nat)).mpr
      (by rw [← hslot, hs])
    simp only [SAParams.ts] at h ⊢
    push_cast at h
    have := sp.toParams.hΔ
    nlinarith
  have hbatch : {x | x ∈ H (tr.time i) ∧ ∃ j e', x ∈ H (tr.time j) ∧
      VoteAt tr x j e' ∧ e'.msg.slot = m} =
      {x | x ∈ H (tr.time i) ∧ ∃ j e', VoteAt (tr.upTo (tr.time i)) x j e' ∧
        e'.msg.slot = m} := by
    ext x
    constructor
    · rintro ⟨hx, j, e', hxj, hv, hvs⟩
      exact ⟨hx, j, e', upTo_voteAt.mpr ⟨hm (before hxj hv hvs).le, hv⟩, hvs⟩
    · rintro ⟨hx, j, e', hv, hvs⟩
      obtain ⟨hji, hv⟩ := upTo_voteAt.mp hv
      exact ⟨hx, j, e', hr.antitone hji hx, hv, hvs⟩
  rw [hbatch] at hhalf
  apply SA.next_transfer_of_carry sp hry hy hc' hs
  · intro x hx j e' hv hvs
    obtain ⟨hji, hv⟩ := upTo_voteAt.mp hv
    exact hall x j e' (hr.antitone hji hx) hv hvs
  · exact hhalf
  · have h := carryAt_upTo (d := tr.time i) le_rfl hbefore hcarry
    refine ⟨h.awake, h.joined, ?_, ?_⟩
    · rintro v ⟨x, hx, j, e', hv, he, hvs⟩
      obtain ⟨hji, hv⟩ := upTo_voteAt.mp hv
      exact h.heads v ⟨x, j, e', hr.antitone hji hx, hv, he, hvs⟩
    · rintro v ⟨x, hx, j, e', hv, he, hvs⟩
      obtain ⟨hji, hv⟩ := upTo_voteAt.mp hv
      exact h.holds v ⟨x, j, e', hr.antitone hji hx, hv, he, hvs⟩
  · have hcount : honestAwakeJoined (tr.upTo (tr.time i)) (H (tr.time i)) (tr.time i) =
        {x | x ∈ H (tr.time i) ∧ tr.awake x (tr.time i) ∧ JoinedAt tr x (tr.time i)}.ncard := by
      unfold honestAwakeJoined
      congr 1
      ext x
      simp only [Trace.upTo_awake, upTo_joinedAt le_rfl, le_refl, and_true]
    change (H (tr.time i))ᶜ.ncard < honestAwakeJoined (tr.upTo (tr.time i)) _ (tr.time i)
    rw [hcount]
    exact hf
  · exact hviab
  · intro x hx j hji e' hv hvs
    obtain ⟨hjt, hv⟩ := upTo_voteAt.mp hv
    exact hearlier x j hji (hr.antitone hjt hx) e' hv hvs

end Consensus.Goldilocks.SA.Growing

end
