module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents

public section

/-! # Counted result supporters at a later independently honest vote -/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {proposer : Nat → Fin sp.n}

/-- Carrying a result carries support for each ancestor of that result. -/
theorem counted_ancestor_supporters (hrun : ACRun proposer tr H U)
    {X y : Fin sp.n} {i₀ i s : Nat} (hX : X ∈ H (tr.time i₀)) (hy : y ∈ H (tr.time i))
    {B C : Blk sp.n FGP} {ℓX ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hcX : tr.CallAt X i₀ ℓX) (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hBC : Anc U B C)
    (hcarry : CarryAt tr U y i e s (fastCounted sp (tr.state X i₀) ℓX.frame s C))
    (hviab : ViableAtVote ℓ e (s + 1) B)
    (hd : ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s}) :
    {w | ∃ v ∈ fastCounted sp (tr.state X i₀) ℓX.frame s C, v.val = w} ⊆
      supporters ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s B := by
  have hrX := hrun.localRun.upTo (hrun.localRun.time_nonneg i₀)
  have hry := hrun.upTo (hrun.localRun.time_nonneg i)
  have hcX' := (Trace.upTo_callAt tr).mpr ⟨le_rfl, hcX⟩
  have hc' := upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hU := hrun.localRun.coherent
  obtain ⟨hΦX, hΦXU⟩ := frameIn_of_call hrX hX hcX'
  obtain ⟨hΦ, _⟩ := frameIn_of_call hry.localRun hy hc'.1
  have hCt : B ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact mem_of_anc h hΦ.fcRoot_mem
  have hone : ∀ w ∉ equivocators {x | x ∈ (tr.state X i₀).pool s}, ∀ v₁ v₂,
      v₁ ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes →
      v₂ ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes →
      v₁.val = w → v₂.val = w → v₁ = v₂ := by
    intro w hw v₁ v₂ h₁ h₂ hv₁ hv₂
    by_contra hne
    rcases hd v₁ h₁ (merged_vote_slot hry.localRun hy hc' v₁ h₁) with h₁' | h₁'
    · rcases hd v₂ h₂ (merged_vote_slot hry.localRun hy hc' v₂ h₂) with h₂' | h₂'
      · exact hw ⟨v₁, h₁', v₂, h₂', hne, hv₁, hv₂⟩
      · exact hw (hv₂ ▸ h₂')
    · exact hw (hv₁ ▸ h₁')
  rintro w ⟨v, ⟨hvp, hvw, hvres, hvanc⟩, rfl⟩
  have hst := Trace.upTo_state tr X (d := tr.time i₀) (i := i₀)
    (fun _ hk => hrun.localRun.time_mono hk.le)
  have hvp' : v ∈ ((tr.upTo (tr.time i₀)).state X i₀).pool s := hst.symm ▸ hvp
  have hvs := state_pool_slot sp hrX hX i₀ s v hvp'
  obtain ⟨Hd, hHd, hHdr, hHds⟩ : ∃ Hd ∈ ℓX.frame.tree, Hd.root = v.head ∧ Hd.slot ≤ v.slot := by
    unfold resolutionTime at hvres
    split at hvres
    · exact absurd hvres (by simp [ETime.of])
    · rename_i Hd hl
      obtain ⟨hHd, hHdr⟩ := lookup_eq_some hl
      split_ifs at hvres with hlt
      · exact absurd hvres (by simp [ETime.of])
      · exact ⟨Hd, hHd, hHdr, Nat.le_of_not_lt hlt⟩
  have hCHd : Anc U C Hd := by
    obtain ⟨R, hR, hRr, hCR⟩ := hvanc
    obtain rfl : R = Hd := hU.1 (hΦXU hR) (hΦXU hHd) (hRr.trans hHdr.symm)
    exact Anc.mono hΦXU hCR
  have hheld : HeldBefore e.readPoint v (sp.ts s + 3 * sp.Δ) := by
    rcases hcarry.holds v ⟨hvp, hvw, hvres, hvanc⟩ with h |
      ⟨v₁, v₂, h12, _, _, hv₁, hv₂, hs₁, hs₂, hh₁, hh₂⟩
    · exact h
    · exfalso
      have hm : ∀ u, u.slot = s → HeldBefore e.readPoint u (sp.ts s + 3 * sp.Δ) →
          u ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes := by
        intro u hus hu
        refine Or.inl (List.mem_filter.mpr ⟨?_, ?_⟩)
        · simp only [SAState.poolAt, show ¬ (((s + 1 : Nat) : Int) - 1 < 0) by omega, ite_false]
          simpa [hus] using hu.1
        · simpa [freeze] using hu.2
      exact h12 (hone _ hvw v₁ v₂ (hm v₁ hs₁ hh₁) (hm v₂ hs₂ hh₂) hv₁ hv₂)
  obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads v ⟨hvp, hvw, hvres, hvanc⟩
  have hEq : Hd = Hv := hU.1 (hΦXU hHd) hHv (hHdr.trans hHvr.symm)
  subst Hd
  have hacc' : AcceptedBefore (tr.upTo (tr.time i)) y Hv (sp.ts s + 3 * sp.Δ) := by
    have hT : sp.ts s + 3 * sp.Δ < tr.time i := by
      have hslot : e.msg.slot = sp.slot (tr.time i) := (castAt_spec hry.localRun hy hc').2.1
      have h := (ts_le_iff_le_slot sp (hrun.localRun.time_nonneg i) ((s : Int) + 1)).mpr
        (by rw [← hslot, hs]; push_cast; rfl)
      have hΔ := sp.toParams.hΔ
      simp only [SAParams.ts] at h ⊢
      linarith
    rcases hacc Hv Relation.ReflTransGen.refl with hg | ⟨k, hk, ht⟩
    · exact Or.inl hg
    · exact Or.inr ⟨k, (ACTrace.upTo_acceptAt (A := goldilocksSA sp FGP ro)).mpr
        ⟨ht.le.trans hT.le, hk⟩, ht⟩
  refine carried_supporter hry hy hc' hs hCt hvs hheld
    ⟨Hv, hHv, hHvr, hvs ▸ hHds, hBC.trans hCHd, hacc'⟩ fun hq => ?_
  obtain ⟨x, hx, x', hx', hne, hxv, hx'v⟩ := hq
  exact hne (hone _ hvw x x' hx hx' hxv hx'v)

end Consensus.Goldilocks.SA.Growing

end
