module
public import ConsensusLean.Instances.Goldilocks.Statements.AC.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Count
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock

public section

/-! # Goldilocks SA: the step lemmas (A1.1–A1.5, A1.8, A1.9)

The per-vote transfer lemmas over SA traces. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- **A1.2.** -/
theorem first_transfer : FirstTransfer sp := by
  sorry

/-- **A1.3.** -/
theorem next_transfer : NextTransfer sp := by
  intro FGP ro H U tr hrun m y i B ℓ e hy hc hs hall hhalf hcarry hfault hsync hviab hearlier
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨-, -, -, hhead⟩ := castAt_spec hr hy hc
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
    rcases hr.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
      exact h.1
  have hσ : ((m + 1 : Nat) : Int) - 1 = (m : Int) := by push_cast; ring
  rw [hs, hσ] at hhead
  have hdomA := voterBlockTree_anc hr hy hc
  rw [hs] at hdomA
  have hBt : B ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact mem_of_anc h hΦ.fcRoot_mem
  -- the honest voters of slot `m` are supporters of `B` at `y`
  set SX : Set (Fin sp.n) := {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = m}
  have hsupp : SX ⊆ supporters ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame (m + 1)) m B := by
    rintro w ⟨hw, j, e', hv, hvs⟩
    obtain ⟨ℓw, hcw⟩ := id hv
    have hvw : e'.msg.val = w := (castAt_spec hr hw hcw).1
    have hmem : e'.msg ∈ {v | ∃ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = m} :=
      ⟨w, hw, j, e', hv, rfl, hvs⟩
    -- `y` holds `e'.msg` itself (an honest validator has one slot-`m` vote)
    have hheld : HeldBefore e.readPoint e'.msg (sp.ts m + 3 * sp.Δ) := by
      rcases hcarry.holds _ hmem with h | ⟨v₁, v₂, h12, h1, h2, hv₁, hv₂, hs₁, hs₂, hh₁, hh₂⟩
      · exact h
      · exfalso
        have hm : ∀ u, u.slot = m → HeldBefore e.readPoint u (sp.ts m + 3 * sp.Δ) →
            u ∈ (mergedVoteView sp e.readPoint ℓ.frame (m + 1)).votes := by
          intro u hus hu
          refine Or.inl (List.mem_filter.2 ⟨?_, ?_⟩)
          · simp only [SAState.poolAt, show ¬ (((m + 1 : Nat) : Int) - 1 < 0) by omega, ite_false]
            simpa [hus] using hu.1
          · simpa [freeze] using hu.2
        obtain ⟨j₁, -, e₁, hv₁', he₁⟩ :=
          honest_merged_vote hrun hy hc (hm v₁ hs₁ hh₁) (hv₁.trans hvw ▸ hw)
        have := (one_vote_per_slot sp) FGP ro H U tr hr w hw j₁ j e₁ e'
          (hv₁.trans hvw ▸ hv₁') hv (by rw [he₁, hs₁, hvs])
        exact h1 (he₁ ▸ this.2 ▸ rfl)
    obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads _ hmem
    obtain ⟨Hd, hHd, hHdr, hHds⟩ := honest_head hrun hw hv
    obtain ⟨Hd', hHd', hHd'r, hBHd'⟩ := hall w hw j e' hv hvs
    have h1 : Hd = Hv := hU.1 hHd hHv (hHdr.trans hHvr.symm)
    have h2 : Hd' = Hv := hU.1 hHd' hHv (hHd'r.trans hHvr.symm)
    have := carried_supporter hrun hy hc hs hBt hvs hheld
      ⟨Hv, hHv, hHvr, h1 ▸ hvs ▸ hHds, h2 ▸ hBHd', hacc Hv Relation.ReflTransGen.refl⟩
      (honest_not_equivocator hrun hy hc (hvw ▸ hw))
    exact hvw ▸ this
  -- counting: the voters at `y` are honest slot-`m` voters or faulty, and `f < |SX|`
  have hHle : SX.ncard ≤ H.ncard := Set.ncard_le_ncard fun x hx => hx.1
  have hhonest : honestAwakeJoined tr H (tr.time i) ≤ H.ncard :=
    Set.ncard_le_ncard fun x hx => hx.1
  have hfault' : Hᶜ.ncard < H.ncard := lt_of_lt_of_le hfault hhonest
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hvoters : voters (mergedVoteView sp e.readPoint ℓ.frame (m + 1)).votes ⊆ SX ∪ Hᶜ := by
    rintro w ⟨v, hv, rfl⟩
    by_cases hw : v.val ∈ H
    · obtain ⟨j, -, e', hv', he'⟩ := honest_merged_vote hrun hy hc hv hw
      exact Or.inl ⟨hw, j, e', hv', by rw [he']; exact merged_vote_slot hr hy hc v hv⟩
    · exact Or.inr hw
  have h3 : (SX ∪ Hᶜ).ncard < 2 * SX.ncard := by
    have := Set.ncard_union_le SX Hᶜ
    omega
  have hcore := anc_getHead hU hΦ hΦU e.readPoint (tr.time i)
    (mergedVoteView sp e.readPoint ℓ.frame (m + 1)) (m : Int) (fun B hB => hB.1) hdomA hviab
    (locks_compatible_next hrun hy hc hs hBt hall
      (S := SX) (fun w hw => by
        obtain ⟨-, x, hx, hxv, hxs, hxa⟩ := hsupp hw
        exact ⟨x, hx, hxv, by exact_mod_cast hxs, hxa⟩)
      hhalf (by omega) hearlier)
    fun X' Cx hCx hp hCxC =>
      isBest_of_majority hΦ (merged_support_subset hr hy hc (m + 1)) (fun B hB => hB.1.1)
        hsupp hvoters h3 hCx hp hCxC
  refine ⟨_, hΦU ?_, hhead.symm, Anc.mono hΦU hcore⟩
  by_cases he : B = getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame (m + 1)))
      (mergedVoteView sp e.readPoint ℓ.frame (m + 1)) (m : Int)
  · exact he ▸ hBt
  · exact (Anc.mem hcore he).2

/-- **A1.4 (a).** -/
theorem optimistic_transfer : OptimisticTransfer sp := by
  sorry

/-- **A1.4 (b).** -/
theorem optimistic_next_update : OptimisticNextUpdate sp := by
  sorry

/-- A block that `ac_to_fg` returns is a candidate. -/
private theorem mem_toFGCandidates {FGP : Type} {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {C : Blk sp.n FGP} (h : (acToFG sp A Φ t).2.1 = some C) : C ∈ toFGCandidates sp A Φ t := by
  unfold acToFG at h
  dsimp only at h
  split_ifs at h
  split at h
  · cases h
  · rename_i C' hC'
    split_ifs at h
    cases h
    exact (deepest_mem hC').1

/-- **A1.5.** -/
theorem source_age : SourceAge sp := by
  intro FGP ro H U tr hrun τ x i ℓ C hx hto hslot
  obtain ⟨hc, -, hC⟩ := hto
  obtain ⟨hCv, l, hl, hlb, hlf, hls⟩ := mem_toFGCandidates sp hC
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩ := hl
  obtain ⟨j, hj, B', CV', hfl, L, hL, hLr, hLB'⟩ :=
    fast_lock_provenance hrun.localRun hx i l₀ hl₀ hlf
  have hU := hrun.localRun.coherent
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
    rcases hrun.localRun.frameLaw x hx i ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
      exact h.1
  refine ⟨j, hj.le, l₀.slot, B', CV', hfl, ?_, hls, ?_⟩
  · -- the lock was written in a slot after `τ`'s
    have h1 : sp.slot τ + 1 ≤ l₀.slot := by simp only at hls; omega
    have hτ : τ < sp.ts (l₀.slot : Int) := by
      rcases le_or_gt 0 τ with h0 | h0
      · refine lt_of_lt_of_le (not_le.1 fun h => ?_)
          ((ts_le_iff sp (a := (sp.slot τ : Int) + 1) (b := l₀.slot)).2 (by omega))
        have := ((ts_le_iff_le_slot sp h0) _).1 h
        omega
      · refine lt_of_lt_of_le h0 ?_
        simp only [SAParams.ts]
        have := sp.toParams.hΔ
        positivity
    rcases hfl with ⟨ℓ', C', ⟨-, -, ht, -⟩, -⟩ | ⟨ℓ', A', -, hs, -⟩
    · rw [ht]
      have := sp.toParams.hΔ
      linarith
    · refine lt_of_lt_of_le hτ ?_
      rw [← hs]
      exact ((ts_le_iff_le_slot sp (hrun.localRun.time_nonneg j)) _).2 le_rfl
  · -- `C` is the viable ancestor of the lock's block, which is `L`
    have hCt : C ∈ ℓ.frame.tree := hCv.1
    have hva : Anc ℓ.frame.tree (ℓ.frame.viableAncestor B₀) B₀ := by
      unfold Frame.viableAncestor
      split
      · rename_i h
        exact h.choose_spec.1
      · exact Relation.ReflTransGen.refl
    have hvat : ℓ.frame.viableAncestor B₀ ∈ ℓ.frame.tree := by
      by_cases he : ℓ.frame.viableAncestor B₀ = B₀
      · rw [he]; exact hB₀
      · exact (Anc.mem hva he).1
    have hCe : C = ℓ.frame.viableAncestor B₀ := hU.1 (hΦU hCt) (hΦU hvat) hlb.symm
    have hLe : L = B₀ := hU.1 hL (hΦU hB₀) (hLr.trans hB₀r.symm)
    subst hCe hLe
    exact (Anc.mono hΦU hva).trans hLB'

/-- **A1.8.** -/
theorem result_transfer : ResultTransfer sp := by
  intro FGP ro H U tr hrun s X y i₀ i C CV ℓ e hX hres hy hc hs hcarry hviab hlocks hd
  obtain ⟨-, -, -, hhead⟩ := castAt_spec hrun.localRun hy hc
  have hU := hrun.localRun.coherent
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
    rcases hrun.localRun.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
      exact h.1
  have hσ : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  rw [hs, hσ] at hhead
  have hdomA := voterBlockTree_anc hrun.localRun hy hc
  rw [hs] at hdomA
  have hCt : C ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact mem_of_anc h hΦ.fcRoot_mem
  have hcore := anc_getHead hU hΦ hΦU e.readPoint (tr.time i)
    (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int) (fun B hB => hB.1) hdomA hviab
    (fun L hL => hlocks L hL) fun X' Cx hCx hp hCxC =>
      isBest_of_majority hΦ (merged_support_subset hrun.localRun hy hc (s + 1))
        (fun B hB => hB.1.1)
        (result_supporters hrun hX hy hres hc hs hcarry hviab hd)
        (merged_voters_subset hrun.localRun hy hc hd)
        (result_majority hres) hCx hp hCxC
  refine ⟨_, hΦU ?_, hhead.symm, Anc.mono hΦU hcore⟩
  by_cases he : C = getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame (s + 1)))
      (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int)
  · exact he ▸ hCt
  · exact (Anc.mem hcore he).2


end Consensus.Goldilocks.SA

end
