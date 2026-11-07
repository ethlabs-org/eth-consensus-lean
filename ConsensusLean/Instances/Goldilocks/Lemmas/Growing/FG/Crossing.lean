module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.FG.Service

public section

/-! # FG crossing at independently honest proposal and observation cuts -/

namespace Consensus.Goldilocks.Store.Growing

/-- G1.8(a): the observing node and each proposal need honesty only at their own cuts. -/
theorem crossing (P : Params) (ACP : Type) : Crossing P ACP := by
  intro acp₀ H U tr hr y k C T g r hy hC hT hTC _ _ hCs hw
  let rt := tr.upTo (tr.time k)
  have rr := hr.upTo (hr.time_nonneg k)
  have hs : FGTrace.store rt y k = tr.store y k := by
    exact congrArg Prod.fst (Trace.upTo_state tr y (fun l hl => hr.time_mono hl.le))
  have coh : Coherent (tr.store y k).tree := by
    rw [← hs]
    exact rr.coherent.mono (rr.tree_subset y hy k)
  have step : ∀ {W : NodeBlock P ACP} {pr}, W ∈ (tr.store y k).tree → W.parent = some pr →
      P.fg.stateTransition ((tr.store y k).σ pr) W.fgView = some ((tr.store y k).σ W.root) := by
    intro W pr hW hp
    rw [← hs] at hW ⊢
    exact Store.step_σ rr hy hW hp
  have height : ∀ {A W : NodeBlock P ACP}, (tr.store y k).Anc A W →
      ((tr.store y k).σ A.root).h ≤ ((tr.store y k).σ W.root).h ∧
      (((tr.store y k).σ W.root).h = ((tr.store y k).σ A.root).h →
        ((tr.store y k).σ W.root).Th = ((tr.store y k).σ A.root).Th ∧
        ((tr.store y k).σ A.root).prog ⊆ ((tr.store y k).σ W.root).prog) := by
    intro A W h
    rw [← hs] at h ⊢
    exact Store.anc_h rr hy h
  have parent_height : ∀ {E E' : NodeBlock P ACP}, ((tr.store y k).σ E.root).Th = E.root →
      ParentIn (tr.store y k).tree E' E →
      ((tr.store y k).σ E'.root).h < ((tr.store y k).σ E.root).h := by
    intro E E' h hp
    rw [← hs] at h hp ⊢
    exact Store.entry_parent rr hy h hp
  have row : ∀ {W : NodeBlock P ACP} {x : FG.Att P.n}, W ∈ (tr.store y k).tree →
      x ∈ W.fgPayload → ∃ W', ParentIn (tr.store y k).tree W' W ∧
        x.h ≤ ((tr.store y k).σ W'.root).h := by
    intro W x hW hx
    rw [← hs] at hW ⊢
    exact Store.row_parent rr hy hW hx
  have hM := le_max_left P.δt r
  have hM' := le_max_right P.δt r
  obtain ⟨Y, Pr, p, j, hP, hYC, hwY, hYw, hq⟩ := hw (T.slot + max P.δt r) (by omega) (by omega)
  have hq' := hq (by omega)
  have hYt : Y ∈ (tr.store y k).tree := by
    by_cases hYC' : Y = C
    exacts [hYC' ▸ hC, (Goldilocks.Anc.mem hYC hYC').1]
  have hTY : (tr.store y k).Anc T Y := by
    rcases Goldilocks.Anc.total coh hTC hYC with h | h
    · exact h
    · have := (Goldilocks.Anc.slot_le coh h).1
      omega
  have hTne : Y ≠ T := by rintro rfl; omega
  obtain ⟨Pr', hTPr, hPrY⟩ := hTY.cases_tail.resolve_left hTne
  obtain ⟨hpH, -, -, -, hPrp, hYpar, hP5⟩ := hP
  have he : Pr' = Pr := hr.coherent.1
    (hr.tree_subset y k (tr.time k) (hr.time_nonneg k) (fun l hl => hr.time_mono hl.le) hy hPrY.1)
    (hr.tree_subset p j (tr.time j) (hr.time_nonneg j) (fun l hl => hr.time_mono hl.le) hpH hPrp)
    (Option.some.inj (hPrY.2.2.symm.trans hYpar))
  rw [he] at hTPr hPrY
  have hPrt := hPrY.1
  have hle := height hTPr
  by_cases hPh : ((tr.store y k).σ Pr.root).h = ((tr.store y k).σ T.root).h
  swap
  · have := (Goldilocks.Anc.slot_le coh (.single hPrY)).1
    exact ⟨Pr, hPrt, hTPr, (Relation.ReflTransGen.single hPrY).trans hYC, by omega, by omega⟩
  refine ⟨Y, hYt, hTY, hYC, ?_, by omega⟩
  have hPrTh : ((tr.store y k).σ Pr.root).Th = T.root := (hle.2 hPh).1.trans hT.2
  have es := Store.entry_slot rr hy (hs ▸ hPrt)
  rw [hs] at es
  obtain ⟨E, hE, hEr, hEs⟩ := es
  rw [coh.1 hE hT.1 (hEr.trans hPrTh)] at hEs
  have transfer : ∀ {A B : NodeBlock P ACP}, (tr.store p j).Anc A B →
      B ∈ (tr.store y k).tree → (tr.store y k).Anc A B := by
    intro A B h hB
    exact anc_transfer hr (hr.time_nonneg j) (hr.time_nonneg k) hpH hy
      (fun l hl => hr.time_mono hl.le) (fun l hl => hr.time_mono hl.le) h hB
  have hrows : ∀ x ∈ (tr.store p j).atts, x.h = ((tr.store y k).σ T.root).h → x.T = T.root →
      x.val ∈ ((tr.store y k).σ Pr.root).prog ∨ ∃ a ∈ Y.fgPayload, a.val = x.val ∧
        a.h = ((tr.store y k).σ Pr.root).h ∧ a.T = ((tr.store y k).σ Pr.root).Th := by
    intro x hx hxh hxT
    by_cases hon : (tr.store p j).OnChain Pr x
    · left
      obtain ⟨X, -, hXPr, hxX⟩ := hon
      have hXPr' := transfer hXPr hPrt
      have hXt : X ∈ (tr.store y k).tree := by
        by_cases hXe : X = Pr
        exacts [hXe ▸ hPrt, (Goldilocks.Anc.mem hXPr' hXe).1]
      obtain ⟨X', hX'X, hxX'⟩ := row hXt hxX
      rcases Goldilocks.Anc.total coh hXPr' hTPr with hXT | hTX
      · exfalso
        rcases (Relation.ReflTransGen.head hX'X hXT).cases_tail with rfl | ⟨T', hX'T', hT'T⟩
        · have := (Goldilocks.Anc.slot_le coh hXT).1
          have := coh.2 _ hX'X.1 _ hX'X.2.1 hX'X.2.2
          omega
        · have := (height hX'T').1
          have := parent_height hT.2 hT'T
          omega
      have hTX' : (tr.store y k).Anc T X' := by
        rcases hTX.cases_tail with rfl | ⟨Z, hTZ, hZX⟩
        · have := parent_height hT.2 hX'X
          omega
        · obtain rfl : Z = X' :=
            coh.1 hZX.1 hX'X.1 (Option.some.inj (hZX.2.2.symm.trans hX'X.2.2))
          exact hTZ
      have h1 := height hTX'
      have h2 := (height ((Relation.ReflTransGen.single hX'X).trans hXPr')).1
      have hX'h : ((tr.store y k).σ X'.root).h = ((tr.store y k).σ T.root).h := by omega
      have hX'T := (h1.2 hX'h).1
      have h3 := height hXPr'
      rcases Store.step_entry (step hX'X.2.1 hX'X.2.2) with ⟨hh, -, -, hp, -⟩ | ⟨hh, -, -⟩
      · exact (h3.2 (by omega)).2 (hp _ (Or.inr ⟨x, hxX, rfl, by omega,
          hxT.trans (hT.2.symm.trans hX'T.symm)⟩))
      · omega
    · right
      have hv : ((tr.store p j).σ Pr.root).validAtt x := by
        rw [σ_eq_of_held hr (hr.time_nonneg j) (hr.time_nonneg k) hpH hy
          (fun l hl => hr.time_mono hl.le) (fun l hl => hr.time_mono hl.le) hPrp hPrt]
        exact Or.inl ⟨by omega, hxT.trans hPrTh.symm⟩
      exact ⟨x, hP5 x hx hv hon, rfl, by omega, hxT.trans hPrTh.symm⟩
  rcases Store.step_entry (step hYt hYpar) with ⟨-, -, -, hp, hto⟩ | ⟨hh, -, -⟩
  · refine absurd ⟨le_trans hq' (Finset.card_le_card fun v hv => ?_), ?_⟩ hto
    · simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at hv
      obtain ⟨x, ⟨hx, hxh, hxT⟩, rfl⟩ := hv
      exact hp _ (hrows x hx hxh hxT)
    · change ((tr.store y k).σ Pr.root).ThSlot + P.δt ≤ Y.slot
      omega
  · omega

end Consensus.Goldilocks.Store.Growing

end
