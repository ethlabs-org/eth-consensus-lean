module
public import AvailableChainSimplexFG
public import AvailableChainKitFG.Correspondence
public import AvailableChainKitFG.Provenance

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

/-! # `fj.inBandLock.v1`: no lock stall for an in-band source

r148 (`fj-redteam.md`, lines 577–597). The contradiction does not use the
record Λ. It uses only a carrier K in the full view with `h_j(K) = m` and
`J.root = J'`. Both lock sources (a lock `Λ.lock[m] = J'` and a same-action
finality pair) give such a carrier. Thus the statement is positive: C's entry
at m is J'.

In the pinned text, "finalized crossing" is `fg.finalLock.v1`, and "same-height
justification uniqueness" is `fg.uniqueJust.v1` (the paper form of `huniq`;
`uniqueJust_chains` gives it for two chains). `hFJ'` (`F ⪯ J'`) is a
hypothesis. The step "in a contest, an actual head reaches H" is AP data
(`ap.headReachesLo.v5` under ALFS) and is not in this file. -/

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- [pin fj.inBandLock.v1] For an in-band selected source C of height m, any
carrier in the full view of a justified entry J' at m (with F ⪯ J') forces C's
entry at m to be J'. So a lock or same-action finality pair on J' ≠ C's entry
cannot suppress C's row. -/
theorem inBandLock (E : Electorate V) (cfg : FGConfig) (F : FGBlock V) (Vw : View V)
    (hinj : ViewRootInj Vw) (C : FGBlock V) (hC : C ∈ Vw)
    (hband : (fjFrame E cfg F Vw).lo ≤ hOf E cfg C)
    (hsrc : FGBlock.Preceq (fjFrame E cfg F Vw).Z C)
    (J' : BlockId)
    (hcar : ∃ K ∈ Vw, (derive E cfg K).h_j = hOf E cfg C ∧ (derive E cfg K).J.root = J')
    (hFJ' : ∀ K ∈ Vw, (derive E cfg K).J.root = J' → FGBlock.Preceq F (derive E cfg K).J)
    (huniq : ∀ K ∈ Vw, ∀ K' ∈ Vw, (derive E cfg K).h_j = hOf E cfg C →
      (derive E cfg K').h_j = hOf E cfg C → (derive E cfg K).J = (derive E cfg K').J) :
    (derive E cfg C).T_h.root = J' := by
  obtain ⟨K, hK, hKj, hKJ⟩ := hcar
  set c := fjControls E cfg F Vw with hc
  change c.lo ≤ hOf E cfg C at hband
  change FGBlock.Preceq c.Z C at hsrc
  have hH : c.H = frontier E cfg Vw := rfl
  -- Step 1: the carrier K has state height ≥ m+1, so `H = m+1` and `lo = m`.
  have hKh := justified_below_height E cfg K
  have hKH := le_frontier E cfg hK
  have hCH := le_frontier E cfg hC
  have hlo1 := Controls.H_sub_one_le_lo c
  unfold hOf at hband hKH hCH hKj
  rw [← hH] at hKH hCH
  -- Step 2: a contest gives `lo = H = m+1 > m`.
  have hnc : c.contest = false := by
    cases hcb : c.contest
    · rfl
    · have hloH : c.lo = c.H := by simp only [Controls.lo, hcb, ite_true]
      simp only [Height] at *
      omega
  -- Step 3: the selected pair is at least K's pair, so `j = m` and `J = J(K)`.
  obtain ⟨K', hK', -, hlex, hmax⟩ := lexMax_spec E cfg F Vw hinj ⟨K, hK, hFJ' K hK hKJ⟩
  have hj : c.j = (derive E cfg K').h_j := by
    change (lexMax E cfg F Vw).1 = _
    rw [hlex]
  have hJ : c.J = (derive E cfg K').J := by
    change (lexMax E cfg F Vw).2 = _
    rw [hlex]
  have hle := fst_le_of_lexKey_le (hmax K hK (hFJ' K hK hKJ))
  have hK'h := justified_below_height E cfg K'
  have hK'H := le_frontier E cfg hK'
  unfold hOf at hK'H
  rw [← hH] at hK'H
  dsimp only at hle
  have hK'j : (derive E cfg K').h_j = (derive E cfg C).h := by
    simp only [Height] at *
    omega
  have hJK : c.J = (derive E cfg K).J := by
    rw [hJ]
    exact huniq K' hK' K hK hK'j hKj
  -- The frame is uncontested with root J.
  have hr : c.rootIsJ = true := by
    simp only [Controls.rootIsJ, hnc, hj, Bool.not_false, Bool.and_true, decide_eq_true_eq]
    simp only [Height] at *
    omega
  have hZ : c.Z = (derive E cfg K).J := by
    simp only [Controls.Z, hr, ite_true, hJK]
  -- Step 4: C extends J and has height m, so C's entry at m is J.
  rw [hZ] at hsrc
  have hnz : (derive E cfg K).h_j ≠ 0 := by
    have := one_le_h E cfg C
    simp only [Height] at *
    omega
  rw [entry_eq_of_preceq E cfg K C hnz hKj.symm hsrc, hKJ]

/-- [pin fj.inBandLock.v1] (a lock at H needs a carrier above H) A finality pair
made with the head fields of Hd has the head as carrier at state height at least
its height plus one. -/
theorem finalityPair_carrier_above (E : Electorate V) (cfg : FGConfig) (Λ : Record) (i : V)
    (src : Option (FGBlock V)) (Hd : FGBlock V) (p : FinalityPair)
    (hp : (createRow E cfg Λ i src (HeadFields.ofBlock E cfg Hd)).1.finality_pair = some p) :
    p.height + 1 ≤ (derive E cfg Hd).h := by
  obtain ⟨h1, -⟩ := provenance_finalityRow E cfg Λ i src Hd p hp
  rw [h1]
  exact justified_below_height E cfg Hd

end AvailableChain.KitFG
end
