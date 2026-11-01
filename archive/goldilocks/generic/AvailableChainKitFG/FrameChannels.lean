module
public import AvailableChainKitFG.Correspondence

public section

/-! P3 §8.7 F2.2; bp02 §§3.1–3.4. Pure store geometry for the shared
channels. No run or history is used. DC has no FJ contest counterpart;
TS/spec/fgsa-protocol.tex:2557–2571 explains the contest and band change. -/

namespace AvailableChain.KitFG
open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig)

private theorem frame_J_carrier (st : Store V) (h : StoreInv E cfg st) (hinj : ViewRootInj st.TF) :
    ∃ K ∈ st.TF, st.J = (derive E cfg K).J ∧ st.h_j = (derive E cfg K).h_j := by
  obtain ⟨L, hL, hLF⟩ := h.Fcar
  obtain ⟨K, hK, _, hp, _⟩ := lexMax_spec E cfg st.F st.TF
    hinj ⟨L, hL, hLF ▸ derive_F_preceq_J E cfg L⟩
  exact ⟨K, hK, congrArg Prod.snd (h.pair.trans hp),
    congrArg Prod.fst (h.pair.trans hp)⟩

private theorem frame_crossed_entry (W : FGBlock V) (m : Nat)
    (hm : 1 ≤ m) (hlt : m < hOf E cfg W) :
    ∃ U, FGBlock.Preceq U W ∧ hOf E cfg U = m := by
  obtain ⟨U, hU, hh, _⟩ := height_crossing E cfg W m hm hlt
  exact ⟨U, hU, hh⟩

private theorem frame_contest_crossing (st : Store V) (h : StoreInv E cfg st) (hinj : ViewRootInj
  st.TF)
    (htop : st.h_max = st.h_j + 1) (W : FGBlock V)
    (hW : hOf E cfg W = st.h_max) (hn : ¬ FGBlock.Preceq st.J W) :
    ∃ U, FGBlock.Preceq U W ∧ hOf E cfg U < hOf E cfg W ∧
      ¬ (FGBlock.Preceq st.J (derive E cfg U).T_h ∨
        FGBlock.Preceq (derive E cfg U).T_h st.J) := by
  obtain ⟨K, _, hJ, hj⟩ := frame_J_carrier E cfg st h hinj
  have hnz : st.h_j ≠ 0 := by
    intro hz
    exact hn (hJ ▸ justified_zero_is_genesis E cfg K (hj.symm.trans hz) ▸ genesis_preceq W)
  obtain ⟨U, hU, hh⟩ := frame_crossed_entry E cfg W st.h_j (Nat.one_le_iff_ne_zero.mpr hnz)
    (by rw [hW, htop]; exact Nat.lt_succ_self _)
  refine ⟨U, hU, by rw [hh, hW, htop]; exact Nat.lt_succ_self _, ?_⟩
  intro hc
  have hJW : FGBlock.Preceq (derive E cfg U).T_h W :=
    preceq_trans (entry_preceq E cfg U) hU
  have hhJ : (derive E cfg st.J).h = (derive E cfg U).h := by
    rw [hJ, entry_height E cfg K (fun hz => hnz (hj.trans hz))]
    exact hj.symm.trans hh.symm
  have heJ : (derive E cfg st.J).T_h = st.J := hJ ▸ J_is_entry E cfg K
  rcases hc with hc | hc
  · exact hn (preceq_trans hc hJW)
  · have he : (derive E cfg U).T_h = st.J := by
      have hp := entry_eq_on_plateau E cfg hc
        ((entry_same_height E cfg U).trans hhJ.symm)
      rw [entry_idem, heJ] at hp
      exact hp
    exact hn (he ▸ hJW)

/-- P3 §8.7 F2.2, bp02 §§3.1,3.3: compatible crossed entries exclude contest.
DC counterpart: none for contest; EntryHeight.lean:131 supplies the plateau
step. Class A2. The FJ test differs by TS/spec/fgsa-protocol.tex:2557–2571. -/
theorem storeFrame_noContest_of_crossed (st : Store V) (h : StoreInv E cfg st) (hinj : ViewRootInj
  st.TF)
    (hc : ∀ W ∈ st.TF, ∀ U, FGBlock.Preceq U W → hOf E cfg U < hOf E cfg W →
      FGBlock.Preceq st.J (derive E cfg U).T_h ∨
        FGBlock.Preceq (derive E cfg U).T_h st.J) :
    (storeControls E cfg st).contest = false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  change (decide (st.h_max = st.h_j + 1) && decide _) = true at ht
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at ht
  obtain ⟨htop, W, hW, hh, hn⟩ := ht
  obtain ⟨U, hU, hlt, hbad⟩ := frame_contest_crossing E cfg st h hinj htop W hh hn
  exact hbad (hc W hW U hU hlt)

/-- P3 §8.7 F2.2, bp02 §3.3 and the universal CPCompat clause: a block
compatible with J and all crossed entries precedes every contest witness.
DC counterpart: none for contest (FGRootWitness.lean:548 has only root
compatibility). Class A2; TS/spec/fgsa-protocol.tex:2557–2571. -/
theorem storeFrame_contest_of_compatible (st : Store V) (h : StoreInv E cfg st) (hinj :
  ViewRootInj st.TF)
    (B : FGBlock V) (hJ : FGBlock.Preceq st.J B ∨ FGBlock.Preceq B st.J)
    (hc : ∀ W ∈ st.TF, ∀ U, FGBlock.Preceq U W → hOf E cfg U < hOf E cfg W →
      FGBlock.Preceq (derive E cfg U).T_h B ∨ FGBlock.Preceq B (derive E cfg U).T_h)
    (ht : (storeControls E cfg st).contest = true) :
    FGBlock.Preceq B st.J ∧ ∀ W ∈ st.TF, hOf E cfg W = st.h_max →
      ¬ FGBlock.Preceq st.J W → FGBlock.Preceq B W := by
  have ht' := ht
  change (decide (st.h_max = st.h_j + 1) && decide _) = true at ht'
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at ht'
  obtain ⟨htop, W₀, hW₀, hh₀, hn₀⟩ := ht'
  have step : ∀ W ∈ st.TF, hOf E cfg W = st.h_max → ¬ FGBlock.Preceq st.J W →
      FGBlock.Preceq B st.J ∧ FGBlock.Preceq B W := by
    intro W hW hh hn
    obtain ⟨U, hU, hlt, hbad⟩ := frame_contest_crossing E cfg st h hinj htop W hh hn
    have hBW : FGBlock.Preceq B (derive E cfg U).T_h := by
      rcases hc W hW U hU hlt with hu | hu
      · rcases hJ with hj | hj
        · exact (hbad (preceq_total_of_common hj hu)).elim
        · exact (hbad (Or.inr (preceq_trans hu hj))).elim
      · exact hu
    have hBJ : FGBlock.Preceq B st.J := by
      rcases hJ with hj | hj
      · exact (hbad (Or.inl (preceq_trans hj hBW))).elim
      · exact hj
    exact ⟨hBJ, preceq_trans hBW (preceq_trans (entry_preceq E cfg U) hU)⟩
  exact ⟨(step W₀ hW₀ hh₀ hn₀).1, fun W hW hh hn => (step W hW hh hn).2⟩

/-- P3 §8.7 F2.2, bp02 §3.5(3): crossed prefixes bound the uncontested floor.
DC analogue: FGRootWitness.lean:frontier_confirmationWitness_core_entry;
diverges by using pure prefix premises instead of run witnesses. Class A2,
structure-first split (docs/LEAN-ARCHITECTURE.md:63–88). -/
theorem storeFrame_height_of_crossed_prefix (st : Store V) (h : StoreInv E cfg st)
    (B : FGBlock V) (hn : (storeControls E cfg st).contest = false)
    (hc : ∀ W ∈ st.TF, ∀ U, FGBlock.Preceq U W → hOf E cfg U < hOf E cfg W →
      FGBlock.Preceq (derive E cfg U).T_h B) :
    (storeControls E cfg st).lo ≤ hOf E cfg B := by
  have hlo : (storeControls E cfg st).lo = st.h_max - 1 := by
    change (if (storeControls E cfg st).contest then _ else _) = _
    rw [hn]; rfl
  rw [hlo]
  by_cases hh : st.h_max ≤ 1
  · exact le_trans (Nat.sub_eq_zero_of_le hh ▸ Nat.zero_le _) (Nat.le_refl _)
  · obtain ⟨W, hW, hheight⟩ := exists_frontier E cfg st.TF ⟨_, h.gen⟩
    have hw : hOf E cfg W = st.h_max := hheight.trans h.hmax.symm
    obtain ⟨U, hU, hu⟩ := frame_crossed_entry E cfg W (st.h_max - 1)
      (by simp only [Height] at *; omega) (by simp only [Height] at *; omega)
    have hm := h_mono E cfg (hc W hW U hU (by simp only [Height] at *; omega))
    rw [entry_same_height] at hm
    exact hu ▸ hm

/-- P3 §8.7 F2.2, bp02 §3.4: compatibility with crossed entries retains a
stored block above F unless Z covers it. DC analogue: FGRootWitness.lean:548
for compatibility; none for the FJ filtered-domain conclusion. Class A2;
TS/spec/fgsa-protocol.tex:2557–2571 explains the FJ band. -/
theorem storeFrame_retention_of_compatible (st : Store V) (h : StoreInv E cfg st) (hinj :
  ViewRootInj st.TF)
    (B : FGBlock V) (hB : B ∈ st.TF) (hFB : FGBlock.Preceq st.F B)
    (hJ : FGBlock.Preceq st.J B ∨ FGBlock.Preceq B st.J)
    (hc : ∀ W ∈ st.TF, ∀ U, FGBlock.Preceq U W → hOf E cfg U < hOf E cfg W →
      FGBlock.Preceq (derive E cfg U).T_h B ∨ FGBlock.Preceq B (derive E cfg U).T_h) :
    FGBlock.Preceq B (storeControls E cfg st).Z ∨
      B ∈ filteredFrom E cfg (storeControls E cfg st) st.TF := by
  let c := storeControls E cfg st
  by_cases hBZ : FGBlock.Preceq B c.Z
  · exact Or.inl hBZ
  right
  have hZB : FGBlock.Preceq c.Z B := by
    change FGBlock.Preceq (if c.rootIsJ then st.J else st.F) B
    cases hr : c.rootIsJ
    · exact hFB
    · rcases hJ with hj | hj
      · exact hj
      · exact (hBZ (by
          change FGBlock.Preceq B (if c.rootIsJ then st.J else st.F)
          rw [hr]; exact hj)).elim
  apply (mem_filteredFrom E cfg c st.TF B).2
  refine ⟨hB, hFB, hZB, ?_⟩
  cases ht : c.contest with
  | true =>
    have hx := storeFrame_contest_of_compatible E cfg st h hinj B hJ hc ht
    have ht' := ht
    change (decide (st.h_max = st.h_j + 1) && decide _) = true at ht'
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at ht'
    obtain ⟨_, W, hW, hh, hn⟩ := ht'
    exact ⟨W, hW, hx.2 W hW hh hn, hh ▸ Controls.lo_le_H c⟩
  | false =>
    have hlo : c.lo = st.h_max - 1 := by change (if c.contest then _ else _) = _; rw [ht]; rfl
    obtain ⟨W, hW, hh⟩ := exists_frontier E cfg st.TF ⟨_, h.gen⟩
    have hw : hOf E cfg W = st.h_max := hh.trans h.hmax.symm
    by_cases hsmall : st.h_max ≤ 1
    · exact ⟨B, hB, preceq_refl B, by rw [hlo]; simp only [Height] at *; omega⟩
    obtain ⟨U, hU, hu⟩ := frame_crossed_entry E cfg W (st.h_max - 1)
      (by simp only [Height] at *; omega) (by simp only [Height] at *; omega)
    rcases hc W hW U hU (by simp only [Height] at *; omega) with heB | hBe
    · refine ⟨B, hB, preceq_refl B, ?_⟩
      have hm := h_mono E cfg heB
      rw [entry_same_height] at hm
      exact hlo.trans hu.symm ▸ hm
    · exact ⟨W, hW, preceq_trans hBe (preceq_trans (entry_preceq E cfg U) hU),
        by rw [hlo, hw]; simp only [Height] at *; omega⟩

end AvailableChain.KitFG
end
