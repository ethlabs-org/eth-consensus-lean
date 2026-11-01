module
public import AvailableChainFGSAClaims.Statements.Phases
public import AvailableChainFGSA.Proofs.FrameViews
public import AvailableChainKitFG.HeightConsumeTransfer
public import AvailableChainKitFG.HeightHistoryTransfer

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG

/-- The active height bridge supplies the shared height laws. -/
private theorem kheight_laws (p : Params) : FGHeightLaws p.E (heightView p) :=
  heightLaws_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)

/-- Equal heights on the entry path keep the entry block. -/
private theorem kheight_entry (p : Params) {U P : FGBlock (Fin p.n)} {y : Nat}
    (hU : EntryAt p U y) (hUP : FGBlock.Preceq U P)
    (hP : (heightView p P).h = y) : (heightView p P).T_h = U :=
  ((kheight_laws p).entry_plateau hUP (hU.1.trans hP.symm)).symm.trans hU.2

/-- ROOT-DIGEST W2b. Target coverage writes the entry through the height bridge. -/
private theorem kheight_target (p : Params) {U X : FGBlock (Fin p.n)} {y : Nat}
    (hX : X ≠ .genesis) (hU : EntryAt p U y) (hUX : FGBlock.Preceq U X.parent)
    (hP : (heightView p X.parent).h = y) (hc : CoveredByChild p .target X U y) :
    JustifiedCross p X U y := by
  have hT := kheight_entry p hU hUX hP
  obtain ⟨S, hS, hc⟩ := hc
  cases X with
  | genesis => exact (hX rfl).elim
  | node P s root x rs =>
      change (heightView p P).h = y at hP
      change (heightView p P).T_h = U at hT
      obtain ⟨hh, hJ, hj⟩ := derive_target_of_cover_of_bridge p.E p.cfg
        (heightView p) (heightView_bridge p) P s root x rs S hS (by
          simpa only [hP, hT] using
            (show ∀ i ∈ S, i ∈ (heightView p P).target_participation ∨
              ∃ a ∈ rs, a.signer = i ∧ a.height_pair = .vote y U.root false from hc))
      exact ⟨hP, hh.trans (congrArg (· + 1) hP), hJ.trans hT, hj.trans hP⟩

/-- ROOT-DIGEST W2b. Mature progress coverage advances through the height bridge. -/
private theorem kheight_progress (p : Params) {U X : FGBlock (Fin p.n)} {y : Nat}
    (hX : X ≠ .genesis) (hU : EntryAt p U y) (hUX : FGBlock.Preceq U X.parent)
    (hP : (heightView p X.parent).h = y) (hc : CoveredByChild p .progress X U y)
    (hm : U.slot + p.δt ≤ X.slot) : (heightView p X).h = y + 1 := by
  have hT := kheight_entry p hU hUX hP
  obtain ⟨S, hS, hc⟩ := hc
  cases X with
  | genesis => exact (hX rfl).elim
  | node P s root x rs =>
      change (heightView p P).h = y at hP
      change (heightView p P).T_h = U at hT
      have hh := derive_progress_of_cover_of_bridge p.E p.cfg
        (heightView p) (heightView_bridge p) P s root x rs S hS (by
          intro i hi
          rcases hc i hi with hb | ⟨a, ha, hs, timeout, hp⟩
          · exact Or.inl hb
          · refine Or.inr ⟨a, ha, hs, ?_⟩
            rw [hp]
            change decide (y = (heightView p P).h ∧
              U.root = (heightView p P).T_h.root) = true
            simp only [hP, hT, and_self, decide_true, eq_self]) (by
          rw [hT]
          exact hm)
      exact hh.trans (congrArg (· + 1) hP)

/-- A crossing either writes this entry or keeps a lower justification. -/
private theorem kheight_cross_cases (p : Params) {U W : FGBlock (Fin p.n)} {y : Nat}
    (hU : EntryAt p U y) (hUW : FGBlock.Preceq U W.parent)
    (hP : (heightView p W.parent).h = y) (hW : (heightView p W).h = y + 1) :
    JustifiedCross p W U y ∨ MixedCross p W y :=
  cross_cases_of_laws (kheight_laws p) (FGJustificationLaws.of_bridge (heightView_bridge p))
    hU hUW hP hW

/-- ROOT-DIGEST W2b. FINAL 22:710–737,1213–1223. The first target edge supplies the trichotomy.
DC: W4FKChainJustification.lean:185; FG-SA also names a mixed ancestor. -/
theorem fgsa_foldTrichotomy_target (p : Params) : foldTrichotomy p .target := by
  rw [foldTrichotomy_def]
  intro y U X hX hU hUX hc _hm
  have laws := kheight_laws p
  have hlow := laws.h_mono hUX
  rw [hU.1] at hlow
  by_cases hP : (heightView p X.parent).h = y
  · have hj := kheight_target p hX hU hUX hP (hc hP)
    exact ⟨by rw [hj.2.1], fun _ => Or.inl ⟨X, preceq_refl _, hj⟩⟩
  · have hhigh : y < (heightView p X.parent).h := by simp only [Height] at *; omega
    obtain ⟨W, _hne, hUW, hWP, hp, hw⟩ := first_height_crossing_edge_of_bridge
      p.E p.cfg (heightView p) (heightView_bridge p) y hUX hU.1 hhigh
    have hPX : FGBlock.Preceq X.parent X := by
      cases X with
      | genesis => exact (hX rfl).elim
      | node P s root x rs => exact preceq_parent_node P s root x rs
    have hmono := laws.h_mono hPX
    refine ⟨by simp only [Height] at *; omega, fun _ => ?_⟩
    rcases kheight_cross_cases p hU hUW hp hw with hj | hm
    · exact Or.inl ⟨W, preceq_trans hWP hPX, hj⟩
    · exact Or.inr ⟨W, hWP, hm⟩

/-- ROOT-DIGEST W2b. FINAL 22:710–737,1213–1223. Mature progress crosses or has already crossed.
DC: ProgressQuorumCore.lean:39; height monotonicity handles earlier crossings. -/
theorem fgsa_foldTrichotomy_progress (p : Params) : foldTrichotomy p .progress := by
  rw [foldTrichotomy_def]
  intro y U X hX hU hUX hc hm
  have laws := kheight_laws p
  have hlow := laws.h_mono hUX
  rw [hU.1] at hlow
  constructor
  · by_cases hP : (heightView p X.parent).h = y
    · rw [kheight_progress p hX hU hUX hP (hc hP) (hm rfl)]
    · have hPX : FGBlock.Preceq X.parent X := by
        cases X with
        | genesis => exact (hX rfl).elim
        | node P s root x rs => exact preceq_parent_node P s root x rs
      have := laws.h_mono hPX
      simp only [Height] at *
      omega
  · intro hk
    cases hk

/-- ROOT-DIGEST W2b. A matching carrier row persists at a later point of the same height. -/
private theorem kheight_progress_row (p : Params) {B P : FGBlock (Fin p.n)}
    {a : Row (Fin p.n)} (ha : a ∈ B.rows) (hBP : FGBlock.Preceq B P)
    (hh : (heightView p B.parent).h = (heightView p P).h)
    (hm : a.height_pair.matchesEntry (heightView p B.parent).h
      (heightView p B.parent).T_h.root = true) : a.signer ∈ (heightView p P).progress := by
  cases B with
  | genesis => exact (List.not_mem_nil ha).elim
  | node D s root x rs =>
      exact progress_from_row_of_bridge p.E p.cfg (heightView p) (heightView_bridge p) ha hBP hm hh

/-- ROOT-DIGEST W2b. FINAL 21:1397–1407,22:710–737. Equal-height paths keep stored progress
coverage.
DC: ProgressQuorumCore.lean:39; KitFG row-bit persistence supplies the path transfer. -/
theorem fgsa_storedProgressConsume (p : Params) : StoredProgressConsume p := by
  rw [StoredProgressConsume_def]
  intro y U B X hU hUB hBX hc hP hm
  have laws := kheight_laws p
  have hBP : FGBlock.Preceq B.parent X.parent := by
    have hb : FGBlock.Preceq B.parent B := by
      cases B with
      | genesis => exact preceq_refl _
      | node D s root x rs => exact preceq_parent_node D s root x rs
    exact preceq_trans hb hBX
  have hlo := laws.h_mono hUB
  have hhi := laws.h_mono hBP
  have hB : (heightView p B.parent).h = y := by
    rw [hU.1] at hlo
    rw [hP] at hhi
    simp only [Height] at *
    omega
  have hT := kheight_entry p hU hUB hB
  obtain ⟨S, hS, hc⟩ := hc
  have hbits : ∀ i ∈ S, i ∈ (heightView p X.parent).progress := by
    intro i hi
    rcases hc i hi with hb | ⟨a, ha, hs, timeout, hp⟩
    · exact progress_persist_of_bridge p.E p.cfg (heightView p) (heightView_bridge p) hBP
        (hB.trans hP.symm) hb
    · rw [← hs]
      exact kheight_progress_row p ha hBX (hB.trans hP.symm) (by
        rw [hp]
        change decide (y = (heightView p B.parent).h ∧
          U.root = (heightView p B.parent).T_h.root) = true
        simp only [hB, hT, and_self, decide_true, eq_self])
  have hX : X ≠ .genesis := by
    intro heq
    subst X
    have hSe : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro i hi
      obtain ⟨W, a, hW, ha, _, _⟩ := laws.progress_origin .genesis i (hbits i hi)
      obtain rfl := preceq_genesis.mp hW
      exact List.not_mem_nil ha)
    subst S
    have hq : p.E.q = Gen.Pure.qF p.n :=
      (toWeights_q p.E).symm.trans (unit_toWeights_q p.n)
    rw [hq, Gen.Pure.qF_def] at hS
    have h0 : p.E.weightOf ∅ = 0 := Finset.sum_empty
    rw [h0] at hS
    have hn := p.nPos
    omega
  exact kheight_progress p hX hU (preceq_trans hUB hBP) hP
    ⟨S, hS, fun i hi => Or.inl (hbits i hi)⟩ hm

/-- ROOT-DIGEST W2b. Increasing slots give a slot bound on every ancestor. -/
private theorem kheight_slot_le (p : Params) {W X : FGBlock (Fin p.n)}
    (hs : SlotChain X) (hWX : FGBlock.Preceq W X) : W.slot ≤ X.slot := by
  induction X with
  | genesis => obtain rfl := preceq_genesis.mp hWX; exact le_refl _
  | node P s root x rs ih =>
      by_cases heq : W = .node P s root x rs
      · subst W; exact le_refl _
      · have hWP := preceq_parent_of_preceq_node hWX heq
        have hslot := hs (.node P s root x rs) (preceq_refl _) (by simp)
        have hp : SlotChain P := fun A hA hne =>
          hs A (preceq_node_of_preceq s root x rs hA) hne
        exact le_trans (ih hp hWP) (Nat.le_of_lt hslot)

/-- ROOT-DIGEST W2b. FINAL 22:1213–1216. Every parent ancestor is strictly before maturity.
DC: CarrierTimeoutGate.lean:121; FG-SA takes the slot gate and slot order as premises. -/
theorem fgsa_noMixedMaturity (p : Params) : NoMixedMaturity p := by
  intro y U X hs hU hUX hearly W hWP hm
  have laws := kheight_laws p
  obtain ⟨hP, hW, hj⟩ := hm
  have hne : W ≠ .genesis := by
    intro heq
    subst W
    change (heightView p .genesis).h = y at hP
    rw [hP] at hW
    simp only [Height] at hW
    omega
  have hUW : FGBlock.Preceq U W := by
    rcases preceq_total_of_common hUX hWP with h | h
    · exact h
    · have hh := laws.h_mono h
      rw [hU.1, hW] at hh
      simp only [Height] at hh
      omega
  have hUWp : FGBlock.Preceq U W.parent := by
    cases W with
    | genesis => exact (hne rfl).elim
    | node D s root x rs =>
        apply preceq_parent_of_preceq_node hUW
        intro heq
        rw [← heq, hU.1] at hW
        simp only [Height] at hW
        omega
  have hPX : X.parent.slot < X.slot := hs X (preceq_refl _) (by
    intro heq
    subst X
    obtain rfl := preceq_genesis.mp hWP
    exact hne rfl)
  have hslots := kheight_slot_le p (X := X.parent)
    (fun A hA hAne => hs A (preceq_trans hA (by
      cases X with
      | genesis => exact preceq_refl _
      | node D s root x rs => exact preceq_parent_node D s root x rs)) hAne) hWP
  have hwEarly : W.slot < U.slot + p.cfg.timeoutDelay := by
    change X.slot < U.slot + p.cfg.timeoutDelay + 1 at hearly
    simp only [Slot] at *
    omega
  have hjust := no_mixed_cross_before_maturity_of_bridge p.E p.cfg
    (heightView p) (heightView_bridge p) y hne hUWp hU.1 hU.2 hP hwEarly hW
  rw [hjust.2] at hj
  exact (Nat.lt_irrefl y hj)

/-- FINAL 22:1218–1223. No mixed predecessor leaves a justified first crossing.
DC: W4FKChainJustification.lean:185; FG-SA uses the explicit ancestor path. -/
theorem fgsa_justifyAt (p : Params) : JustifyAt p := by
  rw [JustifyAt_def]
  intro y U X hX hU hUX hc hn
  obtain ⟨_hh, hcross⟩ := fgsa_foldTrichotomy_target p y U X hX hU hUX hc
    (by intro hk; cases hk)
  rcases hcross rfl with hj | ⟨W, hWP, hm⟩
  · exact hj
  · exact (hn W hWP hm).elim

end AvailableChain.FGSA.Run
end
