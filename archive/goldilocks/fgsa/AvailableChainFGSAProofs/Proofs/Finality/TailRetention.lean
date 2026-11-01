module
public import AvailableChainFGSA.Proofs.WindowRetention
public import AvailableChainFGSA.Proofs.StoreLaws
public import AvailableChainFGSA.Statements.WindowEntries

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG

variable (p : Params)

private theorem ktail_view_hj (B : FGBlock (Fin p.n)) :
    (heightView p B).h_j = (Window.derive p p.K_W B).h_j := by
  rw [heightView_def, Window.projectHeight_def]

private theorem ktail_view_J (B : FGBlock (Fin p.n)) :
    (heightView p B).J = (Window.derive p p.K_W B).J := by
  rw [heightView_def, Window.projectHeight_def]

private theorem ktail_view_h (B : FGBlock (Fin p.n)) :
    (Window.certificateHeight p p.K_W B).h = (heightView p B).h := by
  rw [Window.certificateHeight_def, heightView_def]

private theorem ktail_view_hF (B : FGBlock (Fin p.n)) :
    (finalityView p B).h_F = (Window.derive p p.K_W B).h_F := by
  rw [finalityView_def, Window.certificateFinality_def]
  dsimp only
  rw [Window.projectFinality_def]

/-! ### The latest pending pair is a window entry -/

/-- ROOT-DIGEST W2b. Paper 22:1997–1999 (FT-Tail-W: "in the pending case the latest entry is
retained"). While finality is below the latest justification, the window keeps the
latest pair (h_j, J) as an entry. Plan §3: membership from the fold, not from birth.
DC: INTENTIONAL: W keeps up to K entries; DC keeps one pending pair. -/
theorem ktail_latest_entry (B : FGBlock (Fin p.n))
    (hpend : (Window.derive p p.K_W B).h_F < (Window.derive p p.K_W B).h_j) :
    ∃ e ∈ (Window.derive p p.K_W B).W, e.j = (Window.derive p p.K_W B).h_j ∧
      e.X = (Window.derive p p.K_W B).J := by
  have hK := p.kWLarge
  induction B with
  | genesis =>
    exfalso
    rw [Window.derive_def] at hpend
    exact Nat.lt_irrefl 0 hpend
  | node P s root x rs ih =>
    have hPB : FGBlock.Preceq P (.node P s root x rs) := preceq_parent_node P s root x rs
    rcases Window.window_latest_pair_kept p p.K_W P s root x rs with
      ⟨hj, hJ, _hq⟩ | ⟨_hj, _hJ, hq⟩
    · have hFP := Window.window_hF_mono p p.K_W hK P _ hPB
      obtain ⟨e, he, hej, heX⟩ := ih (by rw [← hj]; exact lt_of_le_of_lt hFP hpend)
      rcases Window.window_entry_history p p.K_W hK P _ hPB e he with
        ⟨d, hd, hdj, hdX, -⟩ | ⟨-, hle, -⟩ |
          ⟨-, -, -, P', s', root', x', rs', -, hP'B, -, -, hlen, _C, -, -, hall⟩
      · exact ⟨d, hd, hdj.trans (hej.trans hj.symm), hdX.trans (heX.trans hJ.symm)⟩
      · rw [hej, ← hj] at hle
        exact absurd hpend (Nat.not_lt.mpr hle)
      · exfalso
        have hne : (Window.derive p p.K_W (.node P' s' root' x' rs')).W ≠ [] := by
          intro h0
          rw [h0] at hlen
          have h2 := hK
          simp only [List.length_nil] at hlen
          omega
        obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hne
        have hlt := (hall d hd).1
        have hdle := (Window.window_bounds p p.K_W hK _ d hd).2.1
        have hmono := Window.window_hj_mono p p.K_W hK _ _ hP'B
        rw [hej, ← hj] at hlt
        exact absurd (lt_of_lt_of_le hlt (hdle.trans hmono)) (Nat.lt_irrefl _)
    · obtain ⟨-, older, hW, -, -⟩ :=
        Window.window_target_appended_newest p p.K_W hK P s root x rs hq
      have hjEq : (Window.derive p p.K_W (.node P s root x rs)).h_j =
          (Window.finalizeWindow p.E (Window.certificateFolded p p.K_W (.node P s root x rs))).h ∧
          (Window.derive p p.K_W (.node P s root x rs)).J =
          (Window.finalizeWindow p.E (Window.certificateFolded p p.K_W (.node P s root x rs))).T_h
            := by
        change (Window.process_height_events p.E p.cfg p.K_W
          (Window.certificateFolded p p.K_W (.node P s root x rs))).h_j = _ ∧
          (Window.process_height_events p.E p.cfg p.K_W
          (Window.certificateFolded p p.K_W (.node P s root x rs))).J = _
        rw [Window.process_height_events_def]
        dsimp only
        rw [ite_eq_left hq]
        exact ⟨rfl, rfl⟩
      refine ⟨_, by rw [hW]; exact List.mem_append_right _ (List.mem_singleton_self _),
        hjEq.1.symm, hjEq.2.symm⟩

/-! ### At most one justification birth above a height-sourceH witness -/

/-- ROOT-DIGEST W2b. Paper 22:2001–2003 (FT-Tail-W: "before the terminal z+κ carrier there is at
most
one newer justification, at e+1"). On the chain from Q to P with Q at height at least
y and P at height at most y+1, every birth crosses height y, and the crossing is unique.
Plan §3: the birth set is built from uniqueness, not from a scalar height bound.
DC: INTENTIONAL: W retention; DC has no window. -/
theorem ktail_one_birth (Q P : FGBlock (Fin p.n)) (y : Nat)
    (hQ : y ≤ (heightView p Q).h) (hP : (heightView p P).h ≤ y + 1) :
    ∃ births : Finset (FGBlock (Fin p.n)), births.card ≤ 1 ∧
      ∀ C j J, StrictPrefix Q C → FGBlock.Preceq C P →
        JustificationBirth p.E (Window.certificateHeight p p.K_W) C j J → C ∈ births := by
  classical
  have laws := (fgCertificateLaws p).height
  -- Every birth on this chain has parent height y and its own height y+1.
  have shape : ∀ C j J, StrictPrefix Q C → FGBlock.Preceq C P →
      JustificationBirth p.E (Window.certificateHeight p p.K_W) C j J →
      (heightView p C.parent).h = y ∧ (heightView p C).h = y + 1 := by
    intro C j J hQC hCP hb
    obtain ⟨hne, hpar, -, -, -, hself, -⟩ := hb
    have hpar' : (heightView p C.parent).h = j := (ktail_view_h p C.parent).symm.trans hpar
    have hself' : (heightView p C).h = j + 1 := (ktail_view_h p C).symm.trans hself
    have hQpar : FGBlock.Preceq Q C.parent := by
      cases C with
      | genesis => exact (hne rfl).elim
      | node R t root z rows => exact preceq_parent_of_preceq_node hQC.1 hQC.2
    have h1 := laws.h_mono hQpar
    have h2 := laws.h_mono hCP
    rw [hpar'] at h1
    rw [hself'] at h2
    simp only [Height] at *
    refine ⟨?_, ?_⟩ <;> omega
  by_cases hex : ∃ C j J, StrictPrefix Q C ∧ FGBlock.Preceq C P ∧
      JustificationBirth p.E (Window.certificateHeight p p.K_W) C j J
  · obtain ⟨C₀, j₀, J₀, hQC₀, hC₀P, hb₀⟩ := hex
    refine ⟨{C₀}, Finset.card_singleton C₀ |>.le, ?_⟩
    intro C j J hQC hCP hb
    rw [Finset.mem_singleton]
    have s₀ := shape C₀ j₀ J₀ hQC₀ hC₀P hb₀
    have s₁ := shape C j J hQC hCP hb
    -- A strict ancestor birth would sit at the descendant's parent height.
    have noStrict : ∀ A B j' J' j'' J'',
        JustificationBirth p.E (Window.certificateHeight p p.K_W) A j' J' →
        JustificationBirth p.E (Window.certificateHeight p p.K_W) B j'' J'' →
        (heightView p A).h = y + 1 → (heightView p B.parent).h = y →
        FGBlock.Preceq A B → A = B := by
      intro A B j' J' j'' J'' _ hbB hA hB hAB
      by_contra hne
      have hBg : B ≠ .genesis := hbB.1
      have hAp : FGBlock.Preceq A B.parent := by
        cases B with
        | genesis => exact (hBg rfl).elim
        | node R t root z rows => exact preceq_parent_of_preceq_node hAB hne
      have := laws.h_mono hAp
      simp only [Height] at *
      omega
    rcases preceq_total_of_common hCP hC₀P with h | h
    · exact noStrict C C₀ j J j₀ J₀ hb hb₀ s₁.2 s₀.1 h
    · exact (noStrict C₀ C j₀ J₀ j J hb₀ hb s₀.2 s₁.1 h).symm
  · refine ⟨∅, by simp, ?_⟩
    intro C j J hQC hCP hb
    exact (hex ⟨C, j, J, hQC, hCP, hb⟩).elim

/-! ### Two-height retention of the latest pending key -/

/-- Paper 22:1997–2003 (FT-Tail-W), plan §3. Q has the latest pending key (hK, K)
with hK = h_j(Q) < h(Q). Along a chain to P with h(Q) ≥ y and h(P) ≤ y+1, the key
stays in P's window or P's finality covers it. The scalar gap between hK and y is
free (plan §6, K_W = 2 case).
DC: INTENTIONAL: W retention with K_W ≥ 2; retention does not imply acceptance. -/
theorem ktail_retained_or_covered (Q P : FGBlock (Fin p.n)) (y : Nat)
    (hQP : FGBlock.Preceq Q P) (hQ : y ≤ (heightView p Q).h)
    (hP : (heightView p P).h ≤ y + 1)
    (hpend : (finalityView p Q).h_F < (heightView p Q).h_j) :
    Window.RetainedW p P (heightView p Q).h_j (heightView p Q).J ∨
      Window.CoveredW p P (heightView p Q).h_j (heightView p Q).J := by
  have hK := p.kWLarge
  rw [ktail_view_hF, ktail_view_hj] at hpend
  rw [ktail_view_hj, ktail_view_J]
  obtain ⟨e, he, hej, heX⟩ := ktail_latest_entry p Q hpend
  by_cases hle : (Window.derive p p.K_W Q).h_j ≤ (Window.derive p p.K_W P).h_F
  · right
    rw [Window.CoveredW_def]
    refine ⟨hle, ?_⟩
    have hc := Window.window_le_hF_covered p p.K_W hK Q P hQP e he (by rw [hej]; exact hle)
    rw [heX] at hc
    exact hc
  · left
    obtain ⟨births, hcard, hcover⟩ := ktail_one_birth p Q P y hQ hP
    obtain ⟨d, hd, hdj, hdX, -⟩ := Window.window_retained_fresh_one_newer p p.K_W hK Q P hQP
      e he hej (by rw [hej]; exact Nat.lt_of_not_le hle) births hcard hcover
    rw [Window.RetainedW_def]
    exact ⟨d, hd, hdj.trans hej, hdX.trans heX⟩

end AvailableChain.FGSA.Run
end
