module
public import AvailableChainFGCompose.Proofs.Finality.RestoreReads
public import AvailableChainKitFG.WindowStore
public import AvailableChainKitFG.FrameGeometry

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P)
variable (Ef : Electorate (Fin n)) (cfg : FGConfig) (K : Nat)

/-- DC: SAME entry comparison on one path, with the window height view. -/
private theorem d7a5a_J_path (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K)
    (st : Store (Fin n))
    (hI : KitFG.FGStoreInvariant (KitFG.Window.certificateHeight Ef cfg K)
      (KitFG.Window.certificateFinality Ef cfg K) st)
    (W : FGBlock (Fin n)) (hpath : FGBlock.Preceq st.J W) :
    FGBlock.Preceq (KitFG.Window.certificateHeight Ef cfg K W).J st.J ∨
      st.h_j < (KitFG.Window.certificateHeight Ef cfg K W).h_j := by
  have hH := (KitFG.Window.windowCertificateLaws Ef cfg K hne hK).height
  have hJ : FGJustificationLaws (KitFG.Window.certificateHeight Ef cfg K) :=
    FGJustificationLaws.of_bridge (KitFG.Window.windowHeightBridge Ef cfg K hK)
  have hJW := KitFG.preceq_trans (hH.justified_preceq_entry W) (hH.entry_preceq W)
  rcases KitFG.preceq_total_of_common hJW hpath with h | h
  · exact Or.inl h
  by_cases hz : (KitFG.Window.certificateHeight Ef cfg K W).h_j = 0
  · exact Or.inl (hJ.J_zero W hz ▸ KitFG.genesis_preceq st.J)
  by_cases hs : st.h_j = 0
  · right
    rw [hs]
    exact Nat.pos_of_ne_zero hz
  obtain ⟨C, _, _, hc, he⟩ := hI.pair.1
  have hsh : (KitFG.Window.certificateHeight Ef cfg K st.J).h = st.h_j := by
    rw [he, hJ.J_height C (fun h => hs (hc.trans h)), ← hc]
  have hwh := hJ.J_height W hz
  have hle := hH.h_mono h
  rw [hsh, hwh] at hle
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inr hlt
  left
  have hp := hH.entry_plateau h (hsh.trans (heq.trans hwh.symm))
  rw [he, hJ.J_entry C, hJ.J_entry W] at hp
  rw [he, hp]
  exact KitFG.preceq_refl _

/-- DC: INTENTIONAL selected handler guards accept the window finality. -/
private theorem d7a5a_update (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K)
    (st : Store (Fin n))
    (hI : KitFG.FGStoreInvariant (KitFG.Window.certificateHeight Ef cfg K)
      (KitFG.Window.certificateFinality Ef cfg K) st)
    (W : FGBlock (Fin n))
    (hF : FGBlock.Preceq st.F (SimplexFG.Window.derive Ef cfg K W).F)
    (hmem : (SimplexFG.Window.derive Ef cfg K W).F ∈ insert W st.TF)
    (hj : FGBlock.Preceq st.J W ∨ st.h_j < (SimplexFG.Window.derive Ef cfg K W).h_j)
    (hcap : max st.h_max ((SimplexFG.Window.derive Ef cfg K W).h) ≤
      (SimplexFG.Window.derive Ef cfg K W).h + 1) :
    FGBlock.Preceq (SimplexFG.Window.derive Ef cfg K W).F
      (SimplexFG.Window.update_finality Ef cfg K { st with TF := insert W st.TF } W).F := by
  classical
  have hσJ : FGBlock.Preceq (SimplexFG.Window.derive Ef cfg K W).F
      (SimplexFG.Window.derive Ef cfg K W).J := KitFG.Window.window_F_preceq_J Ef cfg K hne hK W
  have hFJ := KitFG.preceq_trans hF hσJ
  have hj' : FGBlock.Preceq (SimplexFG.Window.derive Ef cfg K W).J st.J ∨
      st.h_j < (SimplexFG.Window.derive Ef cfg K W).h_j := by
    rcases hj with hj | hj
    · exact d7a5a_J_path Ef cfg K hne hK st hI W hj
    · exact Or.inr hj
  have hJW : FGBlock.Preceq (SimplexFG.Window.derive Ef cfg K W).J W :=
    KitFG.preceq_trans
      ((KitFG.Window.windowCertificateLaws Ef cfg K hne hK).height.justified_preceq_entry W)
      ((KitFG.Window.windowCertificateLaws Ef cfg K hne hK).height.entry_preceq W)
  let st1 : Store (Fin n) :=
    { st with TF := insert W st.TF, h_max := max st.h_max ((SimplexFG.Window.derive Ef cfg K W).h) }
  let st2 := if FGBlock.preceq st.F (SimplexFG.Window.derive Ef cfg K W).J &&
      decide (lexKey (st.h_j, st.J) <
        lexKey ((SimplexFG.Window.derive Ef cfg K W).h_j, (SimplexFG.Window.derive Ef cfg K W).J))
    then { st1 with
      J := (SimplexFG.Window.derive Ef cfg K W).J
      h_j := (SimplexFG.Window.derive Ef cfg K W).h_j } else st1
  have h2F : st2.F = st.F := by dsimp only [st2]; split_ifs <;> rfl
  have h2T : st2.TF = insert W st.TF := by dsimp only [st2]; split_ifs <;> rfl
  have h2H : st2.h_max = max st.h_max ((SimplexFG.Window.derive Ef cfg K W).h) := by
    dsimp only [st2]; split_ifs <;> rfl
  have h2J : FGBlock.Preceq (SimplexFG.Window.derive Ef cfg K W).F st2.J := by
    dsimp only [st2]
    split_ifs with hu
    · exact hσJ
    · rcases hj' with hj | hj
      · exact KitFG.preceq_trans hσJ hj
      · exfalso
        apply hu
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hFJ, Prod.Lex.left _ _ hj⟩
  have hv : (SimplexFG.Window.derive Ef cfg K W).F ∈
      SimplexFG.Window.acceptViable Ef cfg K st2 := by
    rw [SimplexFG.Window.acceptViable_def]
    apply Finset.mem_filter.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨h2T.symm ▸ hmem, ?_, ?_⟩
    · exact h2F.symm ▸ hF
    · refine ⟨W, h2T.symm ▸ Finset.mem_insert_self _ _, KitFG.preceq_trans hσJ hJW, ?_⟩
      rw [h2H]
      simp only [Height] at hcap ⊢
      omega
  rw [SimplexFG.Window.update_finality_def]
  change FGBlock.Preceq (SimplexFG.Window.derive Ef cfg K W).F
    (if FGBlock.preceq st2.F (SimplexFG.Window.derive Ef cfg K W).F &&
      decide (st2.F ≠ (SimplexFG.Window.derive Ef cfg K W).F) &&
      FGBlock.preceq (SimplexFG.Window.derive Ef cfg K W).F st2.J &&
      decide ((SimplexFG.Window.derive Ef cfg K W).F ∈ SimplexFG.Window.acceptViable Ef cfg K st2)
    then { st2 with F := (SimplexFG.Window.derive Ef cfg K W).F } else st2).F
  by_cases he : st2.F = (SimplexFG.Window.derive Ef cfg K W).F
  · simp only [he, ne_eq, not_true_eq_false, decide_false, Bool.and_false,
      Bool.false_and]
    rw [ite_eq_right (by decide)]
    exact he.symm ▸ KitFG.preceq_refl _
  · have ht : (FGBlock.preceq st2.F (SimplexFG.Window.derive Ef cfg K W).F &&
        decide (st2.F ≠ (SimplexFG.Window.derive Ef cfg K W).F) &&
        FGBlock.preceq (SimplexFG.Window.derive Ef cfg K W).F st2.J &&
        decide ((SimplexFG.Window.derive Ef cfg K W).F ∈
          SimplexFG.Window.acceptViable Ef cfg K st2)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨h2F.symm ▸ hF, he⟩, h2J⟩, hv⟩
    rw [ht, ite_eq_left rfl]
    exact KitFG.preceq_refl _

/-- DC-CS/W4FKChainSecondCheckpoint.lean:43 (W4CommonFinalityAtConfirmationPin).
INTENTIONAL: the selected W receipt, its exact one-step consequence and a strict
supplied deadline. -/
theorem acceptBefore_W (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K)
    (F : FGFinalityDurableLaws R)
    (ready : Nat → V → FGBlock (Fin n) → Time → Prop)
    (step : AcceptStep_W R E rho Ef cfg K ready)
    (inv : ∀ i x, x ∈ rho.honest → KitFG.FGStoreInvariant
      (KitFG.Window.certificateHeight Ef cfg K) (KitFG.Window.certificateFinality Ef cfg K)
      (R.core (V2.D.Run.stateBefore E rho i x)).fg)
    (W U : FGBlock (Fin n)) (a₀ d : Time)
    (h : AcceptPrem_W R E rho Ef cfg K ready W U a₀ d) :
    ∀ x ∈ rho.honest, AcceptsFinalBefore R E rho x U d := by
  intro x hx
  classical
  let w := h.deliver.selected x hx
  obtain ⟨htime, hbefore, hreceipt⟩ := h.deliver.witness x hx
  have hcover : FGBlock.Preceq U (R.core (V2.D.Run.stateBefore E rho (w.index + 1) x)).fg.F := by
    rcases hreceipt with hc | ⟨_, hr⟩
    · exact hc
    obtain ⟨he, hm⟩ := step w.index x W w.time hx hr
    by_cases hc : FGBlock.Preceq U (R.core (V2.D.Run.stateBefore E rho w.index x)).fg.F
    · refine KitFG.preceq_trans hc ?_
      rw [he]
      rcases KitFG.Window.window_update_finality_F_cases Ef cfg K
        { (R.core (V2.D.Run.stateBefore E rho w.index x)).fg with
          TF := insert W (R.core (V2.D.Run.stateBefore E rho w.index x)).fg.TF } W with
        hs | ⟨hf, _, _, hn⟩
      · rw [hs]
        exact KitFG.preceq_refl _
      · rw [hn]
        exact hf
    have hf : FGBlock.Preceq (R.core (V2.D.Run.stateBefore E rho w.index x)).fg.F U :=
      (h.guards.finCmp x hx hr).resolve_right hc
    rw [he]
    apply KitFG.preceq_trans h.finalized
    apply d7a5a_update Ef cfg K hne hK _ (inv w.index x hx) W
      (KitFG.preceq_trans hf h.finalized) hm (h.guards.jPath x hx hr hc)
    exact h.guards.cap x hx hr hc
  apply finality_acceptsFinalBefore_of_idx R E rho F h.schedule
  obtain ⟨e, he, het⟩ := Option.map_eq_some_iff.mp htime
  obtain ⟨hi, hie⟩ := List.getElem?_eq_some_iff.mp he
  refine ⟨w.index + 1, hi, ?_, hcover⟩
  intro k hk
  have hki : k ≤ w.index := Nat.le_of_lt_succ hk
  have hkl : k < rho.events.length := lt_of_le_of_lt hki hi
  refine ⟨rho.events[k], List.getElem?_eq_getElem hkl, ?_⟩
  apply lt_of_le_of_lt (b := w.time) _ hbefore
  by_cases hke : k = w.index
  · subst k
    rw [hie]
    exact le_of_eq het
  · have hkey := (List.pairwise_iff_getElem.mp h.schedule.sorted)
      k w.index hkl hi (lt_of_le_of_ne hki hke)
    have ht := V2.D.Engine.time_le_of_key_le _ _ hkey
    rw [hie, het] at ht
    exact ht

/-- DC-CS/W4FKChainFinalityWrite.lean:177 followed by acceptance at :43.
INTENTIONAL: the pending pair is consumed by the window fold; acceptance uses the same
selected receipt and strict deadline. Conditional on the selected delivery. -/
theorem finalizePending_W (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K)
    (F : FGFinalityDurableLaws R)
    (ready : Nat → V → FGBlock (Fin n) → Time → Prop)
    (step : AcceptStep_W R E rho Ef cfg K ready)
    (inv : ∀ i x, x ∈ rho.honest → KitFG.FGStoreInvariant
      (KitFG.Window.certificateHeight Ef cfg K) (KitFG.Window.certificateFinality Ef cfg K)
      (R.core (V2.D.Run.stateBefore E rho i x)).fg)
    (y : Nat) (U X : FGBlock (Fin n)) (a₀ d : Time)
    (h : FinalizePrem_W R E rho Ef cfg K ready y U X a₀ d) :
    ∀ x ∈ rho.honest, AcceptsFinalBefore R E rho x U d := by
  have hfinal : FGBlock.Preceq U (SimplexFG.Window.derive Ef cfg K X).F := by
    obtain ⟨child, e, he, hj, hX, Q, hQ, cover⟩ := h.fold
    cases X with
    | genesis => exact (child rfl).elim
    | node B s root body rows =>
        have hc : ∀ i ∈ Q, i ∈ e.Q ∨ ∃ row ∈ rows,
            row.signer = i ∧ row.finality_pair = some ⟨e.j, e.X.root⟩ := by
          intro i hi
          rcases cover i hi with hb | ⟨row, hrow, hs, hf⟩
          · exact Or.inl hb
          · exact Or.inr ⟨row, hrow, hs, by rw [hj, hX]; exact hf⟩
        have r := KitFG.Window.window_finality_of_cover Ef cfg K hne hK B s root body rows e he
          Q hQ hc
        rw [hX] at r
        exact r.1
  exact acceptBefore_W R E rho Ef cfg K hne hK F ready step inv X U a₀ d
    ⟨h.schedule, hfinal, h.deliver, h.guards, h.horizon⟩

end AvailableChain.FGCompose
end
