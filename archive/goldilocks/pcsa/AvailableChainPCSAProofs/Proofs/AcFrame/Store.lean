module
public import AvailableChainPCSAProofs.Proofs.Shared.FGStore
public import AvailableChainPCSAProofs.Proofs.AcFrame.Height
public import AvailableChainPCSAProofs.Proofs.Foundations.Run -- shake: keep (engine induction re-export for AcFrame.Run)
public import AvailableChainFGSA.Proofs.Admission

public section

/-! Store-side AC-only frame preservation (pcsa34-r4.3 §5.0). -/

namespace AvailableChain.PCSA
open SimplexFG
variable {n : Nat}

/-- The cached frame is initial and every chain row has a signer in F. -/
def AcStoreSafe (F : Finset (Fin n)) (st : State n) : Prop :=
  st.fg.F = .genesis ∧ st.fg.J = .genesis ∧ st.fg.h_max = 1 ∧ st.fg.h_j = 0 ∧
    ∀ B ∈ st.fg.TF, ∀ W, FGBlock.Preceq W B → ∀ a ∈ W.rows, a.signer ∈ F

/-- The store invariant exposes only its proposition equation. -/
theorem AcStoreSafe_def (F : Finset (Fin n)) (st : State n) :
    AcStoreSafe F st =
      (st.fg.F = .genesis ∧ st.fg.J = .genesis ∧ st.fg.h_max = 1 ∧ st.fg.h_j = 0 ∧
        ∀ B ∈ st.fg.TF, ∀ W, FGBlock.Preceq W B → ∀ a ∈ W.rows, a.signer ∈ F) := by
  apply propext
  exact ⟨fun h => h, fun h => h⟩

/-- A window update on a block with only faulty rows keeps the cached frame initial. -/
theorem pcsa_on_block_acSafe (p : Params) (F : Finset (Fin p.n))
    (hF : p.E.weightOf F < p.E.q) (st : State p.n) (h : AcStoreSafe F st)
    (B : FGBlock (Fin p.n))
    (hB : ∀ W, FGBlock.Preceq W B → ∀ a ∈ W.rows, a.signer ∈ F) :
    AcStoreSafe F { st with fg := FGSA.Window.on_block p p.K_W st.fg B } := by
  obtain ⟨hh, hj, hJ, hFin⟩ := pcsa_window_no_quorum p F hF B hB
  unfold FGSA.Window.on_block
  split
  · exact h
  · have hT : ∀ C ∈ insert B st.fg.TF, ∀ W, FGBlock.Preceq W C → ∀ a ∈ W.rows,
        a.signer ∈ F := by
      intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      · exact hB
      · exact h.2.2.2.2 C hC
    unfold FGSA.Window.update_finality
    simp only [hh, hj, hJ, hFin, h.1, h.2.1, h.2.2.1, h.2.2.2.1, max_self,
      ne_eq, decide_false, Bool.and_false, lt_self_iff_false]
    exact ⟨rfl, rfl, rfl, rfl, hT⟩

/-- Rows on a new child come from its parent chain or its row list. -/
theorem pcsa_child_rows (P : FGBlock (Fin n)) (b : Block) (rows : List (RowWire n))
    (F : Finset (Fin n))
    (hP : ∀ W, FGBlock.Preceq W P → ∀ a ∈ W.rows, a.signer ∈ F)
    (hr : ∀ a ∈ rows.filterMap RowWire.toRow?, a.signer ∈ F) :
    ∀ W, FGBlock.Preceq W (fgBlock P b rows) → ∀ a ∈ W.rows, a.signer ∈ F := by
  intro W hW
  change (decide (W = fgBlock P b rows) || FGBlock.preceq W P) = true at hW
  rcases Bool.or_eq_true_iff.mp hW with he | hp
  · have he' := of_decide_eq_true he
    subst W
    exact hr
  · exact hP W hp

/-- A delivery preserves the initial frame when all its carried rows are faulty. -/
theorem pcsa_process_acSafe (p : Params) (F : Finset (Fin p.n))
    (hF : p.E.weightOf F < p.E.q) (st : State p.n) (o : Wire p.n) (h : AcStoreSafe F st)
    (hr : ∀ s N, o.decode = some (.block s N) →
      ∀ a ∈ N.rows.filterMap RowWire.toRow?, a.signer ∈ F) :
    AcStoreSafe F (process p st o) := by
  have keep (st' : State p.n) (he : st'.fg = st.fg) : AcStoreSafe F st' := by
    simpa only [AcStoreSafe_def, he] using h
  delta process
  cases hd : o.decode with
  | some msg => cases msg with
    | vote s i r =>
      dsimp only
      exact h
    | row i body =>
      dsimp only
      apply keep
      delta admitRow
      cases hdecode : RowWire.decode? ⟨o.auth, body⟩ <;> dsimp only
      split <;> rfl
    | block s N =>
      dsimp only
      rcases pcsa_admitBlock_fg_cases p st s N with he | ⟨P, hp, he⟩
      · exact keep _ he
      · have hP : P ∈ st.fg.TF := (FGSA.pickPair_some_spec _ _ hp).1
        have hb := pcsa_child_rows P N.erase N.rows F (h.2.2.2.2 P hP) (hr s N hd)
        have hk := pcsa_on_block_acSafe p F hF st h _ hb
        simpa only [AcStoreSafe_def, he] using hk
    | ack s i r =>
      dsimp only
      apply keep
      unfold admitAck
      rw [(collectPCs_frame _).2.2.2.2]
      delta poolAck
      cases hdecode : AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) <;> dsimp only
      rename_i v
      rcases v with ⟨_, _, _⟩
      dsimp only
      split_ifs <;> rfl
    | pc d =>
      dsimp only
      apply keep
      unfold admitPC
      split
      · rw [(collectPCs_frame _).2.2.2.2, pcsa_fold_poolAckRaw_fg]
      · rfl
  | none =>
    exact h

/-- An initial cached frame has a genesis root and band floor zero. -/
theorem pcsa_acSafe_frame (p : Params) (F : Finset (Fin p.n)) (st : State p.n)
    (h : AcStoreSafe F st) :
    st.fg.F = .genesis ∧ (controls p st).Z = .genesis ∧ (controls p st).lo = 0 := by
  have hn : ¬ ∃ W ∈ st.fg.TF, (FGSA.heightView p W).h = 1 ∧
      ¬ FGBlock.Preceq (.genesis : FGBlock (Fin p.n)) W := by
    rintro ⟨W, _, _, hW⟩
    exact hW (KitFG.genesis_preceq W)
  simp only [controls_def, KitFG.storeControlsView_def, h.1, h.2.1, h.2.2.1,
    h.2.2.2.1, hn, decide_false, Bool.and_false]
  dsimp only [Controls.Z, Controls.lo]
  exact ⟨trivial, by split <;> rfl, rfl⟩

end AvailableChain.PCSA
end
