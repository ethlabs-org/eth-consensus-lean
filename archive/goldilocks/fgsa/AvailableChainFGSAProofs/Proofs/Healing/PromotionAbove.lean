module
public import AvailableChainFGSAClaims.Statements.Fold
public import AvailableChainFGSA.Proofs.WindowAdmissionInvariant
public import AvailableChainFGSARun.Proofs.Reachable

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.KitFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- The exact proposal read is a reachable post-clock state. -/
theorem healing_promotion_proposal_reachable {s : Slot} {st : State p.n}
    (hs : proposalStateAt p c E rho s = some st) : Reachable p st := by
  change (postClock E rho _ _).map (·.st) = some st at hs
  rw [postClock_def, preTick_def] at hs
  cases hk : V2.D.Run.tickIdx? rho (V2.D.proposerOf rho (fgsaInterface p c) s)
      (V2.D.proposalTime (fgsaInterface p c) s) with
  | none => rw [hk] at hs; cases hs
  | some k =>
      rw [hk] at hs
      rw [← Option.some.inj hs]
      exact reachable_postClock E rho k _ _

/-- ROOT-DIGEST W2b. Blueprint 21:1385–1410; r3 A1.
DC: SAME stored R6W at the row parent rules out staleUseful at this height. -/
theorem healing_rows_above_entry_at_height (st : State p.n) (hr : Reachable p st)
    (k : RowKind) (y : Nat) (U P : FGBlock (Fin p.n)) (hP : P ∈ st.fg.TF)
    (hPh : (heightView p P).h = y) (hUP : FGBlock.Preceq U P) :
    ∀ i W, FGBlock.Preceq W P → (∃ row ∈ W.rows, RowNames p k row i y U) →
      FGBlock.Preceq U W.parent := by
  intro i W hWP ⟨row, hrow, hnames⟩
  have hinv := storeInvariant p st hr
  have hW : W ∈ st.fg.TF := ancestor_closed_of_parent_closed _ hinv.fg.closed P hP W hWP
  cases W with
  | genesis => exact (List.not_mem_nil hrow).elim
  | node Q t root x rs =>
  have hv := stored_r6wW p hr Q t root x rs hW row hrow
  have hpair : ∃ timeout, row.height_pair = .vote y U.root timeout := by
    obtain ⟨_, hk⟩ := hnames
    cases k with
    | target => exact ⟨_, hk⟩
    | progress => obtain ⟨timeout, ht⟩ := hk; exact ⟨timeout, ht⟩
  obtain ⟨timeout, hp⟩ := hpair
  have hQP : FGBlock.Preceq Q P := preceq_trans (preceq_parent_node Q t root x rs) hWP
  have hQh : (heightView p Q).h ≤ y := hPh ▸ (fgCertificateLaws p).height.h_mono hQP
  have hdh : (Window.derive p p.K_W Q).h = (heightView p Q).h := by
    rw [heightView_def, Window.projectHeight_def]
  have hdT : (Window.derive p p.K_W Q).T_h = (heightView p Q).T_h := by
    rw [heightView_def, Window.projectHeight_def]
  rw [Window.r6w_def] at hv
  rcases Bool.or_eq_true_iff.mp hv with hm | hm
  · rw [Window.heightMatch_def, hp] at hm
    simp only [NamedHeightPair.matchesEntry, decide_eq_true_eq] at hm
    have hroot : U.root = (heightView p Q).T_h.root := hdT ▸ hm.2
    have hU : U = (heightView p Q).T_h := viewRootInj_TF p st hinv _ _ ⟨P, hP, hUP⟩
      ⟨P, hP, preceq_trans ((fgCertificateLaws p).height.entry_preceq Q) hQP⟩ hroot
    change FGBlock.Preceq U Q
    rw [hU]
    exact (fgCertificateLaws p).height.entry_preceq Q
  · rw [Window.staleUseful_def, hp] at hm
    cases hf : row.finality_pair with
    | none => rw [hf] at hm; cases hm
    | some fp =>
      rw [hf] at hm
      have hb := (Bool.and_eq_true_iff.mp hm).1
      have hlt : y < (Window.derive p p.K_W Q).h := (of_decide_eq_true hb).2
      rw [hdh] at hlt
      simp only [Height] at *
      omega

end AvailableChain.FGSA.Run
end
